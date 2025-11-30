// Template for Northwestern - CompEng 361 - Lab4 
// Groupname:
// NetIDs:

//General Parameters
   `define WORD_WIDTH 32
   `define NUM_REGS 32
//Opcodes
   `define OPCODE_COMPUTE    7'b0110011 // R-Type
   `define OPCODE_COMPUTE_IMMEDIATE 7'b0010011 // I-Type (ADDI, SLTI, etc)
   `define OPCODE_BRANCH 7'b1100011 // B-Type
   `define FUNC_BEQ 3'b000
   `define FUNC_BNE 3'b001
   `define FUNC_BLT 3'b100
   `define FUNC_BGE 3'b101
   `define FUNC_BLTU 3'b110
   `define FUNC_BGEU 3'b111
   `define OPCODE_LOAD       7'b0000011 // I-Type (Load)
   `define FUNC_LB 3'b000
   `define FUNC_LH 3'b001
   `define FUNC_LW 3'b010
   `define FUNC_LBU 3'b100
   `define FUNC_LHU 3'b101
   `define OPCODE_STORE      7'b0100011 // S-Type
   `define FUNC_SB 3'b000
   `define FUNC_SH 3'b001
   `define FUNC_SW 3'b010
   `define FUNC_ADD      3'b000
   `define AUX_FUNC_ADD  7'b0000000 // R-type func7 for ADD/SLT/etc
   `define AUX_FUNC_SUB  7'b0100000 // R-type func7 for SUB/SRA
   `define AUX_FUNC_M  7'b0000001 // R-type func7 for M-extension
   `define OPCODE_LUI 7'b0110111 // U-Type
   `define OPCODE_AUIPC 7'b0010111 // U-Type
   `define OPCODE_JAL 7'b1101111 // J-Type
   `define OPCODE_JALR 7'b1100111 // I-Type (JALR)
   `define SIZE_BYTE  2'b00
   `define SIZE_HWORD 2'b01
   `define SIZE_WORD  2'b10
// ALU funct3 codes for comparison (for branch logic)
   `define FUNC_SLT 3'b010
   `define FUNC_SLTU 3'b011

module PipelinedCPU(halt, clk, rst);
   output halt;
   input clk, rst;
    
    // global memory interface
    wire [31:0] DataAddr, StoreData, DataWord;
    wire [1:0]  MemSize;
    wire        MemWrEn;

    // global register file interface (used in ID/WB)
    wire [4:0]  rd_WB;          // dest reg from WB
    wire [31:0] Rdata1, Rdata2; // read ports
    wire [31:0] RWrdata_WB;     // data written back
    wire        RWrEn_WB;       // write enable in WB

   //a bunch of wire declarations that i forgot to add- chat helped
    wire [31:0] InstWord;

    // ---- IF / ID control ----
    wire        PC_WE;              // PC write enable
    wire        valid_op_ID;        // ID-stage valid-op flag
    wire        memory_alignment_error_MEM; // MEM-stage alignment error

    // ---- EX-stage control and data ----
    wire        RegWrite_EX;
    wire        MemWrite_EX;
    wire        MemRead_EX;
    wire        MemToReg_EX;
    wire        IsBranch_EX;
    wire        IsJal_EX;
    wire        IsJalr_EX;
    wire [1:0]  Size_EX;
    wire [2:0]  BranchFunct3_EX;

    wire [31:0] EX_opA;
    wire [31:0] EX_opB_raw;
    wire [6:0]  EX_eu_funct7_in;
    wire [2:0]  EX_eu_funct3_in;

    wire [31:0] EX_branch_target;
    wire [31:0] EX_jal_target;
    wire [31:0] EX_jalr_target;
    wire        EX_branch_taken;
    wire [31:0] EX_PC_target;

    // ---- Long-latency MUL/DIV counter ----
    wire [4:0]  EX_busy;
    wire [4:0]  EX_busy_next;


   /* Pipelining!!!! here comes the real work*/
   // ---------- IF stage ----------
   //Logic
   wire [31:0] PC, PC_next, PC_Plus_4;
   assign PC_Plus_4 = PC + 4;
   Reg PC_REG(.Din(PC_next), .Qout(PC), .WE(PC_WE), .CLK(clk), .RST(rst));
   Mem   MEM(.InstAddr(PC), .InstOut(InstWord), 
            .DataAddr(DataAddr), .DataSize(MemSize), .DataIn(StoreData), .DataOut(DataWord), .WE(MemWrEn), .CLK(clk));
   
   //Pipeline Reg
   wire [31:0] IFID_PC, IFID_IR;
   wire        IFID_WE;
   wire        IFID_flush;      
   wire [31:0] IFID_IR_in = IFID_flush ? 32'h00000013 : InstWord; // ADDI x0,x0,0 = NOP

   Reg #(.width(32)) IFID_PC_REG (.Din(PC),        .Qout(IFID_PC), .WE(IFID_WE), .CLK(clk), .RST(rst));
   Reg #(.width(32)) IFID_IR_REG (.Din(IFID_IR_in),.Qout(IFID_IR), .WE(IFID_WE), .CLK(clk), .RST(rst));

   //Branching/Jumping Logic for next PC
   wire EX_do_redirect = IsJal_EX | IsJalr_EX | EX_branch_taken;   //either from EX output's PC_target (branch/jump) or increment PC normally
   assign PC_next = EX_do_redirect ? EX_PC_target : PC_Plus_4;  
   assign IFID_flush = load_use_hazard | EX_do_redirect; //flush pipeline if we branched/jumped
   assign PC_WE      = ~load_use_hazard & ~long_latency_stall_IF;        // Only stalls on load-use or long latency instuction
   assign IFID_WE    = ~load_use_hazard & ~long_latency_stall_IF;        // Only stalls on load-use or long latency instruction
   /*
   During a load-use hazard...
   IF/ID   stalls  , instruction “add” stays in decode
   ID/EX   gets flushed , becomes NOP
   EX      receives NOP , harmless
   MEM     continues the load
   WB      completes load
   */


   // ---------- ID stage ----------
   //Decode Logic
   wire [31:0] ID_PC   = IFID_PC;
   wire [31:0] ID_IR   = IFID_IR;

   wire [6:0] opcode = ID_IR[6:0];
   wire [4:0] Rdst   = ID_IR[11:7];
   wire [4:0] Rsrc1  = ID_IR[19:15];
   wire [4:0] Rsrc2  = ID_IR[24:20];
   wire [2:0] funct3 = ID_IR[14:12];
   wire [6:0] funct7 = ID_IR[31:25];
   wire [4:0] Shamt = ID_IR[24:20]; //shift amount
   wire [1:0] SR_control = ID_IR[31:30]; //top two bits indicate shift control (left/00 vs right/01)

   // Immediate Value Generation
   // I-Type Immediate (Load, ADDI, JALR)
   wire [11:0] imm_i_raw = ID_IR[31:20];
   wire [31:0] imm_i_type_sext = {{20{imm_i_raw[11]}}, imm_i_raw}; // sign-extended 32-bit
   // S-Type Immediate (Store)
   wire [11:0] imm_s_raw = {ID_IR[31:25], ID_IR[11:7]};
   wire [31:0] imm_s_type_sext = {{20{imm_s_raw[11]}}, imm_s_raw};
   // B-Type Immediate (Branch) (FIXED: 33-bit issue corrected)
   wire [31:0] imm_b_type = {
                            {19{ID_IR[31]}},  // Sign extension to fill 19 MSBs
                            ID_IR[31],        // Imm[12]
                            ID_IR[7],         // Imm[11]
                            ID_IR[30:25],     // Imm[10:5]
                            ID_IR[11:8],      // Imm[4:1]
                            1'b0                // Imm[0]
                            };
   // U-Type Immediate (LUI, AUIPC)
   wire [31:0] imm_u_type_shifted = {ID_IR[31:12], 12'b0};
   // J-Type Immediate (JAL)
   wire [31:0] imm_j_type_offset = {
                                   {12{ID_IR[31]}},  // Sign extension to fill 12 MSBs
                                    ID_IR[19:12],    // Imm[19:12]
                                    ID_IR[20],       // Imm[11]
                                    ID_IR[30:21],    // Imm[10:1]
                                    1'b0                // Imm[0]
                                   };
   RegFile RF(
    .AddrA(Rsrc1), .DataOutA(Rdata1),
    .AddrB(Rsrc2), .DataOutB(Rdata2),
    .AddrW(rd_WB), .DataInW(RWrdata_WB),
    .WenW(RWrEn_WB), .CLK(clk)
   );

   //Control Signals
   wire RegWrite_ID, MemWrite_ID, MemRead_ID, MemToReg_ID;
   wire IsBranch_ID, IsJal_ID, IsJalr_ID;
   wire [1:0] Size_ID;
   wire [2:0] BranchFunct3_ID; // for BLT/BGE/other branch functions
   assign RegWrite_ID = (opcode == `OPCODE_LUI) |
                        (opcode == `OPCODE_AUIPC) |
                        (opcode == `OPCODE_JAL) |
                        (opcode == `OPCODE_JALR) |
                        (opcode == `OPCODE_LOAD) |
                        (opcode == `OPCODE_COMPUTE_IMMEDIATE) |
                        (opcode == `OPCODE_COMPUTE);
   assign MemWrite_ID = (opcode == `OPCODE_STORE);
   assign MemRead_ID  = (opcode == `OPCODE_LOAD);
   assign MemToReg_ID = (opcode == `OPCODE_LOAD);  // WB chooses DataWord vs ALU result
   assign IsBranch_ID = (opcode == `OPCODE_BRANCH);
   assign IsJal_ID    = (opcode == `OPCODE_JAL);
   assign IsJalr_ID   = (opcode == `OPCODE_JALR);
   assign Size_ID     = (opcode == `OPCODE_LOAD | opcode == `OPCODE_STORE) ? ID_IR[13:12] : 2'b00;
   assign BranchFunct3_ID = funct3;
   //Pack control signals into one large signal/register since they consist of many smaller sized chunks
   //This goes into EX stage
      localparam IDEX_CTRL_W = 1+1+1+1+1+1+2+3; // RegWrite,MemWrite,MemRead,MemToReg,IsBranch,IsJal/Jalr,Size,BranchFunct3
      wire [IDEX_CTRL_W-1:0] IDEX_ctrl_in, IDEX_ctrl_out;
      assign IDEX_ctrl_in = {RegWrite_ID, MemWrite_ID, MemRead_ID, MemToReg_ID,
                           IsBranch_ID, IsJal_ID, IsJalr_ID,
                           Size_ID, BranchFunct3_ID};
   


   //Pipeline Reg, ID/EX
   wire [31:0] IDEX_PC, IDEX_R1, IDEX_R2, IDEX_imm_i, IDEX_imm_s, IDEX_imm_b, IDEX_imm_u, IDEX_imm_j;
   wire [4:0]  IDEX_rs1, IDEX_rs2, IDEX_rd;
   wire [2:0]  IDEX_funct3;
   wire [6:0]  IDEX_funct7;
   wire [6:0]  IDEX_opcode;
   wire [4:0]  IDEX_Shamt;
   wire [1:0]  IDEX_SR_control;
   wire        IDEX_WE = ~long_latency_stall_ID;
   wire        IDEX_flush; // from hazard unit

   Reg #(32) IDEX_PC_REG     (.Din(ID_PC),           .Qout(IDEX_PC),       .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(32) IDEX_R1_REG     (.Din(Rdata1),          .Qout(IDEX_R1),       .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(32) IDEX_R2_REG     (.Din(Rdata2),          .Qout(IDEX_R2),       .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(32) IDEX_IMM_I_REG  (.Din(imm_i_type_sext), .Qout(IDEX_imm_i),    .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(32) IDEX_IMM_S_REG  (.Din(imm_s_type_sext), .Qout(IDEX_imm_s),    .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(32) IDEX_IMM_B_REG  (.Din(imm_b_type),      .Qout(IDEX_imm_b),    .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(32) IDEX_IMM_U_REG  (.Din(imm_u_type_shifted), .Qout(IDEX_imm_u), .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(32) IDEX_IMM_J_REG  (.Din(imm_j_type_offset), .Qout(IDEX_imm_j),  .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(5)  IDEX_RS1_REG    (.Din(Rsrc1),           .Qout(IDEX_rs1),      .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(5)  IDEX_RS2_REG    (.Din(Rsrc2),           .Qout(IDEX_rs2),      .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(5)  IDEX_RD_REG     (.Din(Rdst),            .Qout(IDEX_rd),       .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(3)  IDEX_f3_REG     (.Din(funct3),          .Qout(IDEX_funct3),   .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(7)  IDEX_f7_REG     (.Din(funct7),          .Qout(IDEX_funct7),   .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(7)  IDEX_OPCODE_REG (.Din(opcode),       .Qout(IDEX_opcode),   .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(5)  IDEX_Shamt_REG  (.Din(Shamt),           .Qout(IDEX_Shamt),    .WE(IDEX_WE), .CLK(clk), .RST(rst));
   Reg #(2)  IDEX_SRC_REG    (.Din(SR_control),      .Qout(IDEX_SR_control), .WE(IDEX_WE), .CLK(clk), .RST(rst));

   // control bus with bubble on flush
   assign IDEX_flush = load_use_hazard | EX_do_redirect;
   wire [IDEX_CTRL_W-1:0] IDEX_ctrl_Din = IDEX_flush ? {IDEX_CTRL_W{1'b0}} : IDEX_ctrl_in;
   Reg #(IDEX_CTRL_W) IDEX_CTRL_REG (.Din(IDEX_ctrl_Din), .Qout(IDEX_ctrl_out), .WE(IDEX_WE), .CLK(clk), .RST(rst));
      
   // Unpack control for EX
    assign {
        RegWrite_EX, MemWrite_EX, MemRead_EX, MemToReg_EX,
        IsBranch_EX, IsJal_EX, IsJalr_EX,
        Size_EX, BranchFunct3_EX
    } = IDEX_ctrl_out;

   //Halt logic
   assign valid_op_ID = (opcode == `OPCODE_LUI) | (opcode == `OPCODE_AUIPC)|
                     (opcode == `OPCODE_JAL) | (opcode == `OPCODE_JALR) |
                     (opcode == `OPCODE_BRANCH) | (opcode == `OPCODE_LOAD) |
                     (opcode == `OPCODE_STORE) | (opcode == `OPCODE_COMPUTE_IMMEDIATE) |
                     (opcode == `OPCODE_COMPUTE);
   assign halt = (~valid_op_ID) | memory_alignment_error_MEM;

   //Load-use hazard
   wire load_use_hazard = MemRead_EX && (IDEX_rd != 5'd0) && ((IDEX_rd == Rsrc1) || (IDEX_rd == Rsrc2));



   // ---------- EX stage ----------

   /*ALU*/
   //Operands
      //Forwarding operands
      // Forward to rs1 (operand A)
      wire [31:0] EX_R1_fwd =
         (RegWrite_MEM && (EXMEM_rd != 5'd0) && (EXMEM_rd == IDEX_rs1)) ? EXMEM_ALU_out :
         (RegWrite_WB  && (MEMWB_rd  != 5'd0) && (MEMWB_rd  == IDEX_rs1)) ? RWrdata_WB   :
                                                                           IDEX_R1;

      // Forward to rs2 (operand B / store data)
      wire [31:0] EX_R2_fwd =
         (RegWrite_MEM && (EXMEM_rd != 5'd0) && (EXMEM_rd == IDEX_rs2)) ? EXMEM_ALU_out :
         (RegWrite_WB  && (MEMWB_rd  != 5'd0) && (MEMWB_rd  == IDEX_rs2)) ? RWrdata_WB   :
                                                                           IDEX_R2;
   //Operand A
   assign EX_opA = EX_R1_fwd;
   // Operand B mux
   wire EX_useImmI = (IDEX_opcode == `OPCODE_COMPUTE_IMMEDIATE) ||
                     (IDEX_opcode == `OPCODE_LOAD) ||
                     (IDEX_opcode == `OPCODE_JALR);
   wire EX_useImmS = (IDEX_opcode == `OPCODE_STORE);
   assign EX_opB_raw =
         EX_useImmI ? IDEX_imm_i : //I-Type/Load/JALR: imm_i, 
         EX_useImmS ? IDEX_imm_s : //Store: imm_s
                     EX_R2_fwd; //R-Type: R2
         
   // ALU Funct7 Mux (eu_funct7_in)
   assign EX_eu_funct7_in = (IDEX_opcode == `OPCODE_BRANCH && (IDEX_funct3 == `FUNC_BEQ | IDEX_funct3 == `FUNC_BNE)) ? `AUX_FUNC_SUB : 
                         (IDEX_opcode == `OPCODE_BRANCH && (IDEX_funct3 == `FUNC_BLT | IDEX_funct3 == `FUNC_BGE | IDEX_funct3 == `FUNC_BLTU | IDEX_funct3 == `FUNC_BGEU)) ? `AUX_FUNC_ADD : // All comparisons use R-Type ADD/SLT auxfunc
                         (IDEX_opcode == `OPCODE_COMPUTE_IMMEDIATE) ? 7'b0110000: IDEX_funct7; // I-Type uses FUNC_3 (7'b0110000)
                            
   // ALU Funct3 Mux (eu_funct3_in)
   assign EX_eu_funct3_in = (IDEX_opcode == `OPCODE_BRANCH && (IDEX_funct3 == `FUNC_BEQ | IDEX_funct3 == `FUNC_BNE)) ? `FUNC_ADD : // BEQ/BNE: Use ADD func3 (to trigger SUB when auxFunc=FUNC_1)
                         (IDEX_opcode == `OPCODE_BRANCH && (IDEX_funct3 == `FUNC_BLT | IDEX_funct3 == `FUNC_BGE)) ? `FUNC_SLT : // BLT/BGE: Use SLT func3
                         (IDEX_opcode == `OPCODE_BRANCH && (IDEX_funct3 == `FUNC_BLTU | IDEX_funct3 == `FUNC_BGEU)) ? `FUNC_SLTU : // BLTU/BGEU: Use SLTU func3
                        IDEX_funct3; // Default to instruction's funct3 for Load/Store/R-Type/I-Type
   
   wire [31:0] EX_eu_out;
    // Execution unit
    ExecutionUnit EU (
        .out(EX_eu_out),
        .opA(EX_opA),
        .opB(EX_opB_raw),
        .func(EX_eu_funct3_in),
        .auxFunc(EX_eu_funct7_in), 
        .opBS(IDEX_Shamt),
        .sr_C(IDEX_SR_control)
    );


   /*Branch + Jump*/
   assign EX_branch_target = IDEX_PC + IDEX_imm_b;
   assign EX_jal_target    = IDEX_PC + IDEX_imm_j;
   assign EX_jalr_target   = (EX_opA + IDEX_imm_i) & 32'hFFFFFFFE; //'and' forces last bit to be 0, alignment
   //Branch taken logic
   assign EX_branch_taken = IsBranch_EX && (
        (BranchFunct3_EX == `FUNC_BEQ  && EX_eu_out == 32'b0) || // BEQ: eu_out == 0
        (BranchFunct3_EX == `FUNC_BNE  && EX_eu_out != 32'b0) || // BNE: eu_out != 0
        ((BranchFunct3_EX == `FUNC_BLT  || BranchFunct3_EX == `FUNC_BLTU) &&  EX_eu_out == 32'd1) || // BLT/BLTU: eu_out == 1 (SLT/SLTU result)
        ((BranchFunct3_EX == `FUNC_BGE  || BranchFunct3_EX == `FUNC_BGEU) && EX_eu_out == 32'd0)  // BGE/BGEU: eu_out == 0 (not less)
    );
   // EX next PC calculation upon branching
   assign EX_PC_target =
      IsJal_EX       ? EX_jal_target  :
      IsJalr_EX      ? EX_jalr_target :
      EX_branch_taken ? EX_branch_target :
      32'b0;          // unused when no control transfer


   /*Special Treatment for instructions that don't use EX's output (lui, auipc, jal, jalr*/
   wire [31:0] EX_PC_plus4 = IDEX_PC + 32'd4;  // PC + 4 for this instruction (based on IDEX_PC)
   wire [31:0] EX_result =
      (IDEX_opcode == `OPCODE_LUI)   ? IDEX_imm_u                  : // LUI
      (IDEX_opcode == `OPCODE_AUIPC) ? (IDEX_PC + IDEX_imm_u)      : // AUIPC
      (IDEX_opcode == `OPCODE_JAL)   ? EX_PC_plus4                 : // JAL: link = PC+4
      (IDEX_opcode == `OPCODE_JALR)  ? EX_PC_plus4                 : // JALR: link = PC+4
                                       EX_eu_out;                    // everything else
      
      
   
   //Pipeline Reg, EX/MEM
      
      // Control bus EX → MEM = {RegWrite, MemWrite, MemRead, MemToReg, IsJal, IsJalr, Size[1:0], LoadFunct3[2:0]}
      localparam EXMEM_CTRL_W = 1+1+1+1+1+1+2+3;
      wire [EXMEM_CTRL_W-1:0] EXMEM_ctrl_in, EXMEM_ctrl_out;

   assign EXMEM_ctrl_in = {
      RegWrite_EX,    // [EXMEM_CTRL_W-1]
      MemWrite_EX,
      MemRead_EX,
      MemToReg_EX,
      IsJal_EX,
      IsJalr_EX,
      Size_EX,        // 2 bits
      IDEX_funct3     // use funct3 for load type in WB
   };

   wire [31:0] EXMEM_ALU_out;       // address for load/store OR ALU result
   wire [31:0] EXMEM_store_data;    // value to be written on store
   wire [31:0] EXMEM_addr;          // same as ALU_out, but kept separately for clarity
   wire [4:0]  EXMEM_rd;
   wire [2:0]  EXMEM_funct3;
   wire [1:0]  EXMEM_Size;
   wire        RegWrite_MEM, MemWrite_MEM, MemRead_MEM, MemToReg_MEM;
   wire        IsJal_MEM, IsJalr_MEM;
   wire EXMEM_WE = ~stall_EX;

   // Pipeline registers:
   Reg #(32) EXMEM_ALU_REG   (.Din(EX_result), .Qout(EXMEM_ALU_out),    .WE(EXMEM_WE), .CLK(clk), .RST(rst));
   Reg #(32) EXMEM_STORE_REG (.Din(EX_R2_fwd),   .Qout(EXMEM_store_data), .WE(EXMEM_WE), .CLK(clk), .RST(rst)); 
   Reg #(32) EXMEM_ADDR_REG  (.Din(EX_eu_out), .Qout(EXMEM_addr),       .WE(EXMEM_WE), .CLK(clk), .RST(rst)); // same value, explicit "addr"
   Reg #(5)  EXMEM_RD_REG    (.Din(IDEX_rd),   .Qout(EXMEM_rd),         .WE(EXMEM_WE), .CLK(clk), .RST(rst));
   Reg #(EXMEM_CTRL_W) EXMEM_CTRL_REG (
      .Din(EXMEM_ctrl_in),
      .Qout(EXMEM_ctrl_out),
      .WE(EXMEM_WE),
      .CLK(clk),
      .RST(rst)
   );

   // Unpack EX/MEM control bits
   assign {
      RegWrite_MEM,      // [EXMEM_CTRL_W-1]
      MemWrite_MEM,
      MemRead_MEM,
      MemToReg_MEM,
      IsJal_MEM,
      IsJalr_MEM,
      EXMEM_Size,        // 2 bits
      EXMEM_funct3       // 3 bits: load funct3 when opcode was LOAD
   } = EXMEM_ctrl_out;


   //Long Latency Mul/Div/Rem Instructions
   Reg #(5) EX_busy_REG (.Din(EX_busy_next), .Qout(EX_busy), .WE(1'b1), .CLK(clk), .RST(rst)); //counter register
   wire isMUL_EX  = (IDEX_opcode == `OPCODE_COMPUTE) &&
                 (IDEX_funct7 == `AUX_FUNC_M) &&
                 (IDEX_funct3 <= 3'b011);   // mul/mulhu/other muls

   wire isDIV_EX  = (IDEX_opcode == `OPCODE_COMPUTE) &&
                 (IDEX_funct7 == `AUX_FUNC_M) &&
                 (IDEX_funct3 >= 3'b100);   // div/divu/rem/remu
   
   wire [4:0] EX_latency = isMUL_EX ? 5'd4 : 
                           isDIV_EX ? 5'd20 : 5'd1;

   wire EX_busy_zero = (EX_busy == 5'd0);

   // Decrement if currently busy
   wire [4:0] EX_busy_dec = EX_busy - 5'd1;

   // Start new latency only if EX is free and a mult/div enters EX
   wire start_new_latency = EX_busy_zero && (EX_latency > 5'd1);

   // Priority: loading new counter > decrementing
   assign EX_busy_next =
      start_new_latency ? (EX_latency - 5'd1) :   // load counter (minus 1 because we count remaining cycles)
      (!EX_busy_zero ? EX_busy_dec : 5'd0);       // decrement if busy

   //Stall while we are executing long latency instructions
   wire stall_EX = (EX_busy != 5'd0);   // multi-cycle stall
   wire long_latency_stall_ID = stall_EX;
   wire long_latency_stall_IF = stall_EX;





   // ---------- MEM stage ----------
   // Connect to data memory side of MEM module
   assign DataAddr = EXMEM_addr;
   assign StoreData = EXMEM_store_data;
   assign MemWrEn   = MemWrite_MEM;
   assign MemSize   = EXMEM_Size;

   // alignment error (based on DataAddr and size)
   assign memory_alignment_error_MEM =
      ((MemRead_MEM | MemWrite_MEM) &&
         ((EXMEM_Size == `SIZE_HWORD && DataAddr[0]   != 1'b0) || // halfword must be 2-byte aligned
         (EXMEM_Size == `SIZE_WORD  && DataAddr[1:0] != 2'b00)) // word must be 4-byte aligned
      );

   //Control bus MEM -> WB = {RegWrite, MemToReg, IsJal, IsJalr, LoadFunct3[2:0]}
   localparam MEMWB_CTRL_W = 1+1+1+1+3;
   wire [MEMWB_CTRL_W-1:0] MEMWB_ctrl_in, MEMWB_ctrl_out;
   assign MEMWB_ctrl_in = {
      RegWrite_MEM,
      MemToReg_MEM,
      IsJal_MEM,
      IsJalr_MEM,
      EXMEM_funct3      // for loads
   };

   //MEM/WB Pipeline Regs
   wire [31:0] MEMWB_ALU_out;
   wire [31:0] MEMWB_DataWord;
   wire [31:0] MEMWB_addr;
   wire [4:0]  MEMWB_rd;
   wire [2:0]  MEMWB_funct3;
   wire        RegWrite_WB, MemToReg_WB, IsJal_WB, IsJalr_WB;

   // Data regs
   Reg #(32) MEMWB_ALU_REG  (.Din(EXMEM_ALU_out), .Qout(MEMWB_ALU_out),   .WE(1'b1), .CLK(clk), .RST(rst));
   Reg #(32) MEMWB_MEM_REG  (.Din(DataWord),      .Qout(MEMWB_DataWord),  .WE(1'b1), .CLK(clk), .RST(rst));
   Reg #(32) MEMWB_ADDR_REG (.Din(EXMEM_addr),    .Qout(MEMWB_addr),      .WE(1'b1), .CLK(clk), .RST(rst));
   Reg #(5)  MEMWB_RD_REG   (.Din(EXMEM_rd),      .Qout(MEMWB_rd),        .WE(1'b1), .CLK(clk), .RST(rst));
   // Control reg
   Reg #(MEMWB_CTRL_W) MEMWB_CTRL_REG (
      .Din(MEMWB_ctrl_in),
      .Qout(MEMWB_ctrl_out),
      .WE(1'b1),
      .CLK(clk),
      .RST(rst)
   );

   // Unpack MEM/WB control
   assign {
      RegWrite_WB,
      MemToReg_WB,
      IsJal_WB,
      IsJalr_WB,
      MEMWB_funct3
   } = MEMWB_ctrl_out;




 // ---------- WB stage ----------
 /* Load Data Extraction Logic
   MEMWB_DataWord is the 32-bit word read at the aligned address
   MEMWB_addr[1:0] selects the correct byte / halfword for unaligned loads */

// Byte selector (little-endian)
wire [7:0] wb_byte =
    (MEMWB_addr[1:0] == 2'b00) ? MEMWB_DataWord[7:0]   :
    (MEMWB_addr[1:0] == 2'b01) ? MEMWB_DataWord[15:8]  :
    (MEMWB_addr[1:0] == 2'b10) ? MEMWB_DataWord[23:16] :
                                  MEMWB_DataWord[31:24];
// Halfword selector (little-endian)
wire [15:0] wb_hword =
    (MEMWB_addr[1] == 1'b0) ? MEMWB_DataWord[15:0] :
                               MEMWB_DataWord[31:16];

// Apply sign/zero extension based on load funct3
wire [31:0] wb_load_data =
    (MEMWB_funct3 == `FUNC_LB)  ? {{24{wb_byte[7]}},   wb_byte}   : // lb  (signed)
    (MEMWB_funct3 == `FUNC_LH)  ? {{16{wb_hword[15]}}, wb_hword}  : // lh  (signed)
    (MEMWB_funct3 == `FUNC_LW)  ? MEMWB_DataWord                      : // lw
    (MEMWB_funct3 == `FUNC_LBU) ? {24'b0,              wb_byte}    : // lbu
    (MEMWB_funct3 == `FUNC_LHU) ? {16'b0,              wb_hword}   : // lhu
                                  MEMWB_DataWord;                     // default (or bad funct3)

// Final writeback value
// - If MemToReg_WB == 1 → load data
// - Else                → ALU result
wire [31:0] RWrdata_next = MemToReg_WB ? wb_load_data : MEMWB_ALU_out;

// These go back into the RegFile in ID
assign RWrdata_WB = RWrdata_next;
assign rd_WB      = MEMWB_rd;
assign RWrEn_WB = RegWrite_WB;




endmodule // PipelinedCPU


module ExecutionUnit(out, opA, opB, func, auxFunc, opBS, sr_C);
   output [`WORD_WIDTH-1:0] out;
   input [`WORD_WIDTH-1:0]  opA, opB;
   input [2:0] 	 func;
   input [6:0] 	 auxFunc;
   input [4:0] 	 opBS;
   input [1:0] 	 sr_C;  

   
   //Copied over from Zach's Lab 2
   //define operation codes
    localparam OP_ADD = 3'b000, //localparam only exists inside the module
               OP_SUB = 3'b000,
               OP_SLL = 3'b001,
               OP_SLT  = 3'b010,
               OP_SLTU = 3'b011,
               OP_XOR = 3'b100,
               OP_SRL = 3'b101,
               OP_SRA= 3'b101,
               OP_OR = 3'b110,
               OP_AND = 3'b111,
               OP_MUL = 3'b000,
               OP_MULH = 3'b001,
               OP_MULHSU = 3'b010,
               OP_MULHU= 3'b011,
               OP_DIV = 3'b100,
               OP_DIVU = 3'b101,
               OP_REM = 3'b110,
               OP_REMU = 3'b111;

    localparam FUNC_0 = 7'b0000000, // AUX_FUNC_ADD
               FUNC_1 = 7'b0100000, // AUX_FUNC_SUB
               FUNC_2 = 7'b0000001, // AUX_FUNC_M
               FUNC_3 = 7'b0110000; // I-Type auxFunc

  //Dataflow model
    assign out =
      // I-Type Arithmetic (ADDI, SLTI, etc) - OpB is immediate
      (auxFunc == FUNC_3) ? (
        (func == OP_ADD) ? (opA + opB) :
        (func == OP_SLT) ? (($signed(opA) < $signed(opB)) ? 32'd1 : 32'd0) :
        (func == OP_SLTU) ? ((opA < opB) ? 32'd1 : 32'd0) :
        (func == OP_XOR) ? (opA ^ opB) :
        (func == OP_OR) ? (opA | opB) :
        (func == OP_AND) ? (opA & opB) :
        (func == OP_SLL) ? (opA << opBS) : // SLLI
        (func == OP_SRL && sr_C == 2'd0) ? (opA >> opBS) : // SRLI
        (func == OP_SRA && sr_C == 2'd1) ? ($signed(opA) >>> opBS) : // SRAI (using system task for clarity)
        32'b0
      ) :
      
      // R-Type Arithmetic (auxFunc == FUNC_0) - OpB is register
      (auxFunc == FUNC_0) ? (
        (func == OP_ADD) ? (opA + opB) :
        (func == OP_SLL) ? (opA << opB[4:0]) :
        (func == OP_SLT) ? (($signed(opA) < $signed(opB)) ? 32'd1 : 32'd0) :
        (func == OP_SLTU) ? ((opA < opB) ? 32'd1 : 32'd0) :
        (func == OP_XOR) ? (opA ^ opB) :
        (func == OP_SRL) ? (opA >> opB[4:0]) :
        (func == OP_OR) ? (opA | opB) :
        (func == OP_AND) ? (opA & opB) :
        32'b0
      ) :
      
      // R-Type Subtraction/SRA (auxFunc == FUNC_1) - OpB is register
      (auxFunc == FUNC_1) ? (
        (func == OP_SUB) ? (opA - opB) :
        (func == OP_SRA) ? ($signed(opA) >>> opB[4:0]) : // SRA
        32'b0
      ) :

      // M-Extension Instructions (auxFunc == FUNC_2) (FIXED: DIV by zero checks)
      (auxFunc == FUNC_2) ? (
        (func == OP_MUL) ? (mul_uu[31:0]) : 
        (func == OP_MULH) ? (mul_ss[63:32]) : 
        (func == OP_MULHSU) ? (mul_su[63:32]) : 
        (func == OP_MULHU) ? (mul_uu[63:32]) : 
        (func == OP_DIV) ? div_q_signed : 
        (func == OP_DIVU) ? div_q_unsigned :
        (func == OP_REM) ? rem_r_signed :
        (func == OP_REMU) ? rem_r_unsigned : 32'b0
      ) :
      32'b0; // Default output (shouldn't happen with correct control)

   // M-instruction processsing ->
   wire signed   [31:0] sA = opA;
   wire signed   [31:0] sB = opB;
   wire         [31:0] uA = opA;
   wire         [31:0] uB = opB; 
   wire signed  [63:0] sextsA = { {32{sA[31]}}, sA };
   wire signed  [63:0] zext_uB = {32'b0, sB};
   wire signed  [63:0] mul_ss  = sA * sB;
   wire signed  [63:0] mul_su = $signed(sextsA) * $signed(zext_uB);
   wire         [63:0] mul_uu  = uA * uB;

   wire div_by_zero = (opB == 32'b0);
   
   // DIV Logic 
   wire signed [31:0] div_q_signed = div_by_zero ? 32'hFFFFFFFF :  
                                     (sA == 32'sh80000000 && sB == 32'hFFFFFFFF) ? 32'sh80000000 : 
                                     sA / sB; 
   // DIVU Logic
   wire [31:0] div_q_unsigned = div_by_zero ? 32'hFFFFFFFF : uA / uB;
   
   // REM Logic
   wire signed [31:0] rem_r_signed = div_by_zero ? sA : 
                                    (sA == 32'sh80000000 && sB == 32'hFFFFFFFF) ? 32'sd0 : sA % sB;
   // REMU Logic
   wire [31:0] rem_r_unsigned = div_by_zero ? uA : uA % uB;


endmodule // ExecutionUnit