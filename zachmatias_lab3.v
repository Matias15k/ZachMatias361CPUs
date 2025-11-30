// Template for Northwestern - CompEng 361 - Lab3 -- Version 1.1
// Groupname: Zach Tey, Matias Ketema
// NetIDs: vcs5888, tnc5178

//General Parameters
   `define WORD_WIDTH 32
   `define NUM_REGS 32
//Opcodes
   `define OPCODE_COMPUTE    7'b0110011 // R-Type
   `define OPCODE_COMPUTE_IMMEDIATE 7'b0010011 // I-Type (ADDI, SLTI, etc)
   `define OPCODE_BRANCH     7'b1100011 // B-Type
   `define FUNC_BEQ 3'b000
   `define FUNC_BNE 3'b001
   `define FUNC_BLT 3'b100
   `define FUNC_BGE 3'b101
   `define FUNC_BLTU 3'b110
   `define FUNC_BGEU 3'b111
   `define OPCODE_LOAD       7'b0000011 // I-Type (Load)
   `define FUNC_LB 3'b000
   `define FUNC_LH 3'b001
   `define FUNC_LW 3'b010
   `define FUNC_LBU 3'b100
   `define FUNC_LHU 3'b101
   `define OPCODE_STORE      7'b0100011 // S-Type
   `define FUNC_SB 3'b000
   `define FUNC_SH 3'b001
   `define FUNC_SW 3'b010
   `define FUNC_ADD      3'b000
   `define AUX_FUNC_ADD  7'b0000000 // R-type func7 for ADD/SLT/etc
   `define AUX_FUNC_SUB  7'b0100000 // R-type func7 for SUB/SRA
   `define AUX_FUNC_M  7'b0000001 // R-type func7 for M-extension
   `define OPCODE_LUI 7'b0110111 // U-Type
   `define OPCODE_AUIPC 7'b0010111 // U-Type
   `define OPCODE_JAL 7'b1101111 // J-Type
   `define OPCODE_JALR 7'b1100111 // I-Type (JALR)
   `define SIZE_BYTE  2'b00
   `define SIZE_HWORD 2'b01
   `define SIZE_WORD  2'b10

// ALU func3 codes for comparison (needed for branch logic)
   `define FUNC_SLT 3'b010
   `define FUNC_SLTU 3'b011

module SingleCycleCPU(halt, clk, rst);
   output halt;
   input clk, rst;

   wire [`WORD_WIDTH-1:0] PC, InstWord;
   wire [`WORD_WIDTH-1:0] DataAddr, StoreData, DataWord;
   wire [1:0]  MemSize;
   wire        MemWrEn;
   
   wire [4:0]  Rsrc1, Rsrc2, Rdst;
   wire [`WORD_WIDTH-1:0] Rdata1, Rdata2, RWrdata;
   wire        RWrEn;
   
   // Instruction Decode Wires, extract from InstWord
   wire [6:0]  opcode = InstWord[6:0];   
   wire [4:0]  Rdst = InstWord[11:7]; 
   wire [4:0]  Rsrc1 = InstWord[19:15]; 
   wire [4:0]  Rsrc2 = InstWord[24:20];
   wire [2:0]  funct3 = InstWord[14:12]; 
   wire [6:0]  funct7 = InstWord[31:25];  
   wire [4:0] Shamt = InstWord[24:20]; //shift amount
   wire [1:0] SR_control = InstWord[31:30]; //top two bits indicate shift control (left/00 vs right/01)

   // Immediate Value Generation
   // I-Type Immediate (Load, ADDI, JALR)
   wire [11:0] imm_i_raw = InstWord[31:20];
   wire [31:0] imm_i_type_sext = {{20{imm_i_raw[11]}}, imm_i_raw}; // sign-extended 32-bit
   // S-Type Immediate (Store)
   wire [11:0] imm_s_raw = {InstWord[31:25], InstWord[11:7]};
   wire [31:0] imm_s_type_sext = {{20{imm_s_raw[11]}}, imm_s_raw};
   // B-Type Immediate (Branch) (FIXED: 33-bit issue corrected)
   wire [31:0] imm_b_type = {
                            {19{InstWord[31]}},  // Sign extension to fill 19 MSBs
                            InstWord[31],        // Imm[12]
                            InstWord[7],         // Imm[11]
                            InstWord[30:25],     // Imm[10:5]
                            InstWord[11:8],      // Imm[4:1]
                            1'b0                // Imm[0]
                            };
   // U-Type Immediate (LUI, AUIPC)
   wire [31:0] imm_u_type_shifted = {InstWord[31:12], 12'b0};
   // J-Type Immediate (JAL) (FIXED: Corrected bit concatenation)
   wire [31:0] imm_j_type_offset = {
                                   {12{InstWord[31]}},  // Sign extension to fill 12 MSBs
                                    InstWord[19:12],    // Imm[19:12]
                                    InstWord[20],       // Imm[11]
                                    InstWord[30:21],    // Imm[10:1]
                                    1'b0                // Imm[0]
                                   };

   wire [`WORD_WIDTH-1:0] NPC, PC_Plus_4;
   wire [31:0] eu_out;
   wire [6:0] eu_funct7_in;
   wire [2:0] eu_funct3_in;
   wire [31:0] Rdata2_in; // ALU Operand B Mux
   wire [31:0] StoreData_in; // Data to be stored (from Rdata2)

   // ALU Operand B Mux (Rdata2_in)
   // R-Type: Rdata2, I-Type/Load: imm_i_type_sext, S-Type: imm_s_type_sext
   assign Rdata2_in = (opcode == `OPCODE_COMPUTE_IMMEDIATE) | (opcode == `OPCODE_LOAD) | (opcode == `OPCODE_JALR) ? imm_i_type_sext : // I-Type
                     (opcode == `OPCODE_STORE) ? imm_s_type_sext : // S-Type
                     Rdata2; // R-Type and others
         
   // ALU Funct7 Mux (eu_funct7_in) (FIXED: Branch logic)
   assign eu_funct7_in = (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BEQ | funct3 == `FUNC_BNE)) ? `AUX_FUNC_SUB : 
                         (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BLT | funct3 == `FUNC_BGE | funct3 == `FUNC_BLTU | funct3 == `FUNC_BGEU)) ? `AUX_FUNC_ADD : // All comparisons use R-Type ADD/SLT auxfunc
                         (opcode == `OPCODE_COMPUTE_IMMEDIATE) ? 7'b0110000: funct7; // I-Type uses FUNC_3 (7'b0110000)
                            
   // ALU Funct3 Mux (eu_funct3_in) (FIXED: Branch logic)
   assign eu_funct3_in = (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BEQ | funct3 == `FUNC_BNE)) ? `FUNC_ADD : // BEQ/BNE: Use ADD func3 (to trigger SUB when auxFunc=FUNC_1)
                         (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BLT | funct3 == `FUNC_BGE)) ? `FUNC_SLT : // BLT/BGE: Use SLT func3
                         (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BLTU | funct3 == `FUNC_BGEU)) ? `FUNC_SLTU : // BLTU/BGEU: Use SLTU func3
                         funct3; // Default to instruction's funct3 for Load/Store/R-Type/I-Type

   // Data Address (Load/Store)
   assign DataAddr = (opcode == `OPCODE_LOAD) | (opcode == `OPCODE_STORE) ? eu_out : 32'b0;

   // Memory Size (for Load/Store)
   assign MemSize = (opcode == `OPCODE_LOAD | opcode == `OPCODE_STORE) ? InstWord[13:12] : 2'b00;

   // Load Data Extraction Logic (FIXED: For unaligned byte/halfword loads)
   // DataWord contains the 32-bit word read from memory at the aligned address (DataAddrW)
   
   // Byte selector logic (selects the correct byte based on DataAddr[1:0] - little-endian)
   wire [7:0] mem_read_byte = (DataAddr[1:0] == 2'b00) ? DataWord[7:0] :
                            (DataAddr[1:0] == 2'b01) ? DataWord[15:8] :
                            (DataAddr[1:0] == 2'b10) ? DataWord[23:16] :
                                                      DataWord[31:24];

   // Halfword selector logic (selects the correct halfword based on DataAddr[1] - little-endian)
   wire [15:0] mem_read_hword = (DataAddr[1] == 1'b0) ? DataWord[15:0] : DataWord[31:16];

   // Register Write Data (RWrdata) Mux (FIXED: LUI, AUIPC, Load instruction extraction)
   assign RWrdata = (opcode == `OPCODE_LUI) ? imm_u_type_shifted :  // LUI
                    (opcode == `OPCODE_AUIPC) ? PC + imm_u_type_shifted : // AUIPC (FIXED: correct addition)
                    (opcode == `OPCODE_JAL) ? (PC + 4) : // JAL (return address)
                    (opcode == `OPCODE_JALR) ? (PC + 4) : // JALR (return address)
                    // Load Instructions (FIXED: using mem_read_byte/hword)
                    (opcode == `OPCODE_LOAD && (funct3 == `FUNC_LB)) ? {{24{mem_read_byte[7]}}, mem_read_byte} : // lb (signed)
                    (opcode == `OPCODE_LOAD && (funct3 == `FUNC_LH)) ? {{16{mem_read_hword[15]}}, mem_read_hword} : // lh (signed)
                    (opcode == `OPCODE_LOAD && (funct3 == `FUNC_LW)) ? DataWord : // lw (signed)
                    (opcode == `OPCODE_LOAD && (funct3 == `FUNC_LBU)) ? {{24{1'b0}}, mem_read_byte} : // lbu (unsigned)
                    (opcode == `OPCODE_LOAD && (funct3 == `FUNC_LHU)) ? {{16{1'b0}}, mem_read_hword} : // lhu (unsigned)
                    // Compute/I-Type Instructions
                    (opcode == `OPCODE_COMPUTE_IMMEDIATE) ? eu_out : 
                    (opcode == `OPCODE_COMPUTE) ? eu_out : 32'b0;  
    
   // Register Write Enable (RWrEn)
   assign RWrEn = (opcode == `OPCODE_LUI) | (opcode == `OPCODE_AUIPC) |
                   (opcode == `OPCODE_JAL) | (opcode == `OPCODE_JALR) |
                   (opcode == `OPCODE_LOAD) | (opcode == `OPCODE_COMPUTE_IMMEDIATE) |
                   (opcode == `OPCODE_COMPUTE);
    
   // Memory Write Enable (MemWrEn)
   assign MemWrEn = (opcode == `OPCODE_STORE);
   
   // Store Data Mux (Data to be written to memory)
   assign StoreData_in = (funct3 == `FUNC_SB) ? {24'b0, Rdata2[7:0]} : // sb
                        (funct3 == `FUNC_SH) ? {16'b0, Rdata2[15:0]} : // sh
                        Rdata2; // sw

   // Halt logic
   wire invalid_op;
   wire valid_op;
   wire memory_alignment_error;
   
   assign halt = !valid_op | memory_alignment_error; 
   
   // Simplified Valid Op to catch all supported instructions
   assign valid_op = (opcode == `OPCODE_LUI) | (opcode == `OPCODE_AUIPC)|
                     (opcode == `OPCODE_JAL) | (opcode == `OPCODE_JALR) |
                     (opcode == `OPCODE_BRANCH) | (opcode == `OPCODE_LOAD) |
                     (opcode == `OPCODE_STORE) | (opcode == `OPCODE_COMPUTE_IMMEDIATE) |
                     (opcode == `OPCODE_COMPUTE);
    
   // Memory Alignment Error
   assign memory_alignment_error = 
         ((opcode == `OPCODE_LOAD | opcode == `OPCODE_STORE) && (funct3 == `FUNC_LH | funct3 == `FUNC_LHU | funct3 == `FUNC_SH) && (DataAddr[0] != 1'b0)) | 
         ((opcode == `OPCODE_LOAD | opcode == `OPCODE_STORE) && (funct3 == `FUNC_LW | funct3 == `FUNC_SW) && (DataAddr[1:0] != 2'b00));
               
   // System State 
   Mem   MEM(.InstAddr(PC), .InstOut(InstWord), 
            .DataAddr(DataAddr), .DataSize(MemSize), .DataIn(StoreData_in), .DataOut(DataWord), .WE(MemWrEn), .CLK(clk));

   RegFile RF(.AddrA(Rsrc1), .DataOutA(Rdata1), 
	      .AddrB(Rsrc2), .DataOutB(Rdata2), 
	      .AddrW(Rdst), .DataInW(RWrdata), .WenW(RWrEn), .CLK(clk));

   Reg PC_REG(.Din(NPC), .Qout(PC), .WE(1'b1), .CLK(clk), .RST(rst));

   // Hardwired to support R-Type instructions -- please add muxes and other control signals
   ExecutionUnit EU(.out(eu_out), .opA(Rdata1), .opB(Rdata2_in), .func(eu_funct3_in), .auxFunc(eu_funct7_in), .opBS(Shamt), .sr_C(SR_control));

   // Next PC Mux
   assign PC_Plus_4 = PC + 4;
   
   wire [31:0] branch_target = PC + imm_b_type;
   wire [31:0] jal_target = PC + imm_j_type_offset; // JAL Target
   wire [31:0] jalr_target = (Rdata1 + imm_i_type_sext) & 32'hFFFFFFFE; // JALR Target (FIXED: using imm_i_type_sext)

   assign NPC = (opcode == `OPCODE_JAL) ? jal_target : 
                (opcode == `OPCODE_JALR) ? jalr_target :
                // BEQ/BNE - Use SUB output (eu_out is the difference)
                (opcode == `OPCODE_BRANCH && funct3 == `FUNC_BEQ && eu_out == 32'b0) ? branch_target : 
                (opcode == `OPCODE_BRANCH && funct3 == `FUNC_BNE && eu_out != 32'b0) ? branch_target : 
                // BLT/BLTU - Use SLT/SLTU output (eu_out is 1 if R1 < R2)
                (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BLT | funct3 == `FUNC_BLTU) && eu_out == 32'd1) ? branch_target : 
                // BGE/BGEU - Use SLT/SLTU output (eu_out is 0 if R1 >= R2)
                (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BGE | funct3 == `FUNC_BGEU) && eu_out == 32'd0) ? branch_target : PC_Plus_4; 
    
endmodule // SingleCycleCPU


module ExecutionUnit(out, opA, opB, func, auxFunc, opBS, sr_C);
   output [`WORD_WIDTH-1:0] out;
   input [`WORD_WIDTH-1:0]  opA, opB;
   input [2:0] 	 func;
   input [6:0] 	 auxFunc;
   input [4:0] 	 opBS;
   input [1:0] 	 sr_C;  

   
   //Copied over from Zach's Lab 2
   //define operation codes
    localparam OP_ADD = 3'b000, //localparam only exists inside the module
               OP_SUB = 3'b000,
               OP_SLL = 3'b001,
               OP_SLT  = 3'b010,
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
   wire signed   [31:0] sA = opA;
   wire signed   [31:0] sB = opB;
   wire         [31:0] uA = opA;
   wire         [31:0] uB = opB; 
   wire signed  [63:0] sextsA = { {32{sA[31]}}, sA };
   wire signed  [63:0] zext_uB = {32'b0, sB};
   wire signed  [63:0] mul_ss  = sA * sB;
   wire signed  [63:0] mul_su = $signed(sextsA) * $signed(zext_uB);
   wire         [63:0] mul_uu  = uA * uB;

   wire div_by_zero = (opB == 32'b0);
   
   // DIV Logic 
   wire signed [31:0] div_q_signed = div_by_zero ? 32'hFFFFFFFF :  
                                     (sA == 32'sh80000000 && sB == 32'hFFFFFFFF) ? 32'sh80000000 : 
                                     sA / sB; 
   // DIVU Logic (Correct)
   wire [31:0] div_q_unsigned = div_by_zero ? 32'hFFFFFFFF : uA / uB;
   
   // REM Logic (Correct)
   wire signed [31:0] rem_r_signed = div_by_zero ? sA : 
                                    (sA == 32'sh80000000 && sB == 32'hFFFFFFFF) ? 32'sd0 : sA % sB;
   // REMU Logic (Correct)
   wire [31:0] rem_r_unsigned = div_by_zero ? uA : uA % uB;


endmodule // ExecutionUnit