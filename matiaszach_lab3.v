// Template for Northwestern - CompEng 361 - Lab3 -- Version 1.1
// Groupname: Zach Tey, Matias Ketema
// NetIDs: vcs5888, tnc5178

// Some useful defines...please add your own
//General Parameters
   `define WORD_WIDTH 32
   `define NUM_REGS 32
//Opcodes
   `define OPCODE_COMPUTE    7'b0110011
   `define OPCODE_COMPUTE_IMMEDIATE 7'b0010011
   `define OPCODE_BRANCH     7'b1100011
   `define FUNC_BEQ 3'b000
   `define FUNC_BNE 3'b001
   `define FUNC_BLT 3'b100
   `define FUNC_BGE 3'b101
   `define FUNC_BLTU 3'b110
   `define FUNC_BGEU 3'b111
   `define OPCODE_LOAD       7'b0000011
   `define FUNC_LB 3'b000
   `define FUNC_LH 3'b001
   `define FUNC_LW 3'b010
   `define FUNC_LBU 3'b100
   `define FUNC_LHU 3'b101
   `define OPCODE_STORE      7'b0100011 
   `define FUNC_SB 3'b000
   `define FUNC_SH 3'b001
   `define FUNC_SW 3'b010
   `define FUNC_ADD      3'b000
   `define AUX_FUNC_ADD  7'b0000000
   `define AUX_FUNC_SUB  7'b0100000
   `define AUX_FUNC_M  7'b0000001
   `define OPCODE_LUI 7'b0110111
   `define OPCODE_AUIPC 7'b0010111
   `define OPCODE_JAL 7'b1101111 
   `define OPCODE_JALR 7'b1100111 
// idk what there are for yet
   `define SIZE_BYTE  2'b00
   `define SIZE_HWORD 2'b01
   `define SIZE_WORD  2'b10

module SingleCycleCPU(halt, clk, rst);
   output halt;
   input clk, rst;

   wire [`WORD_WIDTH-1:0] PC, InstWord;
   wire [`WORD_WIDTH-1:0] DataAddr, StoreData, DataWord;
   wire [1:0]  MemSize;
   wire        MemWrEn;
   
   wire [4:0]  Rsrc1, Rsrc2, Rdst;
   wire [`WORD_WIDTH-1:0] Rdata1, Rdata2, RWrdata;
   wire        RWrEn;
   wire [19:0] imm_u_type;
   wire [6:0] imm_front_s_type;
   wire [4:0] imm_back_s_type; 
   wire [19:0] imm_i_type;
   wire [31:0] imm_j_type;
   wire [31:0] imm_b_type;

   wire [`WORD_WIDTH-1:0] NPC, PC_Plus_4;
   wire [6:0]  opcode;

   wire [6:0]  funct7;
   wire [2:0]  funct3;

   wire invalid_op;
   wire valid_op;
   wire memory_alignment_error;

   //Inputs/outputs of PC register, MEM, RF; We need to mux them depending on the instruction
   //Don't double drive outputs of mem, reg, ex; They will result in Xs on waveform
   wire [31:0] eu_out;
   wire [6:0] eu_funct7_in;
   wire [2:0] eu_funct3_in;
   wire [31:0] pc_reg_in;
   wire [31:0] Rdata2_in;
   wire [31:0] StoreData_in;

   //Characterize the op-code to its instruction type (R, I, S, U)
   //tbh not sure if this is needed so maybe can delete, but good information to have
   wire [3:0] cur_inst_type;
   parameter R_TYPE = 3'b000;
   parameter I_TYPE = 3'b001;
   parameter S_TYPE = 3'b010;
   parameter U_TYPE = 3'b011;
   parameter B_TYPE = 3'b011;

   //Input Controls to RF, MEM
      //Data
         assign RWrdata = (opcode == `OPCODE_LUI) ? (sext_imm_u_type << 12) :  //lui
                          (opcode == `OPCODE_AUIPC) ? (sext_imm_u_type << 12 + PC) : //auipc 
                          (opcode == `OPCODE_JAL) ? (PC + 4) : //jal
                          (opcode == `OPCODE_JALR) ? (PC + 4) : //jalr
                          (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LB)) ? {{24{DataWord[7]}}, DataWord[7:0]} : //lb
                          (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LH)) ? {{16{DataWord[15]}}, DataWord[15:0]} : //lh  
                          (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LW)) ? DataWord : //lw  
                          (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LBU)) ? {{24{1'b0}}, DataWord[7:0]} : //lbu   
                          (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LHU)) ? {{16{1'b0}}, DataWord[15:0]} : //lhu  
                          (opcode ==  `OPCODE_COMPUTE_IMMEDIATE) ? eu_out : //compute_i instructions 
                          (opcode ==  `OPCODE_COMPUTE) ? eu_out : 0; //compute instructions          
         assign cur_inst_type = (opcode == `OPCODE_LUI) ? U_TYPE : 0; //not sure if i need this characterization of instruction type
         assign eu_funct7_in = (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BEQ | funct3 == `FUNC_BNE)) ? `AUX_FUNC_SUB : //beq, bne 
                               (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BLT | funct3 == `FUNC_BGE | funct3 == `FUNC_BLTU | funct3 == `FUNC_BGEU)) ? `AUX_FUNC_ADD : //blt, bge, bltu, bgeu
                               (opcode == `OPCODE_COMPUTE_IMMEDIATE) ? 7'b0000000: 
                               funct7; 
         assign eu_funct3_in = (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BNE)) ? 3'b000 : //bne
                               (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BLT | funct3 == `FUNC_BGE)) ? 3'b010 : //blt, bge
                               (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BLTU | funct3 == `FUNC_BGEU)) ? 3'b011 : //bltu, bgeu
                               (opcode == `OPCODE_LOAD && (funct3 == `FUNC_LB | funct3 == `FUNC_LH | funct3 == `FUNC_LW | funct3 == `FUNC_LBU | funct3 == `FUNC_LHU)) ? 3'b000: //lb, lh, lw, lbu, lhu 
                               (opcode == `OPCODE_STORE && (funct3 == `FUNC_SB | funct3 == `FUNC_SH | funct3 == `FUNC_SW)) ? 3'b000: funct3; //sb, sh, sw
         assign Rdata2_in = (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LB | funct3 == `FUNC_LH | funct3 == `FUNC_LW | funct3 == `FUNC_LBU | funct3 == `FUNC_LHU)) ? {{20{imm_i_type[11]}},imm_i_type} : //lb, lh, lw, lbu, lhu
                            (opcode == `OPCODE_STORE && (funct3 == `FUNC_SB | funct3 == `FUNC_SH | funct3 == `FUNC_SW)) ? {{20{imm_front_s_type[6]}},imm_front_s_type, imm_back_s_type} : //sb, sh, sw
                            (opcode == `OPCODE_COMPUTE_IMMEDIATE) ? {{20{imm_i_type[11]}},imm_i_type} : Rdata2; //compute_i instructions
         assign DataAddr = (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LB | funct3 == `FUNC_LH | funct3 == `FUNC_LW | funct3 == `FUNC_LBU | funct3 == `FUNC_LHU)) ? (eu_out) : //lb, lh, lw, lbu, lhu
                           (opcode == `OPCODE_STORE && (funct3 == `FUNC_SB | funct3 == `FUNC_SH | funct3 == `FUNC_SW)) ? eu_out : 0; //sb, sh, sw
         assign MemSize = (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LB | funct3 == `FUNC_LBU)) ? 2'b00 : //lb, lbu
                          (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LH | funct3 == `FUNC_LHU)) ? 2'b01 : //lh, lhu
                          (opcode ==  `OPCODE_LOAD && (funct3 == `FUNC_LW)) ? 2'b10 : //lw
                          (opcode ==  `OPCODE_STORE && (funct3 == `FUNC_SB)) ? 2'b00 : //lb
                          (opcode ==  `OPCODE_STORE && (funct3 == `FUNC_SH)) ? 2'b01 : //lh
                          (opcode ==  `OPCODE_STORE && (funct3 == `FUNC_SW)) ? 2'b10 : 0; //lw
         assign StoreData_in = (opcode ==  `OPCODE_STORE && (funct3 == `FUNC_SB)) ? {{24{Rdata2[7]}}, Rdata2[7:0]} : //lb
                               (opcode ==  `OPCODE_STORE && (funct3 == `FUNC_SH)) ? {{16{Rdata2[15]}}, Rdata2[15:0]} : //lh
                               (opcode ==  `OPCODE_STORE && (funct3 == `FUNC_SW)) ? Rdata2 : 0; //lw

      //Control
         assign RWrEn = (opcode == `OPCODE_LUI) ? 1 : 
                        (opcode == `OPCODE_AUIPC) ? 1 : 
                        (opcode == `OPCODE_JAL) ? 1 : 
                        (opcode == `OPCODE_JALR) ? 1: 
                        (opcode == `OPCODE_LOAD) ? 1:  
                        (opcode == `OPCODE_COMPUTE_IMMEDIATE) ? 1 :  
                        (opcode == `OPCODE_COMPUTE) ? 1: 0; 
         assign MemWrEn = (opcode == `OPCODE_STORE) ? 1: 0;

         
   //Halt logic
      // Only support R-TYPE ADD and SUB
   assign halt = !valid_op | memory_alignment_error; 
   assign invalid_op = !((opcode == `OPCODE_COMPUTE) && (funct3 == `FUNC_ADD) &&
		      ((funct7 == `AUX_FUNC_ADD) || (funct7 == `AUX_FUNC_SUB)));
   assign valid_op = (opcode == `OPCODE_LUI) | (opcode == `OPCODE_AUIPC)|
                     (opcode == `OPCODE_JAL) | (opcode == `OPCODE_JALR) |
                     (opcode == `OPCODE_BRANCH) | (opcode == `OPCODE_LOAD) |
                     (opcode == `OPCODE_STORE) | (opcode == `OPCODE_COMPUTE_IMMEDIATE) |
                     (opcode == `OPCODE_COMPUTE);
   assign memory_alignment_error = ((((opcode == `OPCODE_LOAD | opcode == `OPCODE_STORE) && (funct3 == `FUNC_LH | funct3 == `FUNC_LHU | funct3 == `FUNC_SH)) && (DataAddr[0] != 1'b0)) ? 1'b1 : 1'b0) | 
                                   ((((opcode == `OPCODE_LOAD | opcode == `OPCODE_STORE) && (funct3 == `FUNC_LW | funct3 == `FUNC_SW)) && (DataAddr[1:0] != 2'b00)) ? 1'b1 : 1'b0);
               
   // System State 
   Mem   MEM(.InstAddr(PC), .InstOut(InstWord), 
            .DataAddr(DataAddr), .DataSize(MemSize), .DataIn(StoreData_in), .DataOut(DataWord), .WE(MemWrEn), .CLK(clk));

   RegFile RF(.AddrA(Rsrc1), .DataOutA(Rdata1), 
	      .AddrB(Rsrc2), .DataOutB(Rdata2), 
	      .AddrW(Rdst), .DataInW(RWrdata), .WenW(RWrEn), .CLK(clk));

   Reg PC_REG(.Din(NPC), .Qout(PC), .WE(1'b1), .CLK(clk), .RST(rst));

   // Instruction Decode
   assign opcode = InstWord[6:0];   
   assign Rdst = InstWord[11:7]; 
   assign Rsrc1 = InstWord[19:15]; 
   assign Rsrc2 = InstWord[24:20];
   assign funct3 = InstWord[14:12];  // R-Type, I-Type, S-Type
   assign funct7 = InstWord[31:25];  // R-Type
   assign imm_u_type = InstWord[31:12];
   assign sext_imm_u_type = {{12{InstWord[31]}},InstWord[31:12]};
   assign imm_front_s_type = InstWord[31:25];
   assign imm_back_s_type = InstWord[11:7];
   assign imm_i_type = InstWord[31:20]; 
   assign imm_j_type = (opcode == `OPCODE_JALR) ? ((Rdata1 + {{20{InstWord[31]}},InstWord[31:20]}) & 32'hFFFFFFFE) : //jalr
                     (PC + {{11{InstWord[31]}}, InstWord[19:12],InstWord[20], InstWord[30:21],1'b0}); //jal            
   assign imm_b_type = {{19{InstWord[31]}},   
                        InstWord[31],         
                        InstWord[7],          
                        InstWord[30:25],      
                        InstWord[11:8], 
                        1'b0      
                        };
   //assign MemWrEn = 1'b0; // Change this to allow stores
   //assign RWrEn = 1'b1;  // At the moment every instruction will write to the register file

   // Hardwired to support R-Type instructions -- please add muxes and other control signals
   ExecutionUnit EU(.out(eu_out), .opA(Rdata1), .opB(Rdata2_in), .func(eu_funct3_in), .auxFunc(eu_funct7_in));

   // Fetch Address Datapath, notably PC_MEM
   assign PC_Plus_4 = PC + 4;
   assign NPC = ((opcode == `OPCODE_JALR) | (opcode == `OPCODE_JAL)) ? imm_j_type : //jalr, jal
                (opcode == `OPCODE_BRANCH && funct3 == `FUNC_BEQ && eu_out == 0) ? (PC + imm_b_type) : //beq
                (opcode == `OPCODE_BRANCH && funct3 == `FUNC_BNE && eu_out != 0) ? (PC + imm_b_type) : //bne
                (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BLT | funct3 == `FUNC_BLTU) && eu_out == 1) ? (PC + imm_b_type) : //blt, bltu
                (opcode == `OPCODE_BRANCH && (funct3 == `FUNC_BGE | funct3 == `FUNC_BGEU) && eu_out == 0) ? (PC + imm_b_type) : PC_Plus_4; //bge, bgeu  
endmodule // SingleCycleCPU



module ExecutionUnit(out, opA, opB, func, auxFunc);
   output [`WORD_WIDTH-1:0] out;
   input [`WORD_WIDTH-1:0]  opA, opB;
   input [2:0] 	 func;
   input [6:0] 	 auxFunc;
   
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
               ///////////////
               OP_MUL = 3'b000,
               OP_MULH = 3'b001,
               OP_MULHSU = 3'b010,
               OP_MULHU= 3'b011,
               OP_DIV = 3'b100,
               OP_DIVU = 3'b101,
               OP_REM = 3'b110,
               OP_REMU = 3'b111;

    localparam FUNC_0 = 7'b0000000,
               FUNC_1 = 7'b0100000,
               FUNC_2 = 7'b0000001;

  //Dataflow model
    assign out =
      (func == OP_ADD && auxFunc == FUNC_0) ? (opA + opB) :
      (func == OP_SUB && auxFunc == FUNC_1) ? (opA - opB) :
      (func == OP_SLL && auxFunc == FUNC_0) ? (opA <<  opB[4:0]) :
      (func == OP_SLT && auxFunc == FUNC_0) ? (($signed(opA) < $signed(opB)) ? 32'd1 : 32'd0) :
      (func == OP_SLTU && auxFunc == FUNC_0) ? ((opA < opB) ? 32'd1 : 32'd0) :
      (func == OP_XOR && auxFunc == FUNC_0) ? (opA ^ opB) :
      (func == OP_SRL && auxFunc == FUNC_0) ? (opA >>  opB[4:0]) :
      (func == OP_SRA && auxFunc == FUNC_1) ? ((sA >>> opB[4:0])) :
      (func == OP_OR  && auxFunc == FUNC_0) ? (opA | opB) :
      (func == OP_AND && auxFunc == FUNC_0) ? (opA & opB) :

      (func == OP_MUL && auxFunc == FUNC_2) ? (mul_uu[31:0]) : 
      (func == OP_MULH && auxFunc == FUNC_2) ? (mul_ss[63:32]) : 
      (func == OP_MULHSU && auxFunc == FUNC_2) ? (mul_su[63:32]) : 
      (func == OP_MULHU && auxFunc == FUNC_2) ? (mul_uu[63:32]) : 
      (func == OP_DIV && auxFunc == FUNC_2) ? div_q_signed : 
      (func == OP_DIVU && auxFunc == FUNC_2) ? div_q_unsigned :
      (func == OP_REM && auxFunc == FUNC_2) ? rem_r_signed :
      (func == OP_REMU && auxFunc == FUNC_2) ? rem_r_unsigned : 32'b0;

   //M-instruction processsing ->
   // 64-bit products for mul variants
   wire signed   [31:0] sA = opA;
   wire signed   [31:0] sB = opB;
   wire         [31:0] uA = opA;
   wire         [31:0] uB = opB; 
   wire signed  [63:0] sextsA = { {32{sA[31]}}, sA };
   wire signed  [63:0] zext_uB = {32'b0, sB};
   wire signed  [63:0] uB_new = zext_uB;
   wire signed  [63:0] mul_ss  = sA * sB;
   wire signed  [63:0] mul_su = $signed(sextsA) * $signed(uB_new);
   wire         [63:0] mul_uu  = uA * uB;

   wire div_by_zero = (opB == 32'b0);
   wire signed [31:0] div_q_signed = div_by_zero ? 32'hFFFFFFFF :  // DIV: -1
                                     (sA == 32'sh80000000 && sB == 32'hFFFFFFFF) ? 32'sh80000000 : // overflow
                                     sA / sB; //normal division
   wire [31:0] div_q_unsigned = div_by_zero ? 32'hFFFFFFFF : uA / uB;
   
   wire signed [31:0] rem_r_signed = div_by_zero ? sA : 
                                    (sA == 32'sh80000000 && sB == -32'sd1) ? 32'sd0 :sA % sB;
   wire [31:0] rem_r_unsigned = div_by_zero ? uA : uA % uB;


endmodule // ExecutionUnit
