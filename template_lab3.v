// Template for Northwestern - CompEng 361 - Lab3 -- Version 1.1
// Groupname: Zach Tey, Matias Ketema
// NetIDs: vcs5888, 

// Some useful defines...please add your own
`define WORD_WIDTH 32
`define NUM_REGS 32
`define OPCODE_COMPUTE    7'b0110011
`define OPCODE_BRANCH     7'b1100011
`define OPCODE_LOAD       7'b0000011
`define OPCODE_STORE      7'b0100011 
`define FUNC_ADD      3'b000
`define AUX_FUNC_ADD  7'b0000000
`define AUX_FUNC_SUB  7'b0100000
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
   wire [9:0] imm_u_type;
   wire [6:0] imm_front_s_type;
   wire [4:0] imm_back_s_type; 
   wire [19:0] imm_i_type;

   wire [`WORD_WIDTH-1:0] NPC, PC_Plus_4;
   wire [6:0]  opcode;

   wire [6:0]  funct7;
   wire [2:0]  funct3;

   wire invalid_op;
   
   //Characterize the op-code to its instruction type (R, I, S, U)
   wire [1:0] cur_inst_type;
   parameter R_TYPE = 2'b00;
   parameter I_TYPE = 2'b01;
   parameter S_TYPE = 2'b10;
   parameter U_TYPE = 2'b11;

   //For lui
      //Data
         assign RWrdata = (opcode = 7'b0110111) ? (imm_u_type << 12) : 0;
         assign RWrdata = (opcode = 7'b0110111) ? (Rdst) : 0;
         assign cur_inst_type = (opcode = 7'b0110111) ? U_TYPE : 0; //not sure if i need this characterization of instruction type
      //Control
         assign RWrEn = (opcode = 7'b0110111) ? 1 : 0;  //need to write to register
   

   // Only support R-TYPE ADD and SUB
   assign halt = invalid_op;
   assign invalid_op = !((opcode == `OPCODE_COMPUTE) && (funct3 == `FUNC_ADD) &&
		      ((funct7 == `AUX_FUNC_ADD) || (funct7 == `AUX_FUNC_SUB)));
     
   // System State 
   Mem   MEM(.InstAddr(PC), .InstOut(InstWord), 
            .DataAddr(DataAddr), .DataSize(MemSize), .DataIn(StoreData), .DataOut(DataWord), .WE(MemWrEn), .CLK(clk));

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
   assign imm_u_type = InstWord[32:12];
   assign imm_front_s_type = InstWord[32:26];
   assign imm_back_s_type = InstWord[11:7];
   assign imm_i_type = InstWord[31:20]; 

   assign MemWrEn = 1'b0; // Change this to allow stores
   //assign RWrEn = 1'b1;  // At the moment every instruction will write to the register file

   // Hardwired to support R-Type instructions -- please add muxes and other control signals
   ExecutionUnit EU(.out(RWrdata), .opA(Rdata1), .opB(Rdata2), .func(funct3), .auxFunc(funct7));

   // Fetch Address Datapath
   assign PC_Plus_4 = PC + 4;
   assign NPC = PC_Plus_4;
   
endmodule // SingleCycleCPU


// Incomplete version of Lab2 execution unit
// You will need to extend it. Feel free to modify the interface also
module ExecutionUnit(out, opA, opB, func, auxFunc);
   output [`WORD_WIDTH-1:0] out;
   input [`WORD_WIDTH-1:0]  opA, opB;
   input [2:0] 	 func;
   input [6:0] 	 auxFunc;

   // wire [`WORD_WIDTH-1:0] 	 addSub;

   // // Only supports add and subtract
   // assign addSub = (auxFunc == 7'b0100000) ? (opA - opB) : (opA + opB);
   // assign out = (func == 3'b000) ? addSub : 32'hXXXXXXXX;
   
   //Copied over from Zach's Lab 2
   //define operation codes
    localparam OP_ADD = 3'b000; //localparam only exists inside the module
    localparam OP_SUB = 3'b000,
               OP_SLL = 3'b001,
               OP_SLT  = 3'b010,
               OP_SLTU = 3'b011,
               OP_XOR = 3'b100,
               OP_SRL = 3'b101,
               OP_SRA= 3'b101,
               OP_OR = 3'b110,
               OP_AND = 3'b111;
    localparam FUNC_0 = 7'b0000000,
               FUNC_1 = 7'b0100000;

  //Dataflow model
    assign out =
      (func == OP_ADD && auxFunc == FUNC_0) ? (opA + opB) :
      (func == OP_SUB && auxFunc == FUNC_1) ? (opA - opB) :
      (func == OP_SLL && auxFunc == FUNC_0) ? (opA <<  opB[4:0]) :
      (func == OP_SLT && auxFunc == FUNC_0) ? (($signed(opA) <  $signed(opB)) ? 32'd1 : 32'd0) :
      (func == OP_SLTU && auxFunc == FUNC_0) ? ((opA < opB) ? 32'd1 : 32'd0) :
      (func == OP_XOR && auxFunc == FUNC_0) ? (opA ^ opB) :
      (func == OP_SRL && auxFunc == FUNC_0) ? (opA >>  opB[4:0]) :
      (func == OP_SRA && auxFunc == FUNC_1) ? ((opA >> opB[4:0]) | ({32{opA[31]}} << (32 - opB[4:0]))) :
      (func == OP_OR  && auxFunc == FUNC_0) ? (opA | opB) :
      (func == OP_AND && auxFunc == FUNC_0) ? (opA & opB) : 32'b0;

endmodule // ExecutionUnit
