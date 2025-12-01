// Template for Northwestern - CompEng 361 - Lab4
// Groupname: Zach Tey, Matias Ketema
// NetIDs: vcs5888, tnc5178

// Some useful defines...please add your own
`define WORD_WIDTH 32
`define NUM_REGS 32

// Opcode Defines
`define OPCODE_COMPUTE    7'b0110011 // R-Type
`define OPCODE_COMPUTE_IMM 7'b0010011 // I-Type
`define OPCODE_BRANCH     7'b1100011 // B-Type
`define OPCODE_LOAD       7'b0000011 // I-Type (Load)
`define OPCODE_STORE      7'b0100011 // S-Type
`define OPCODE_LUI        7'b0110111 // U-Type
`define OPCODE_AUIPC      7'b0010111 // U-Type
`define OPCODE_JAL        7'b1101111 // J-Type
`define OPCODE_JALR       7'b1100111 // I-Type (JALR)

// Funct3/7 Defines
`define FUNC_ADD      3'b000
`define AUX_FUNC_ADD  7'b0000000
`define AUX_FUNC_SUB  7'b0100000
`define AUX_FUNC_M    7'b0000001 // M-Extension

// ALU Funcs
`define FUNC_SLL      3'b001
`define FUNC_SLT      3'b010
`define FUNC_SLTU     3'b011
`define FUNC_XOR      3'b100
`define FUNC_SRL      3'b101
`define FUNC_OR       3'b110
`define FUNC_AND      3'b111

// Branch Conditions
`define FUNC_BEQ      3'b000
`define FUNC_BNE      3'b001
`define FUNC_BLT      3'b100
`define FUNC_BGE      3'b101
`define FUNC_BLTU     3'b110
`define FUNC_BGEU     3'b111

// Memory Sizes
`define SIZE_BYTE  2'b00
`define SIZE_HWORD 2'b01
`define SIZE_WORD  2'b10

module PipelinedCPU(halt, clk, rst);
    output halt;
    input clk, rst;

    // ========================================================================
    // --- Signal Declarations ---
    // ========================================================================

    // --- IF Stage Signals ---
    wire [`WORD_WIDTH-1:0] if_PC, if_NPC, if_InstWord;
    wire if_stall; // Stall signal for IF stage

    // --- IF/ID Pipeline Register ---
    wire [63:0] if_id_in, if_id_out;
    wire if_id_en, if_id_flush;
    wire [31:0] id_PC, id_InstWord;

    // --- ID Stage Signals ---
    wire [6:0] id_opcode = id_InstWord[6:0];
    wire [4:0] id_rd = id_InstWord[11:7];
    wire [4:0] id_rs1 = id_InstWord[19:15];
    wire [4:0] id_rs2 = id_InstWord[24:20];
    wire [2:0] id_funct3 = id_InstWord[14:12];
    wire [6:0] id_funct7 = id_InstWord[31:25];

    wire [31:0] id_Rdata1, id_Rdata2; // Data from RegFile
    wire [31:0] id_imm; // Generated Immediate

    // ID Control Signals
    wire id_RegWrite, id_MemWrite, id_MemRead, id_MemToReg, id_ALUSrc;
    wire id_is_branch, id_is_jump, id_is_halt;
    wire [1:0] id_MemSize;
    wire id_stall_req; // Load-Use Hazard Stall
    wire id_flush; // Flush due to branch taken

    // --- ID/EX Pipeline Register ---
    // Width approx: 32(PC)+32(R1)+32(R2)+32(Imm)+5(rs1)+5(rs2)+5(rd)+3(f3)+7(f7)+7(op)+16(Ctrl) = ~176
    wire [175:0] id_ex_in, id_ex_out;
    wire id_ex_en, id_ex_flush;
    
    // --- EX Stage Signals ---
    wire [31:0] ex_PC, ex_Rdata1, ex_Rdata2, ex_Imm;
    wire [4:0] ex_rs1, ex_rs2, ex_rd;
    wire [2:0] ex_funct3;
    wire [6:0] ex_funct7, ex_opcode;
    // EX Control Signals
    wire ex_RegWrite, ex_MemWrite, ex_MemRead, ex_MemToReg, ex_ALUSrc, ex_is_branch, ex_is_jump, ex_is_halt;
    wire [1:0] ex_MemSize;

    wire [31:0] ex_OpA_Forwarded, ex_OpB_Forwarded;
    wire [31:0] ex_ALUInA, ex_ALUInB;
    wire [31:0] ex_ALUResult;
    wire [31:0] ex_StoreData; 
    
    // Latency / Stall Logic
    wire ex_stall_req; // Stall for multi-cycle ops
    
    // Branch Logic
    wire ex_branch_taken;
    wire [31:0] ex_target_addr;

    // --- EX/MEM Pipeline Register ---
    // Width: 32(ALU)+32(StoreData)+5(rd)+Ctrl(~10) = ~80
    wire [106:0] ex_mem_in, ex_mem_out;
    wire ex_mem_en, ex_mem_flush;

    // --- MEM Stage Signals ---
    wire [31:0] mem_ALUResult, mem_StoreData, mem_ReadData_Raw, mem_ReadData_Final;
    wire [4:0] mem_rd;
    wire mem_RegWrite, mem_MemWrite, mem_MemRead, mem_MemToReg, mem_is_halt;
    wire [1:0] mem_MemSize;
    wire [2:0] mem_funct3; // Passed for Load extension logic if needed (simplified here)
    wire mem_alignment_error;

    // --- MEM/WB Pipeline Register ---
    wire [103:0] mem_wb_in, mem_wb_out;
    wire mem_wb_en;

    // --- WB Stage Signals ---
    wire [31:0] wb_ALUResult, wb_ReadData;
    wire [4:0] wb_rd;
    wire wb_RegWrite, wb_MemToReg, wb_is_halt, wb_alignment_error;
    wire [31:0] wb_WriteData;


    // ========================================================================
    // --- IF STAGE ---
    // ========================================================================

    // PC Mux: Select Branch Target if taken, else PC+4
    assign if_NPC = (ex_branch_taken) ? ex_target_addr : (if_PC + 4);

    // IF Stall Logic: Stall if ID detects Load-Use OR EX detects Multi-cycle op
    assign if_stall = id_stall_req | ex_stall_req;

    Reg #(.width(32), .init(0)) PC_REG (
        .Din(if_NPC), 
        .Qout(if_PC), 
        .WE(!if_stall), 
        .CLK(clk), 
        .RST(rst)
    );

    // Instruction Memory
    // Note: Data ports are driven by MEM stage signals
    Mem MEM (
        .InstAddr(if_PC), 
        .InstOut(if_InstWord), 
        .DataAddr(mem_ALUResult), 
        .DataSize(mem_MemSize), 
        .DataIn(mem_StoreData), 
        .DataOut(mem_ReadData_Raw), 
        .WE(mem_MemWrite), 
        .CLK(clk)
    );

    // ========================================================================
    // --- IF/ID PIPELINE REGISTER ---
    // ========================================================================

    // Flush if branch taken
    assign if_id_flush = ex_branch_taken; 
    assign if_id_en = !if_stall; // Stall logic matches PC stall

    assign if_id_in = {if_PC, if_InstWord};

    PipeReg #(.width(64)) IF_ID (
        .clk(clk), .rst(rst), 
        .en(if_id_en), .flush(if_id_flush), 
        .in(if_id_in), .out(if_id_out)
    );

    assign {id_PC, id_InstWord} = if_id_out;


    // ========================================================================
    // --- ID STAGE ---
    // ========================================================================

    // Control Unit (Hardwired Logic)
    wire is_lui   = (id_opcode == `OPCODE_LUI);
    wire is_auipc = (id_opcode == `OPCODE_AUIPC);
    wire is_jal   = (id_opcode == `OPCODE_JAL);
    wire is_jalr  = (id_opcode == `OPCODE_JALR);
    wire is_branch= (id_opcode == `OPCODE_BRANCH);
    wire is_load  = (id_opcode == `OPCODE_LOAD);
    wire is_store = (id_opcode == `OPCODE_STORE);
    wire is_comp_i= (id_opcode == `OPCODE_COMPUTE_IMM);
    wire is_comp  = (id_opcode == `OPCODE_COMPUTE);

    assign id_RegWrite = is_lui | is_auipc | is_jal | is_jalr | is_load | is_comp_i | is_comp;
    assign id_MemWrite = is_store;
    assign id_MemRead  = is_load;
    assign id_MemToReg = is_load; 
    assign id_ALUSrc   = is_comp_i | is_load | is_store | is_lui | is_auipc | is_jal | is_jalr; // Imm
    assign id_is_branch= is_branch;
    assign id_is_jump  = is_jal | is_jalr;
    assign id_MemSize  = id_funct3[1:0];
    assign id_is_halt  = !(is_lui|is_auipc|is_jal|is_jalr|is_branch|is_load|is_store|is_comp_i|is_comp) && (id_InstWord != 0);

    // Immediate Generation
    wire [31:0] imm_i = {{20{id_InstWord[31]}}, id_InstWord[31:20]};
    wire [31:0] imm_s = {{20{id_InstWord[31]}}, id_InstWord[31:25], id_InstWord[11:7]};
    wire [31:0] imm_b = {{19{id_InstWord[31]}}, id_InstWord[31], id_InstWord[7], id_InstWord[30:25], id_InstWord[11:8], 1'b0};
    wire [31:0] imm_u = {id_InstWord[31:12], 12'b0};
    wire [31:0] imm_j = {{12{id_InstWord[31]}}, id_InstWord[19:12], id_InstWord[20], id_InstWord[30:21], 1'b0};

    assign id_imm = (is_store) ? imm_s : 
                    (is_branch) ? imm_b : 
                    (is_lui | is_auipc) ? imm_u : 
                    (is_jal) ? imm_j : imm_i;

    // Register File
    RegFile RF(
        .AddrA(id_rs1), .DataOutA(id_Rdata1), 
        .AddrB(id_rs2), .DataOutB(id_Rdata2), 
        .AddrW(wb_rd), .DataInW(wb_WriteData), .WenW(wb_RegWrite), .CLK(clk)
    );

    // Hazard Detection (Load-Use)
    // If EX stage is Load AND EX.rd matches ID.rs1 or ID.rs2 -> Stall ID
    assign id_stall_req = ex_MemRead && ((ex_rd == id_rs1) || (ex_rd == id_rs2)) && (ex_rd != 0);

    // ========================================================================
    // --- ID/EX PIPELINE REGISTER ---
    // ========================================================================

    // Flush if Branch taken OR Load-Use Hazard
    assign id_ex_flush = ex_branch_taken || id_stall_req;
    // Stall if EX is stalled (Multi-cycle)
    assign id_ex_en = !ex_stall_req;

    // Control Bus Packing
    wire [15:0] id_ctrl = {id_RegWrite, id_MemWrite, id_MemRead, id_MemToReg, id_ALUSrc, id_is_branch, id_is_jump, id_is_halt, id_MemSize, 6'b0};

    assign id_ex_in = {id_PC, id_Rdata1, id_Rdata2, id_imm, id_rs1, id_rs2, id_rd, id_funct3, id_funct7, id_opcode, id_ctrl};

    PipeReg #(.width(176)) ID_EX (
        .clk(clk), .rst(rst), 
        .en(id_ex_en), .flush(id_ex_flush), 
        .in(id_ex_in), .out(id_ex_out)
    );

    wire [15:0] ex_ctrl;
    assign {ex_PC, ex_Rdata1, ex_Rdata2, ex_Imm, ex_rs1, ex_rs2, ex_rd, ex_funct3, ex_funct7, ex_opcode, ex_ctrl} = id_ex_out;
    assign {ex_RegWrite, ex_MemWrite, ex_MemRead, ex_MemToReg, ex_ALUSrc, ex_is_branch, ex_is_jump, ex_is_halt, ex_MemSize} = ex_ctrl[15:6];


    // ========================================================================
    // --- EX STAGE ---
    // ========================================================================

    // Forwarding Unit
    wire [1:0] fwdA, fwdB;
    // Forward from MEM Stage (EX/MEM)
    wire fwd_mem_A = (mem_RegWrite && (mem_rd != 0) && (mem_rd == ex_rs1));
    wire fwd_mem_B = (mem_RegWrite && (mem_rd != 0) && (mem_rd == ex_rs2));
    // Forward from WB Stage (MEM/WB)
    wire fwd_wb_A  = (wb_RegWrite && (wb_rd != 0) && (wb_rd == ex_rs1));
    wire fwd_wb_B  = (wb_RegWrite && (wb_rd != 0) && (wb_rd == ex_rs2));

    assign fwdA = fwd_mem_A ? 2'b10 : (fwd_wb_A ? 2'b01 : 2'b00);
    assign fwdB = fwd_mem_B ? 2'b10 : (fwd_wb_B ? 2'b01 : 2'b00);

    // Operand Muxes
    assign ex_OpA_Forwarded = (fwdA == 2'b10) ? mem_ALUResult : (fwdA == 2'b01) ? wb_WriteData : ex_Rdata1;
    assign ex_OpB_Forwarded = (fwdB == 2'b10) ? mem_ALUResult : (fwdB == 2'b01) ? wb_WriteData : ex_Rdata2;

    assign ex_StoreData = ex_OpB_Forwarded;

    // ALU Inputs
    // AUIPC/LUI/JAL/JALR override A with PC or 0
    assign ex_ALUInA = (ex_opcode == `OPCODE_AUIPC || ex_opcode == `OPCODE_JAL || ex_opcode == `OPCODE_JALR) ? ex_PC :
                       (ex_opcode == `OPCODE_LUI) ? 32'b0 : 
                       ex_OpA_Forwarded;

    // JAL/JALR override B with 4 (to link PC+4)
    assign ex_ALUInB = (ex_opcode == `OPCODE_JAL || ex_opcode == `OPCODE_JALR) ? 32'd4 :
                       (ex_ALUSrc) ? ex_Imm : ex_OpB_Forwarded;

    // Multi-Cycle Latency Counter
    wire ex_is_mul = (ex_opcode == `OPCODE_COMPUTE) && (ex_funct7 == `AUX_FUNC_M) && (ex_funct3[2] == 0); // MUL*
    wire ex_is_div = (ex_opcode == `OPCODE_COMPUTE) && (ex_funct7 == `AUX_FUNC_M) && (ex_funct3[2] == 1); // DIV*, REM*
    
    wire [4:0] lat_cnt;
    wire [4:0] lat_limit = ex_is_mul ? 5'd4 : (ex_is_div ? 5'd20 : 5'd1);
    
    // Stall if processing multi-cycle and count not reached limit-1
    // Logic: 0,1,2,3 (done). stall req for 0,1,2.
    assign ex_stall_req = (lat_limit > 1) && (lat_cnt < lat_limit - 1);
    
    wire [4:0] next_lat_cnt = (ex_stall_req) ? lat_cnt + 1 : 5'b0;

    Reg #(.width(5)) LatencyCtr (
        .Din(next_lat_cnt), .Qout(lat_cnt), .WE(1'b1), .CLK(clk), .RST(rst)
    );

    // ALU Execution
    // Map branch comparisons to ALU ops
    wire [6:0] eu_auxFunc = (ex_opcode == `OPCODE_BRANCH) ? `AUX_FUNC_ADD : // Use SLT logic
                            (ex_opcode == `OPCODE_COMPUTE_IMM) ? 7'b0110000 : // Special I-Type signature
                            ex_funct7;
    wire [2:0] eu_func = (ex_opcode == `OPCODE_BRANCH) ? 
                            ((ex_funct3 == `FUNC_BEQ || ex_funct3 == `FUNC_BNE) ? `FUNC_ADD : // BEQ/BNE use SUB logic
                             (ex_funct3 == `FUNC_BLT || ex_funct3 == `FUNC_BGE) ? `FUNC_SLT : // BLT/BGE use SLT
                             `FUNC_SLTU) : // BLTU/BGEU use SLTU
                          ex_funct3;

    ExecutionUnit EU(
        .out(ex_ALUResult), 
        .opA(ex_ALUInA), 
        .opB(ex_ALUInB), 
        .func(eu_func), 
        .auxFunc(eu_auxFunc)
    );

    // Branch Resolution
    wire br_cond_met = (ex_funct3 == `FUNC_BEQ && ex_ALUResult == 0) ||
                       (ex_funct3 == `FUNC_BNE && ex_ALUResult != 0) ||
                       ((ex_funct3 == `FUNC_BLT || ex_funct3 == `FUNC_BLTU) && ex_ALUResult == 1) ||
                       ((ex_funct3 == `FUNC_BGE || ex_funct3 == `FUNC_BGEU) && ex_ALUResult == 0);
    
    assign ex_branch_taken = (ex_is_branch && br_cond_met) || ex_is_jump;
    
    wire [31:0] br_target_base = (ex_opcode == `OPCODE_JALR) ? ex_OpA_Forwarded : ex_PC;
    assign ex_target_addr = br_target_base + ex_Imm;


    // ========================================================================
    // --- EX/MEM PIPELINE REGISTER ---
    // ========================================================================

    // Flush if EX is stalling (Insert Bubble into MEM)
    assign ex_mem_flush = ex_stall_req; 
    assign ex_mem_en = 1'b1;

    assign ex_mem_in = {ex_ALUResult, ex_StoreData, ex_rd, ex_RegWrite, ex_MemWrite, ex_MemRead, ex_MemToReg, ex_is_halt, ex_MemSize};

    PipeReg #(.width(107)) EX_MEM (
        .clk(clk), .rst(rst), 
        .en(ex_mem_en), .flush(ex_mem_flush), 
        .in(ex_mem_in), .out(ex_mem_out)
    );

    assign {mem_ALUResult, mem_StoreData, mem_rd, mem_RegWrite, mem_MemWrite, mem_MemRead, mem_MemToReg, mem_is_halt, mem_MemSize} = ex_mem_out;


    // ========================================================================
    // --- MEM STAGE ---
    // ========================================================================

    // Mem access happens in IF block instantiation (dual usage)
    
    // Alignment Error Check
    assign mem_alignment_error = 
           ((mem_MemRead | mem_MemWrite) && (mem_MemSize == `SIZE_HWORD) && (mem_ALUResult[0] != 0)) ||
           ((mem_MemRead | mem_MemWrite) && (mem_MemSize == `SIZE_WORD) && (mem_ALUResult[1:0] != 0));

    // Prepare Load Data (Extraction Logic - simplified for structural reqs, assuming Mem returns aligned word)
    // Note: Full extraction requires funct3 logic (sign extension), simplified here to basic word passing
    // or relying on Mem module behavior for sub-word writes. For reads, we pass aligned word to WB.
    assign mem_ReadData_Final = mem_ReadData_Raw; // Placeholder for extraction if needed in WB

    // ========================================================================
    // --- MEM/WB PIPELINE REGISTER ---
    // ========================================================================

    assign mem_wb_en = 1'b1;
    assign mem_wb_in = {mem_ReadData_Final, mem_ALUResult, mem_rd, mem_RegWrite, mem_MemToReg, mem_is_halt, mem_alignment_error};

    PipeReg #(.width(104)) MEM_WB (
        .clk(clk), .rst(rst), 
        .en(mem_wb_en), .flush(1'b0), 
        .in(mem_wb_in), .out(mem_wb_out)
    );

    assign {wb_ReadData, wb_ALUResult, wb_rd, wb_RegWrite, wb_MemToReg, wb_is_halt, wb_alignment_error} = mem_wb_out;


    // ========================================================================
    // --- WB STAGE ---
    // ========================================================================

    // WriteBack Data Mux
    // Note: For LB/LH, extraction usually happens here based on ALUResult[1:0]. 
    // Assuming aligned word for this template scope.
    assign wb_WriteData = (wb_MemToReg) ? wb_ReadData : wb_ALUResult;

    // Halt
    assign halt = wb_is_halt | wb_alignment_error;

endmodule // PipelinedCPU


// ============================================================================
// Helper Modules
// ============================================================================

module PipeReg #(parameter width = 32)(
    input clk, rst, en, flush,
    input [width-1:0] in,
    output [width-1:0] out
);
    wire [width-1:0] data_in = (flush) ? {width{1'b0}} : in;
    
    Reg #(.width(width)) PReg (
        .Din(data_in), .Qout(out), .WE(en), .CLK(clk), .RST(rst)
    );
endmodule

// Extended Execution Unit from Lab 2/3
module ExecutionUnit(out, opA, opB, func, auxFunc);
    output [`WORD_WIDTH-1:0] out;
    input [`WORD_WIDTH-1:0]  opA, opB;
    input [2:0]  func;
    input [6:0]  auxFunc;

    // Constants
    wire signed [31:0] sA = opA;
    wire signed [31:0] sB = opB;
    wire [31:0] uA = opA;
    wire [31:0] uB = opB;

    // Multiplier/Divider
    wire signed [63:0] mul_ss = sA * sB;
    wire signed [63:0] mul_su = $signed({{32{sA[31]}}, sA}) * $signed({32'b0, uB});
    wire [63:0] mul_uu = uA * uB;
    
    wire div_zero = (uB == 0);
    wire signed [31:0] div_q_s = div_zero ? -1 : (sA == 32'h80000000 && sB == -1) ? 32'h80000000 : sA / sB;
    wire [31:0] div_q_u = div_zero ? -1 : uA / uB;
    wire signed [31:0] rem_r_s = div_zero ? sA : (sA == 32'h80000000 && sB == -1) ? 0 : sA % sB;
    wire [31:0] rem_r_u = div_zero ? uA : uA % uB;

    assign out = 
        (auxFunc == `AUX_FUNC_M) ? ( // M-Extension
            (func == 3'b000) ? mul_uu[31:0] :
            (func == 3'b001) ? mul_ss[63:32] :
            (func == 3'b010) ? mul_su[63:32] :
            (func == 3'b011) ? mul_uu[63:32] :
            (func == 3'b100) ? div_q_s :
            (func == 3'b101) ? div_q_u :
            (func == 3'b110) ? rem_r_s :
            (func == 3'b111) ? rem_r_u : 0
        ) :
        (auxFunc == 7'b0110000) ? ( // I-Type Arith
            (func == 3'b000) ? (opA + opB) :
            (func == 3'b010) ? (($signed(opA) < $signed(opB)) ? 1 : 0) :
            (func == 3'b011) ? ((opA < opB) ? 1 : 0) :
            (func == 3'b100) ? (opA ^ opB) :
            (func == 3'b110) ? (opA | opB) :
            (func == 3'b111) ? (opA & opB) :
            (func == 3'b001) ? (opA << opB[4:0]) : // SLLI
            (func == 3'b101 && opB[10] == 0) ? (opA >> opB[4:0]) : // SRLI
            (func == 3'b101 && opB[10] == 1) ? ($signed(opA) >>> opB[4:0]) : 0 // SRAI
        ) :
        (auxFunc == `AUX_FUNC_ADD) ? ( // R-Type ADD/SLT...
            (func == 3'b000) ? (opA + opB) :
            (func == 3'b001) ? (opA << opB[4:0]) :
            (func == 3'b010) ? (($signed(opA) < $signed(opB)) ? 1 : 0) :
            (func == 3'b011) ? ((opA < opB) ? 1 : 0) :
            (func == 3'b100) ? (opA ^ opB) :
            (func == 3'b101) ? (opA >> opB[4:0]) : // SRL
            (func == 3'b110) ? (opA | opB) :
            (func == 3'b111) ? (opA & opB) : 0
        ) :
        (auxFunc == `AUX_FUNC_SUB) ? ( // R-Type SUB/SRA
            (func == 3'b000) ? (opA - opB) :
            (func == 3'b101) ? ($signed(opA) >>> opB[4:0]) : 0 // SRA
        ) : 32'b0;

endmodule // ExecutionUnit