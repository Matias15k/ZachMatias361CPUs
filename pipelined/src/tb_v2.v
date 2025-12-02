// Testbench for Northwestern - CompEng 361 - Lab4
`define CHAR_WIDTH 8
`define MAX_CHAR 80

module tb_v2;
    reg clk, rst;
    reg exit;
    wire halt;
    reg [`CHAR_WIDTH*`MAX_CHAR-1:0] mem_in_fname, mem_out_fname, regs_in_fname, regs_out_fname;
    reg [`CHAR_WIDTH*`MAX_CHAR-1:0] signal_dump_fname;

    // Pipelined CPU instantiation
    PipelinedCPU CPU (halt, clk, rst);

    // Clock Period = 10 time units
    always #5 clk = ~clk;

    always @(negedge clk)
        if (halt)
            exit = 1;

    integer cycle;

    // ---------- DEBUG PRINT EACH CYCLE ----------
    // always @(posedge clk) begin
    //     if (!rst) begin
    //         cycle <= 0;
    //     end else begin
    //         cycle <= cycle + 1;

    //         $display("\n=== CYCLE %3d  t=%0t ===", cycle, $time);

    //         // One-line summary of PCs / IRs
    //         $display("IF: PC=%08x IR=%08x  |  ID: PC=%08x IR=%08x  |  EX: PC=%08x  |  MEM: addr=%08x  |  WB: rd=%2d data=%08x",
    //                 CPU.PC,
    //                 CPU.InstWord,
    //                 CPU.ID_PC,
    //                 CPU.ID_IR,
    //                 CPU.IDEX_PC,
    //                 CPU.DataAddr,
    //                 CPU.MEMWB_rd,
    //                 CPU.RWrdata_WB);

    //         // IF/ID
    //         $display("IFID : PC=%08x IR=%08x  flush=%b  WE=%b",
    //                 CPU.IFID_PC,
    //                 CPU.IFID_IR,
    //                 CPU.IFID_flush,
    //                 CPU.IFID_WE);

    //         // ID/EX key fields
    //         $display("ID/EX: PC=%08x rs1=%2d rs2=%2d rd=%2d op=%02b f3=%1b f7=%02b  imm_i=%08x imm_u=%08x",
    //                 CPU.IDEX_PC,
    //                 CPU.IDEX_rs1,
    //                 CPU.IDEX_rs2,
    //                 CPU.IDEX_rd,
    //                 CPU.IDEX_opcode,
    //                 CPU.IDEX_funct3,
    //                 CPU.IDEX_funct7,
    //                 CPU.IDEX_imm_i,
    //                 CPU.IDEX_imm_u);

    //         // EX
    //         $display("EX   : opA=%08x opB=%08x EU_out=%08x EX_result=%08x  br_taken=%b PC_tgt=%08x",
    //                 CPU.EX_opA,
    //                 CPU.EX_opB_raw,
    //                 CPU.EX_eu_out,
    //                 CPU.EX_result,
    //                 CPU.EX_branch_taken,
    //                 CPU.EX_PC_target);

    //         $display("       RegW_EX=%b MemR_EX=%b MemW_EX=%b MemToReg_EX=%b IsBr_EX=%b IsJal_EX=%b IsJalr_EX=%b",
    //                 CPU.RegWrite_EX,
    //                 CPU.MemRead_EX,
    //                 CPU.MemWrite_EX,
    //                 CPU.MemToReg_EX,
    //                 CPU.IsBranch_EX,
    //                 CPU.IsJal_EX,
    //                 CPU.IsJalr_EX);

    //         // EX/MEM
    //         $display("EX/MEM: ALU_out=%08x store=%08x addr=%08x rd=%2d  RegW_MEM=%b MemR_MEM=%b MemW_MEM=%b Size=%02b",
    //                 CPU.EXMEM_ALU_out,
    //                 CPU.EXMEM_store_data,
    //                 CPU.EXMEM_addr,
    //                 CPU.EXMEM_rd,
    //                 CPU.RegWrite_MEM,
    //                 CPU.MemRead_MEM,
    //                 CPU.MemWrite_MEM,
    //                 CPU.EXMEM_Size);

    //         // MEM
    //         $display("MEM  : DataAddr=%08x StoreData=%08x DataWord=%08x MemWrEn=%b MemSize=%02b align_err=%b",
    //                 CPU.DataAddr,
    //                 CPU.StoreData,
    //                 CPU.DataWord,
    //                 CPU.MemWrEn,
    //                 CPU.MemSize,
    //                 CPU.memory_alignment_error_MEM);

    //         // MEM/WB
    //         $display("MEM/WB: ALU_out=%08x DataWord=%08x addr=%08x rd=%2d RegW_WB=%b MemToReg_WB=%b f3=%1d",
    //                 CPU.MEMWB_ALU_out,
    //                 CPU.MEMWB_DataWord,
    //                 CPU.MEMWB_addr,
    //                 CPU.MEMWB_rd,
    //                 CPU.RegWrite_WB,
    //                 CPU.MemToReg_WB,
    //                 CPU.MEMWB_funct3);

    //         // WB
    //         $display("WB   : RWrEn_WB=%b rd_WB=%2d RWrdata_WB=%08x",
    //                 CPU.RWrEn_WB,
    //                 CPU.rd_WB,
    //                 CPU.RWrdata_WB);

    //         // Hazards / global
    //         $display("CTRL : load_use=%b stall_EX=%b EX_busy=%2d redirect=%b  halt=%b exit=%b",
    //                 CPU.load_use_hazard,
    //                 CPU.stall_EX,
    //                 CPU.EX_busy,
    //                 CPU.EX_do_redirect,
    //                 halt,
    //                 exit);
    //     end
    //end
        always @(posedge clk) begin
        if (rst) cycle = cycle + 1;

        $display("\n=== CYCLE %3d  t=%0t ===", cycle, $time);

        // Top summary line with stage separators
        $display("IF:  PC=%08x IR=%08x  |  ID: PC=%08x IR=%08x  |  EX: PC=%08x  |  MEM: addr=%08x  |  WB: rd=%2d data=%08x",
                 CPU.PC, CPU.InstWord,
                 CPU.IFID_PC, CPU.IFID_IR,
                 CPU.IDEX_PC,
                 CPU.EXMEM_addr,
                 CPU.MEMWB_rd, CPU.RWrdata_WB);

        // IF/ID
        $display("IFID  : PC=%08x IR=%08x  flush=%b  WE=%b",
                 CPU.IFID_PC, CPU.IFID_IR,
                 CPU.IFID_flush, CPU.IFID_WE);

        // ID-stage control word (decoded)
        $display("ID    : op=%02b rs1=%2d rs2=%2d rd=%2d f3=%0b f7=%02b",
                 CPU.opcode, CPU.Rsrc1, CPU.Rsrc2, CPU.Rdst,
                 CPU.funct3, CPU.funct7);
        $display("ID_ctl: RegW=%b MemR=%b MemW=%b MemToReg=%b Br=%b Jal=%b Jalr=%b Size=%02b f3=%0b",
                 CPU.RegWrite_ID, CPU.MemRead_ID, CPU.MemWrite_ID, CPU.MemToReg_ID,
                 CPU.IsBranch_ID, CPU.IsJal_ID, CPU.IsJalr_ID,
                 CPU.Size_ID, CPU.BranchFunct3_ID);

        // ID/EX pipeline regs + control bus
        $display("ID/EX : PC=%08x rs1=%2d rs2=%2d rd=%2d op=%02b f3=%0b f7=%02b  imm_i=%08x imm_u=%08x",
                 CPU.IDEX_PC, CPU.IDEX_rs1, CPU.IDEX_rs2, CPU.IDEX_rd,
                 CPU.IDEX_opcode, CPU.IDEX_funct3, CPU.IDEX_funct7,
                 CPU.IDEX_imm_i, CPU.IDEX_imm_u);
        $display("IDEX_ctl: %b", CPU.IDEX_ctrl_out);

        // EX stage + control
        $display("EX    : opA=%08x opB=%08x EU_out=%08x EX_result=%08x  br_taken=%b PC_tgt=%08x",
                 CPU.EX_opA, CPU.EX_opB_raw, CPU.EX_eu_out, CPU.EX_result,
                 CPU.EX_branch_taken, CPU.EX_PC_target);
        $display("EX_ctl: RegW=%b MemR=%b MemW=%b MemToReg=%b Br=%b Jal=%b Jalr=%b Size=%02b f3=%0b",
                 CPU.RegWrite_EX, CPU.MemRead_EX, CPU.MemWrite_EX, CPU.MemToReg_EX,
                 CPU.IsBranch_EX, CPU.IsJal_EX, CPU.IsJalr_EX,
                 CPU.Size_EX, CPU.BranchFunct3_EX);

        // EX/MEM regs + control bus
        $display("EX/MEM: ALU_out=%08x store=%08x addr=%08x rd=%2d",
                 CPU.EXMEM_ALU_out, CPU.EXMEM_store_data, CPU.EXMEM_addr, CPU.EXMEM_rd);
        $display("EXMEM_ctl: %b", CPU.EXMEM_ctrl_out);
        $display("MEM_ctl: RegW=%b MemR=%b MemW=%b MemToReg=%b Jal=%b Jalr=%b Size=%02b f3=%0b",
                 CPU.RegWrite_MEM, CPU.MemRead_MEM, CPU.MemWrite_MEM, CPU.MemToReg_MEM,
                 CPU.IsJal_MEM, CPU.IsJalr_MEM,
                 CPU.EXMEM_Size, CPU.EXMEM_funct3);

        // MEM stage
        $display("MEM   : DataAddr=%08x StoreData=%08x DataWord=%08x MemWrEn=%b MemSize=%02b align_err=%b",
                 CPU.DataAddr, CPU.StoreData, CPU.DataWord,
                 CPU.MemWrEn, CPU.MemSize, CPU.memory_alignment_error_MEM);

        // MEM/WB regs + control
        $display("MEM/WB: ALU_out=%08x DataWord=%08x addr=%08x rd=%2d",
                 CPU.MEMWB_ALU_out, CPU.MEMWB_DataWord, CPU.MEMWB_addr, CPU.MEMWB_rd);
        $display("MEMWB_ctl: %b", CPU.MEMWB_ctrl_out);
        $display("WB_ctl: RegW=%b MemToReg=%b Jal=%b Jalr=%b f3=%0b",
                 CPU.RegWrite_WB, CPU.MemToReg_WB, CPU.IsJal_WB, CPU.IsJalr_WB,
                 CPU.MEMWB_funct3);

        // WB stage + global
        $display("WB    : RWrEn_WB=%b rd_WB=%2d RWrdata_WB=%08x",
                 CPU.RWrEn_WB, CPU.rd_WB, CPU.RWrdata_WB);
        $display("CTRL  : load_use=%b stall_EX=%b EX_busy=%2d redirect=%b  halt=%b exit=%b",
                 CPU.load_use_hazard, CPU.stall_EX, CPU.EX_busy, CPU.EX_do_redirect,
                 halt, exit);


        $display("SR_control(ID)=%b  ->  IDEX_SR_control=%b  -> used in EU=%b",
        CPU.SR_control, CPU.IDEX_SR_control, CPU.IDEX_SR_control);
    end

    // ---------- END DEBUG PRINT ----------

    initial begin
        cycle = 0;
        // Read commandline options
        if (!$value$plusargs("MEM_IN=%s", mem_in_fname))
            mem_in_fname = "mem_in_pipelined.hex";
        if (!$value$plusargs("REGS_IN=%s", regs_in_fname))
            regs_in_fname = "regs_in_pipelined.hex";
        if (!$value$plusargs("REGS_OUT=%s", regs_out_fname))
            regs_out_fname = "regs_out_pipelined.hex";
        if (!$value$plusargs("MEM_OUT=%s", mem_out_fname))
            mem_out_fname = "mem_out_pipelined.hex";
        if (!$value$plusargs("DUMP=%s", signal_dump_fname))
            signal_dump_fname = "outputs/pipelined.vcd";

        // Clock and reset setup
        #0 rst = 0; exit = 0; clk = 0;
        #0 rst = 1;

        // Load program memory and regs
        #0 $readmemh(mem_in_fname, CPU.MEM.Mem);
        #0 $readmemh(regs_in_fname, CPU.RF.Mem);

        // Dumpfile
        $dumpfile(signal_dump_fname);
        $dumpvars();

        // Optional: you can comment this out now, since we added the big display block
        // #0 $monitor($time,, "PC=%08x IR=%08x halt=%x exit=%x", CPU.PC, CPU.InstWord, halt, exit);

        // Exit
        wait(exit);

        // Dump memory and regs 
        #0 $writememh(regs_out_fname, CPU.RF.Mem);
        #0 $writememh(mem_out_fname, CPU.MEM.Mem);
        
        $finish;      
   end

    initial begin
        integer timeout_cycles = 5000;
        repeat (timeout_cycles) @(posedge clk);
        $display("TIMEOUT: Simulation took too long. Halting...");
        $finish;
    end
endmodule


module Mem(InstAddr, InstOut,
         DataAddr, DataSize, DataIn, DataOut, WE, CLK);
    input [31:0] InstAddr, DataAddr;
    input [1:0] 	DataSize;   
    input [31:0] DataIn;   
    output [31:0] InstOut, DataOut;  
    input      WE, CLK;
    reg [7:0] 	Mem[0:1024];

    wire [31:0] 	DataAddrH, DataAddrW, InstAddrW;

    // Instruction Addresses are word aligned
    assign InstAddrW = InstAddr & 32'hfffffffc;
   
    assign DataAddrH = DataAddr & 32'hfffffffe;
    assign DataAddrW = DataAddr & 32'hfffffffc;

    // Little endian
    assign InstOut = {Mem[InstAddrW+3], Mem[InstAddrW+2], 
		Mem[InstAddrW+1], Mem[InstAddrW]};

    // Little endian
    assign DataOut = (DataSize == 2'b00) ? {4{Mem[DataAddr]}} :
	       ((DataSize == 2'b01) ? {2{Mem[DataAddrH+1],Mem[DataAddrH]}} :
		{Mem[DataAddrW+3], Mem[DataAddrW+2], Mem[DataAddrW+1], Mem[DataAddrW]});
   
     always @ (posedge CLK)
        if (WE) begin
	        case (DataSize)
            2'b00: begin // Write byte
                Mem[DataAddr] <= DataIn[7:0];
            end
            2'b01: begin  // Write halfword
                Mem[DataAddrH] <= DataIn[7:0];
                Mem[DataAddrH+1] <= DataIn[15:8];
            end
            2'b10, 2'b11: begin // Write word
                Mem[DataAddrW] <= DataIn[7:0];
                Mem[DataAddrW+1] <= DataIn[15:8];
                Mem[DataAddrW+2] <= DataIn[23:16];
                Mem[DataAddrW+3] <= DataIn[31:24];
            end
        endcase // case (Size)
     end

endmodule // Mem

module RegFile(AddrA, DataOutA,
	       AddrB, DataOutB,
	       AddrW, DataInW, WenW, CLK);
   input [4:0] AddrA, AddrB, AddrW;
   output [31:0] DataOutA, DataOutB;  
   input [31:0]  DataInW;
   input 	 WenW, CLK;
   reg [31:0] 	 Mem[0:31];
   
   assign DataOutA = (AddrA == 0) ? 32'h00000000 : Mem[AddrA];
   assign DataOutB = (AddrB == 0) ? 32'h00000000 : Mem[AddrB]; 

   always @ (posedge CLK) begin
     if (WenW) begin
       Mem[AddrW] <= DataInW;
     end
      Mem[0] <= 0; // Enforce the invariant that x0 = 0
   end
   
endmodule // RegFile


module Reg(Din, Qout, WE, CLK, RST);
   parameter width = 32;
   parameter init = 0;
   input [width-1:0] Din;
   output [width-1:0] Qout;
   input 	      WE, CLK, RST;

   reg [width-1:0]    Qout;
   
   always @ (posedge CLK or negedge RST)
     if (!RST)
       Qout <= init;
     else
       if (WE)
	     Qout <= Din;
  
endmodule // Reg
