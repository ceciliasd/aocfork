module riscvpipeline (
    input     clk,
    input     reset,
    output [31:0] PC,
    input  [31:0] Instr,
    output [31:0] Address,  
    output [31:0] WriteData, 
    output        MemWrite,  
    input  [31:0] ReadData);

   /* The 10 "recognizers" for the 10 codeops */
   function isALUreg; input [31:0] I; isALUreg=(I[6:0]==7'b0110011); endfunction
   function isALUimm; input [31:0] I; isALUimm=(I[6:0]==7'b0010011); endfunction
   function isBranch; input [31:0] I; isBranch=(I[6:0]==7'b1100011); endfunction
   function isJALR;   input [31:0] I; isJALR  =(I[6:0]==7'b1100111); endfunction
   function isJAL;    input [31:0] I; isJAL   =(I[6:0]==7'b1101111); endfunction
   function isAUIPC;  input [31:0] I; isAUIPC =(I[6:0]==7'b0010111); endfunction
   function isLUI;    input [31:0] I; isLUI   =(I[6:0]==7'b0110111); endfunction
   function isLoad;   input [31:0] I; isLoad  =(I[6:0]==7'b0000011); endfunction
   function isStore;  input [31:0] I; isStore =(I[6:0]==7'b0100011); endfunction
   function isSYSTEM; input [31:0] I; isSYSTEM=(I[6:0]==7'b1110011); endfunction

   /* Register indices */
   function [4:0] rs1Id; input [31:0] I; rs1Id = I[19:15];      endfunction
   function [4:0] rs2Id; input [31:0] I; rs2Id = I[24:20];      endfunction
   function [4:0] shamt; input [31:0] I; shamt = I[24:20];      endfunction
   function [4:0] rdId;  input [31:0] I; rdId  = I[11:7];       endfunction
   function [1:0] csrId; input [31:0] I; csrId = {I[27],I[21]}; endfunction

   /* funct3 and funct7 */
   function [2:0] funct3; input [31:0] I; funct3 = I[14:12]; endfunction
   function [6:0] funct7; input [31:0] I; funct7 = I[31:25]; endfunction

   /* EBREAK and CSRRS instruction "recognizers" */
   function isEBREAK; input [31:0] I; isEBREAK = (isSYSTEM(I) && funct3(I) == 3'b000); endfunction

   /* The 5 immediate formats */
   function [31:0] Uimm; input [31:0] I; Uimm={I[31:12],{12{1'b0}}}; endfunction
   function [31:0] Iimm; input [31:0] I; Iimm={{21{I[31]}},I[30:20]}; endfunction
   function [31:0] Simm; input [31:0] I; Simm={{21{I[31]}},I[30:25],I[11:7]}; endfunction
   function [31:0] Bimm; input [31:0] I; Bimm = {{20{I[31]}},I[7],I[30:25],I[11:8],1'b0}; endfunction
   function [31:0] Jimm; input [31:0] I; Jimm = {{12{I[31]}},I[19:12],I[20],I[30:21],1'b0}; endfunction

   /* Read/Write tests */
   function writesRd; input [31:0] I; writesRd = !isStore(I) && !isBranch(I); endfunction
   function readsRs1; input [31:0] I; readsRs1 = !(isJAL(I) || isAUIPC(I) || isLUI(I)); endfunction
   function readsRs2; input [31:0] I; readsRs2 = isALUreg(I) || isBranch(I) || isStore(I); endfunction

   // NOP Constant
   localparam NOP = 32'b0000000_00000_00000_000_00000_0110011;

/******** F: Instruction fetch ***********/
   reg [31:0] F_PC;
   reg [31:0] FD_PC;
   reg [31:0] FD_instr;
   reg        FD_nop; // Indicates if FD contains a bubble/nop
   
   assign PC = F_PC;

   /* These signals come from Execute and Decode stages */
   wire [31:0] jumpOrBranchAddress;
   wire        jumpOrBranch;
   wire        stall; // From Hazard Detection Unit

   always @(posedge clk) begin
      if (reset) begin
         F_PC <= 0;
         FD_instr <= NOP;
         FD_PC <= 0;
         FD_nop <= 1;
      end else begin
         // PC Update Logic
         if (jumpOrBranch) begin
            F_PC <= jumpOrBranchAddress; // Flush: Jump taken
         end else if (!stall) begin
            F_PC <= F_PC + 4; // Normal operation
         end
         // Else if stall, PC keeps value

         // Pipeline Register FD Update
         if (jumpOrBranch) begin
             // FLUSH: If branching, current fetch is garbage
             FD_instr <= NOP;
             FD_nop <= 1;
         end else if (!stall) begin
             // Normal: Latch new instruction
             FD_instr <= Instr;
             FD_PC    <= F_PC;
             FD_nop   <= 0;
         end
         // Else if stall, FD keeps value
      end
   end

/******** D: Instruction decode ***********/
   reg [31:0] DE_PC;
   reg [31:0] DE_instr;
   reg [31:0] DE_rs1;
   reg [31:0] DE_rs2;

   /* These signals come from the Writeback stage */
   wire        writeBackEn;
   wire [31:0] writeBackData;
   wire [4:0]  wbRdId;

   reg [31:0] RegisterBank [0:31];

   // --- HAZARD DETECTION UNIT (Load-Use Stall) ---
   // Detects if the instruction in Execute (DE_instr) is a Load
   // and if it writes to a register that the instruction in Decode (FD_instr) needs.
   assign stall = isLoad(DE_instr) && (
                  (readsRs1(FD_instr) && rs1Id(FD_instr) == rdId(DE_instr) && rdId(DE_instr) != 0) ||
                  (readsRs2(FD_instr) && rs2Id(FD_instr) == rdId(DE_instr) && rdId(DE_instr) != 0)
                  );

   // --- REGISTER FILE READ LOGIC (Write-Through / Bypass) ---
   // If writing and reading the same register in the same cycle, return the new value.
   wire [31:0] raw_rs1 = (rs1Id(FD_instr) == 0) ? 0 : 
                         (writeBackEn && (rs1Id(FD_instr) == wbRdId)) ? writeBackData : 
                         RegisterBank[rs1Id(FD_instr)];

   wire [31:0] raw_rs2 = (rs2Id(FD_instr) == 0) ? 0 : 
                         (writeBackEn && (rs2Id(FD_instr) == wbRdId)) ? writeBackData : 
                         RegisterBank[rs2Id(FD_instr)];


   always @(posedge clk) begin
      if (reset || jumpOrBranch || stall || FD_nop) begin
         // Inject Bubble (NOP) if Reset, Flush (Branch), Stall, or previous was NOP
         DE_instr <= NOP;
         DE_PC    <= 0; 
         DE_rs1   <= 0;
         DE_rs2   <= 0;
      end else begin
         DE_PC    <= FD_PC;
         DE_instr <= FD_instr;
         DE_rs1   <= raw_rs1;
         DE_rs2   <= raw_rs2;
      end

      // Writeback happens regardless of stalls in front-end
      if (writeBackEn && wbRdId != 0)
         RegisterBank[wbRdId] <= writeBackData;
   end

/******** E: Execute ***************/
   reg [31:0] EM_PC;
   reg [31:0] EM_instr;
   reg [31:0] EM_rs2;
   reg [31:0] EM_Eresult;
   reg [31:0] EM_addr;

   // Forward declaration for Forwarding Unit logic
   reg [31:0] fwd_op1;
   reg [31:0] fwd_op2;
   
   // --- FORWARDING UNIT ---
   // Checks if previous stages (Memory or Writeback) write to registers used by current ALU
   always @(*) begin
       // Forwarding for Source 1 (RS1)
       if (writesRd(EM_instr) && rdId(EM_instr) != 0 && rdId(EM_instr) == rs1Id(DE_instr))
           fwd_op1 = EM_Eresult; // Forward from Memory Stage (Priority 1)
       else if (writeBackEn && wbRdId != 0 && wbRdId == rs1Id(DE_instr))
           fwd_op1 = writeBackData; // Forward from Writeback Stage (Priority 2)
       else
           fwd_op1 = DE_rs1; // No forwarding

       // Forwarding for Source 2 (RS2)
       if (writesRd(EM_instr) && rdId(EM_instr) != 0 && rdId(EM_instr) == rs2Id(DE_instr))
           fwd_op2 = EM_Eresult; // Forward from Memory Stage (Priority 1)
       else if (writeBackEn && wbRdId != 0 && wbRdId == rs2Id(DE_instr))
           fwd_op2 = writeBackData; // Forward from Writeback Stage (Priority 2)
       else
           fwd_op2 = DE_rs2; // No forwarding
   end


   wire [31:0] E_aluIn1 = fwd_op1;
   wire [31:0] E_aluIn2 = (isALUreg(DE_instr) | isBranch(DE_instr)) ? fwd_op2 : Iimm(DE_instr);
   wire [4:0]  E_shamt  = isALUreg(DE_instr) ? fwd_op2[4:0] : shamt(DE_instr);
   wire E_minus = DE_instr[30] & isALUreg(DE_instr);
   wire E_arith_shift = DE_instr[30];

   // The adder is used by both arithmetic instructions and JALR.
   wire [31:0] E_aluPlus = E_aluIn1 + E_aluIn2;

   // Use a single 33 bits subtract to do subtraction and all comparisons
   wire [32:0] E_aluMinus = {1'b1, ~E_aluIn2} + {1'b0,E_aluIn1} + 33'b1;
   wire        E_LT  = (E_aluIn1[31] ^ E_aluIn2[31]) ? E_aluIn1[31] : E_aluMinus[32];
   wire        E_LTU = E_aluMinus[32];
   wire        E_EQ  = (E_aluMinus[31:0] == 0);

   function [31:0] flip32;
      input [31:0] x;
      flip32 = {x[ 0], x[ 1], x[ 2], x[ 3], x[ 4], x[ 5], x[ 6], x[ 7],
      x[ 8], x[ 9], x[10], x[11], x[12], x[13], x[14], x[15],
      x[16], x[17], x[18], x[19], x[20], x[21], x[22], x[23],
      x[24], x[25], x[26], x[27], x[28], x[29], x[30], x[31]};
   endfunction

   wire [31:0] E_shifter_in = funct3(DE_instr) == 3'b001 ? flip32(E_aluIn1) : E_aluIn1;
   wire [31:0] E_shifter = $signed({E_arith_shift & E_aluIn1[31], E_shifter_in}) >>> E_aluIn2[4:0];
   wire [31:0] E_leftshift = flip32(E_shifter);

   reg [31:0] E_aluOut;
   always @(*) begin
      case(funct3(DE_instr))
         3'b000: E_aluOut = E_minus ? E_aluMinus[31:0] : E_aluPlus;
         3'b001: E_aluOut = E_leftshift;
         3'b010: E_aluOut = {31'b0, E_LT};
         3'b011: E_aluOut = {31'b0, E_LTU};
         3'b100: E_aluOut = E_aluIn1 ^ E_aluIn2;
         3'b101: E_aluOut = E_shifter;
         3'b110: E_aluOut = E_aluIn1 | E_aluIn2;
         3'b111: E_aluOut = E_aluIn1 & E_aluIn2;
      endcase
   end

   /**** Branch, JAL, JALR ************/
   reg E_takeBranch;
   always @(*) begin
      case (funct3(DE_instr))
         3'b000: E_takeBranch = E_EQ;
         3'b001: E_takeBranch = !E_EQ;
         3'b100: E_takeBranch = E_LT;
         3'b101: E_takeBranch = !E_LT;
         3'b110: E_takeBranch = E_LTU;
         3'b111: E_takeBranch = !E_LTU;
         default: E_takeBranch = 1'b0;
      endcase
   end

   wire E_JumpOrBranch = (
          isJAL(DE_instr)  ||
          isJALR(DE_instr) ||
          (isBranch(DE_instr) && E_takeBranch)
   );

   wire [31:0] E_JumpOrBranchAddr =
   isBranch(DE_instr) ? DE_PC + Bimm(DE_instr) :
   isJAL(DE_instr)    ? DE_PC + Jimm(DE_instr) :
   /* JALR */           {E_aluPlus[31:1],1'b0} ;

   wire [31:0] E_result =
   (isJAL(DE_instr) | isJALR(DE_instr)) ? DE_PC+4                :
   isLUI(DE_instr)                      ? Uimm(DE_instr)         :
   isAUIPC(DE_instr)                    ? DE_PC + Uimm(DE_instr) :
                                          E_aluOut               ;

   always @(posedge clk) begin
      // If we are flushing (branch taken), subsequent stages (M) process a NOP
      // However, usually we handle flush at the input of the pipeline registers (F, D).
      // The instruction currently in E is valid (it caused the branch), so it moves to M normally.
      EM_PC      <= DE_PC;
      EM_instr   <= DE_instr;
      EM_rs2     <= fwd_op2; // Note: Use forwarded RS2 for Store instructions!
      EM_Eresult <= E_result;
      EM_addr    <= isStore(DE_instr) ? fwd_op1 + Simm(DE_instr) : // Use forwarded RS1 for Store address
                                        fwd_op1 + Iimm(DE_instr) ;
   end

/******** M: Memory ***************/
   reg [31:0] MW_PC;
   reg [31:0] MW_instr;
   reg [31:0] MW_Eresult;
   reg [31:0] MW_addr;
   reg [31:0] MW_Mdata;

   // halt logic needs reset check
   assign halt = !reset & isEBREAK(MW_instr);

   /***** STORE **********/
   assign Address   = EM_addr;
   assign MemWrite  = isStore(EM_instr);
   assign WriteData = EM_rs2; 

   always @(posedge clk) begin
      MW_PC      <= EM_PC;
      MW_instr   <= EM_instr;
      MW_Eresult <= EM_Eresult;
      MW_Mdata   <= ReadData;
      MW_addr    <= EM_addr;
   end

/******** W: WriteBack **************/

   /***** LOAD **********/
   assign writeBackData = isLoad(MW_instr) ? MW_Mdata : MW_Eresult;
   assign writeBackEn = writesRd(MW_instr) && rdId(MW_instr) != 0;
   assign wbRdId = rdId(MW_instr);

   // These connect back to Fetch stage
   assign jumpOrBranchAddress = E_JumpOrBranchAddr;
   assign jumpOrBranch        = E_JumpOrBranch;

/**************************/

   always @(posedge clk) begin
      if (halt) begin
         $display("Execution finished at PC = %h", MW_PC);
         $writememh("regs.out", RegisterBank);
         $finish();
      end
   end
endmodule