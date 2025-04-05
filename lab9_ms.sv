module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;

  // instantiate device to be tested
  top dut(clk, reset, WriteData, DataAdr, MemWrite);
  
  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(MemWrite) begin
        if(DataAdr === 100 & WriteData === 409625) begin
          $display("Simulation succeeded");
          $stop;
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule



module lab9_ms(input logic clk, reset,
			  output logic [31:0] WriteDataM, DataAdrM,
			  output logic MemWriteM);
	top t(clk, reset, WriteDataM, DataAdrM, MemWriteM);

endmodule

module top(input logic clk, reset,
			  output logic [31:0] WriteDataM, DataAdrM,
			  output logic MemWriteM);
	logic [31:0] PCF, InstrF, ReadDataM;
	// instantiate processor and memories
	riscv riscv(clk, reset, PCF, InstrF, MemWriteM, DataAdrM,
	WriteDataM, ReadDataM);
	imem imem(PCF, InstrF);
	dmem dmem(clk, MemWriteM, DataAdrM, WriteDataM, ReadDataM);
endmodule


module riscv(input logic clk, reset, // what is this variable order. kill me
				 output logic [31:0] PCF,
				 input logic [31:0] InstrF,
				 output logic MemWriteM,
				 output logic [31:0] DataAdrM, WriteDataM,
				 input logic [31:0] ReadDataM);
	
	// Fetch
	logic [31:0] PCFprime, PCPlus4F;
	
	// Decode
	logic RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD;
	logic [1:0] ResultSrcD;
	logic [2:0] ImmSrcD, ALUControlD;
	logic [31:0] RD1D, RD2D, InstrD, PCD, PCPlus4D, ImmExtD;
	
	// Execute
	logic PCSrcE, ZeroE, RegWriteE, MemWriteE, JumpE, BranchE, ALUSrcE;
	logic [1:0] ResultSrcE;
	logic [2:0] ALUControlE;
	logic [4:0] RS1E, RS2E, RdE;
	logic [31:0] RD1E, RD2E, PCE, ImmExtE, PCPlus4E, PCTargetE, SrcAE, SrcBE, ALUResultE, WriteDataE;
	
	// Memory
	logic RegWriteM;
	logic [1:0] ResultSrcM;
	logic [4:0] RdM;
	logic [31:0] ALUResultM, PCPlus4M;
	
	// Write
	logic RegWriteW;
	logic [1:0] ResultSrcW;
	logic [4:0] RdW;
	logic [31:0] ALUResultW, ReadDataW, PCPlus4W, ResultW;
	
	
	// Hazard Unit
	logic StallF, StallD, FlushD, FlushE;
	logic [1:0] ForwardAE, ForwardBE;
	
	
	
	// Fetch
	mux2 #(32) PCFprimeMux(PCPlus4F, PCTargetE, PCSrcE, PCFprime);
	flopr #(32) PCFreg(clk, reset, PCFprime, ~StallF, PCF);
			// instruction memory outside module. Otherwise would be imem(PCF, InstrF)
	assign PCPlus4F = PCF+4;
	// end Fetch
	
	flopr #(32+32+32) DecodeReg(clk, reset, FlushD?96'b0:{InstrF, PCF, PCPlus4F}, FlushD|~StallD, {InstrD, PCD, PCPlus4D});
	
	// Decode
	controller cu(InstrD[6:0], InstrD[14:12], InstrD[30], RegWriteD, ResultSrcD, MemWriteD, JumpD, BranchD, ALUControlD, ALUSrcD, ImmSrcD);
	regfile rf(~clk, RegWriteW, InstrD[19:15], InstrD[24:20], RdW, ResultW, RD1D, RD2D);
	extend ext(InstrD[31:7], ImmSrcD, ImmExtD);
	// end Decode
	
	flopr #(10+32+32+32+5+5+5+32+32) ExecuteReg(clk, reset, FlushE?175'b0:{RegWriteD, ResultSrcD, MemWriteD, JumpD, BranchD, ALUControlD, ALUSrcD, RD1D, RD2D, PCD, InstrD[19:15], InstrD[24:20], InstrD[11:7], ImmExtD, PCPlus4D}, 1'b1, {RegWriteE, ResultSrcE, MemWriteE, JumpE, BranchE, ALUControlE, ALUSrcE, RD1E, RD2E, PCE, RS1E, RS2E, RdE, ImmExtE, PCPlus4E});
	
	// Execute
	assign PCSrcE = JumpE|(BranchE&ZeroE);
	mux3 #(32) SrcAEMux(RD1E, ResultW, ALUResultM, ForwardAE, SrcAE);
	mux3 #(32) WriteDataEMux(RD2E, ResultW, ALUResultM, ForwardBE, WriteDataE);
	mux2 #(32) SrcBEMux(WriteDataE, ImmExtE, ALUSrcE, SrcBE);
	assign PCTargetE = PCE+ImmExtE;
	alu mainalu(SrcAE, SrcBE, ALUControlE, ALUResultE, ZeroE);
	// end Execute
	
	flopr #(4+32+32+5+32) MemoryReg(clk, reset, {RegWriteE, ResultSrcE, MemWriteE, ALUResultE, WriteDataE, RdE, PCPlus4E}, 1'b1, {RegWriteM, ResultSrcM, MemWriteM, ALUResultM, WriteDataM, RdM, PCPlus4M});
	
	// Memory
	assign DataAdrM = ALUResultM;
	// end Memory
	
	flopr #(1+2+32+32+5+32) WriteReg(clk, reset, {RegWriteM, ResultSrcM, ALUResultM, ReadDataM, RdM, PCPlus4M}, 1'b1, {RegWriteW, ResultSrcW, ALUResultW, ReadDataW, RdW, PCPlus4W});
	
	// Write
	mux3 #(32) ResultWMux(ALUResultW, ReadDataW, PCPlus4W, ResultSrcW, ResultW);
	// end Write
	
	
	
	
	// Hazard Unit	
	hazardunit hu(InstrD[19:15], InstrD[24:20], RdE, RS2E, RS1E, RdM, RdW, PCSrcE, ResultSrcE[0], RegWriteM, RegWriteW, StallF, StallD, FlushD, FlushE, ForwardAE, ForwardBE);
	
endmodule


/***********************
DATAPATH SPECIFIC COMPONENTS
- regfile
- extend
- alu
- controller
- maindec
- aludec
- HazardUnit
***********************/

module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0

  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule


module extend(input  logic [31:7] instr,
              input  logic [2:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
               // I-type 
      3'b000:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      3'b001:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
               // B-type (branches)
      3'b010:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
               // J-type (jal)
      3'b011:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
               // U-type (lui)
      3'b100:   immext = {instr[31:12], 12'b0};
      default: immext = 32'bx; // undefined
    endcase             
endmodule

module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];

  always_comb
    case (alucontrol)
      3'b000:  result = sum;                 // add
      3'b001:  result = sum;                 // subtract
      3'b010:  result = a & b;               // and
      3'b011:  result = a | b;		         // or
      3'b100:  result = b;		         // pass b lmao
      3'b101:  result = sum[31];				   // slt
      3'b110:  result = a << b;		         // sll
      3'b111:  result = a >> b;              // srl
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
  
endmodule

module controller(input  logic [6:0] op,
                  input  logic [2:0] funct3,
                  input  logic       funct7b5,
                  output logic       RegWrite,
                  output logic [1:0] ResultSrc,
                  output logic       MemWrite, Jump, Branch,
                  output logic [2:0] ALUControl,
                  output logic       ALUSrc,
                  output logic [2:0] ImmSrc);

  logic [1:0] ALUOp;

  maindec md(op, ResultSrc, MemWrite, Branch,
             ALUSrc, RegWrite, Jump, ImmSrc, ALUOp);
  aludec  ad(op[5], funct3, funct7b5, ALUOp, ALUControl);
  
endmodule

module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrc,
               output logic       MemWrite,
               output logic       Branch, ALUSrc,
               output logic       RegWrite, Jump,
               output logic [2:0] ImmSrc,
               output logic [1:0] ALUOp);

  logic [11:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 12'b1_000_1_0_01_0_00_0; // lw
		/////////////////////////////////////////////////
      // Write more operators here                   //
		7'b0100011: controls = 12'b0_001_1_1_00_0_00_0; // sw
      7'b0110011: controls = 12'b1_000_0_0_00_0_10_0; // R-type 
      7'b1100011: controls = 12'b0_010_0_0_00_1_01_0; // B-type
      7'b0010011: controls = 12'b1_000_1_0_00_0_10_0; // I-type ALU
      7'b1101111: controls = 12'b1_011_0_0_10_0_00_1; // jal
      7'b0110111: controls = 12'b1_100_1_0_00_0_11_0; // lui
      /////////////////////////////////////////////////
      default:    controls = 12'b0_000_0_0_00_0_00_0; // non-implemented instruction
    endcase
endmodule

module aludec(input logic opb5,
				  input logic [2:0] funct3,
				  input logic funct7b5,
				  input logic [1:0] ALUOp,
				  output logic [2:0] ALUControl);
	logic RtypeSub;
	assign RtypeSub = funct7b5 & opb5; // TRUE for R-type subtract instruction
	always_comb
		case(ALUOp)
			2'b00: ALUControl = 3'b000; // addition
			2'b01: ALUControl = 3'b001; // subtraction
			2'b11: ALUControl = 3'b100; // pass b
			default: case(funct3) // R-type or I-type ALU
				3'b000: if (RtypeSub)
						ALUControl = 3'b001; // sub
					else
						ALUControl = 3'b000; // add, addi
				3'b010: ALUControl = 3'b101; // slt, slti
				3'b110: ALUControl = 3'b011; // or, ori
				3'b111: ALUControl = 3'b010; // and, andi
				default: ALUControl = 3'b000; // ???
			endcase
		endcase
endmodule

module hazardunit(input logic [4:0] Rs1D, Rs2D, RdE, Rs2E, Rs1E, RdM, RdW,
						input logic PCSrcE, ResultSrcE0, RegWriteM, RegWriteW,
						output logic StallF, StallD, FlushD, FlushE, 
						output logic [1:0] ForwardAE, ForwardBE);
	// a
	assign ForwardAE = (((Rs1E == RdM)&&RegWriteM)&&(Rs1E!=5'b0))?2'b10:
							 (((Rs1E == RdW)&&RegWriteW)&&(Rs1E!=5'b0))?2'b01:
																					  2'b00;
	assign ForwardBE = (((Rs2E == RdM)&&RegWriteM)&&(Rs2E!=5'b0))?2'b10:
							 (((Rs2E == RdW)&&RegWriteW)&&(Rs2E!=5'b0))?2'b01:
																					  2'b00;
	logic lwStall;
	assign lwStall = ((Rs1D == RdE)||(Rs2D == RdE))&&ResultSrcE0;
	assign {StallF, StallD} = {lwStall, lwStall};
	assign FlushD = PCSrcE;
	assign FlushE = lwStall || PCSrcE;
endmodule

/***********************
BASIC COMPONENTS
- register
- 2 input mux
- 3 input mux
***********************/
module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset,
               input  logic [WIDTH-1:0] d,
					input logic enable,
               output logic [WIDTH-1:0] q);
	
	logic [WIDTH-1:0] qNext;
	assign qNext = enable?d:q;
	always_ff @(posedge clk, posedge reset)
		if (reset) q <= 0;
		else       q <= qNext;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

/***********************
MEMORY COMPONENTS
- imem
- dmem
***********************/
module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned
endmodule

module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

