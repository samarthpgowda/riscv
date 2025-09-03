`timescale 1ns / 1ps
/////////////////////////////////////////////////////////////////////////////////
// Engineer: Samarth.P
// 
// Create Date: 28.08.2025 11:24:34
// Design Name: Risc-v processor (I-type only) 
// Module Name: top
module program_counter(
    input clk, reset,
    input [31:0] pc_in,
    output reg [31:0] pc_out
);
    always @(posedge clk or posedge reset) begin
        if (reset)
            pc_out <= 32'b0;
        else
            pc_out <= pc_in;
    end
endmodule

// adder
module adderforpc(input [31:0] frompc, output [31:0] nxtpc);
    assign nxtpc = frompc + 4;
endmodule

// instruction memory 
module instruction_mem(
    input clk,
    input reset,
    input [31:0] rd_add,
    output reg [31:0] ins_out
);
    reg [31:0] imem[63:0];

    always @(posedge clk) begin
        ins_out <= imem[rd_add[7:2]]; 
    end

    integer i;
    always @(posedge reset) begin
        for (i=0; i<64; i=i+1)
            imem[i] <= 32'b0;
        imem[0] <= 32'h00500093; // ADDI x1, x0, 5
        imem[1] <= 32'h00a00113; // ADDI x2, x0, 10
        imem[2] <= 32'h002081b3; // ADD  x3, x1, x2
        imem[3] <= 32'h0020f233; // AND  x4, x1, x2
        imem[4] <= 32'h0020e2b3; // OR   x5, x1, x2
        imem[5] <= 32'h0000A303; // LW   x6, 0(x1)  
        imem[6] <= 32'h0060A223; // SW   x6, 4(x1)  
        imem[7] <= 32'h00000013; // NOP
    end
endmodule

// register file 
module reg_file(
    input clk,
    input reset,
    input reg_write,
    input [4:0] rs1, rs2, rd,
    input [31:0] wr_data,
    output [31:0] rd_data1,
    output [31:0] rd_data2
);
    reg [31:0] regs[0:31];
    integer i;

    assign rd_data1 = regs[rs1];
    assign rd_data2 = regs[rs2];

    always @(posedge clk) begin
        if (reset) begin
            for (i=0; i<32; i=i+1) regs[i] <= 0;
        end
        else if (reg_write && rd != 0) begin
            regs[rd] <= wr_data;
        end
    end
endmodule

// immediate generator
module imm_gen(
    input [6:0] opcode,
    input [31:0] ins,
    output reg [31:0] imm_op
);
    // Opcodes
    localparam OPC_LOAD = 7'b0000011; // lw
    localparam OPC_OPIMM= 7'b0010011; // I-type ALU
    localparam OPC_STORE= 7'b0100011; // sw

    always @(*) begin
        case (opcode)
            OPC_LOAD, OPC_OPIMM: begin
                imm_op = {{20{ins[31]}}, ins[31:20]};
            end
            OPC_STORE: begin
                imm_op = {{20{ins[31]}}, ins[31:25], ins[11:7]};
            end
            default: imm_op = 32'b0;
        endcase
    end
endmodule

// control unit 
module con_unit(
    input [6:0] opcode,
    input [2:0] funct3,
    output reg branch,
    output reg reg_wr,
    output reg alusrc,
    output reg mem_rd,
    output reg mem_wr,
    output reg memtoreg,
    output reg [1:0] aluop
);
    always @(*) begin
        branch   = 1'b0;
        reg_wr   = 1'b0;
        alusrc   = 1'b0;
        mem_rd   = 1'b0;
        mem_wr   = 1'b0;
        memtoreg = 1'b0;
        aluop    = 2'b00;

        case (opcode)
            7'b0110011: begin // R-type (ADD, AND, OR)
                alusrc   = 1'b0;
                reg_wr   = 1'b1;
                memtoreg = 1'b0;
                aluop    = 2'b10;
            end
            7'b0010011: begin // I-type ALU 
                alusrc   = 1'b1;
                reg_wr   = 1'b1;
                memtoreg = 1'b0;
                aluop    = 2'b10;
            end
            7'b0000011: begin // LW 
                alusrc   = 1'b1;
                reg_wr   = 1'b1;
                memtoreg = 1'b1;
                mem_rd   = 1'b1;
                aluop    = 2'b00;
            end
            7'b0100011: begin // SW 
                alusrc   = 1'b1;
                reg_wr   = 1'b0;
                mem_wr   = 1'b1;
                aluop    = 2'b00;                
            end
            default: begin
            end
        endcase
    end
endmodule

// ALU unit 
module alu_unit(
    input [31:0] a, b,
    input [3:0] control_in,
    output reg zero,
    output reg [31:0] alu_result
);
    always @(*) begin
        case (control_in)
            4'b0000: alu_result = a & b;   // AND
            4'b0001: alu_result = a | b;   // OR
            4'b0010: alu_result = a + b;   // ADD
            4'b0011: alu_result = a ^ b;   // XOR
            4'b0110: alu_result = a - b;   // SUB
            default: alu_result = a + b;   // Default to ADD
        endcase
        zero = (alu_result == 32'b0);
    end
endmodule

// ALU control
module alu_control(
    input [1:0] aluop,
    input fun7,
    input [2:0] fun3,
    output reg [3:0] control_out
);
    always @(*) begin
        case (aluop)
            2'b00: control_out = 4'b0010;  
            2'b10: begin
                if (fun3 == 3'b000) begin
                    control_out = 4'b0010; // ADD
                end else begin
                    case (fun3)
                        3'b111: control_out = 4'b0000; // AND/ANDI
                        3'b110: control_out = 4'b0001; // OR/ORI
                        3'b100: control_out = 4'b0011; // XOR/XORI
                        default: control_out = 4'b0010; // Default to ADD
                    endcase
                end
            end
            default: control_out = 4'b0010; // Default to ADD
        endcase
    end
endmodule

// data memory
module data_memory (
    input         clk,
    input         reset,
    input  [31:0] addr,// Address from ALU
    input  [31:0] write_data, // Data to write
    input         mem_rd,// Enable read
    input         mem_wr,// Enable write
    output reg [31:0] read_data // Data output
);

    reg [31:0] mem [0:63]; 
    integer i;
    always @(posedge reset) begin
        if (reset) begin
            for (i = 0; i < 64; i = i + 1)
                mem[i] <= 32'b0;
            mem[0] <= 32'h12345678;  
            mem[1] <= 32'hABCDEF00;  
            mem[2] <= 32'h11111111;  
        end
    end

    // Write operation
    always @(posedge clk) begin
        if (!reset && mem_wr) begin
            mem[addr[7:2]] <= write_data;
        end
    end

    // Read operation
    always @(*) begin
        if (mem_rd)
            read_data = mem[addr[7:2]];  
        else
            read_data = 32'b0;
    end

endmodule

// all mux
module mux1(input sel1, input [31:0] a1, b1, output [31:0] y1);
    assign y1 = (sel1 == 1'b0) ? a1 : b1;
endmodule
module mux2(input sel2, input [31:0] a2, b2, output [31:0] y2);
    assign y2 = (sel2 == 1'b0) ? a2 : b2;
endmodule
module mux3(input sel3, input [31:0] a3, b3, output [31:0] y3);
    assign y3 = (sel3 == 1'b0) ? a3 : b3;
endmodule

// adder
module riscv_adders(input [31:0] in1, in2, output [31:0] sum);
    assign sum = in1 + in2;
endmodule

// and gate
module and_logic(input branch, zero, output and_out);
    assign and_out = branch & zero;
endmodule

// top module 
module top(
    input clk,
    input reset,
    output [31:0] pc,
    output [31:0] instruction,
    output [31:0] alu_out,
    output [31:0] reg1_data,
    output [31:0] reg2_data,
    output [31:0] data_memory_out
);

    // Internal wires
    wire [31:0] pc_next, pc_in, mem_out;
    wire [31:0] instr;
    wire [31:0] rd_data1, rd_data2;
    wire [31:0] imm_ext, alu_src_b, alu_result;
    wire [31:0] sum_branch, wr_back;
    wire [3:0] alu_control_signal;
    wire [1:0] alu_op;
    wire reg_wr, alusrc, zero, branch, memtoreg, mem_wr, mem_rd, pc_sel;

    // Program Counter
    program_counter PC (.clk(clk),.reset(reset),
        .pc_in(pc_in),.pc_out(pc));

    // PC + 4 adder
    adderforpc pcadder (.frompc(pc),.nxtpc(pc_next));

    // Instruction Memory
    instruction_mem imem (.clk(clk),.reset(reset),
        .rd_add(pc),.ins_out(instr));

    // Register File
    reg_file rf (
        .clk(clk),.reset(reset),.reg_write(reg_wr),
        .rs1(instr[19:15]),.rs2(instr[24:20]),
        .rd(instr[11:7]),.wr_data(wr_back),
        .rd_data1(rd_data1),.rd_data2(rd_data2));

    // Immediate Generator
    imm_gen ig (.opcode(instr[6:0]),.ins(instr),.imm_op(imm_ext));

    // Control Unit
    con_unit cu (.opcode(instr[6:0]),.funct3(instr[14:12]),
        .branch(branch),.reg_wr(reg_wr),
        .alusrc(alusrc),.mem_rd(mem_rd),
        .mem_wr(mem_wr),.memtoreg(memtoreg),
        .aluop(alu_op));

    // ALU Control
    alu_control aluctrl (.aluop(alu_op),.fun7(instr[30]),
        .fun3(instr[14:12]),.control_out(alu_control_signal));

    // ALU input mux
    mux1 alu_mux (.sel1(alusrc),.a1(rd_data2),.b1(imm_ext),.y1(alu_src_b));

    // ALU
    alu_unit alu (.a(rd_data1),.b(alu_src_b),.control_in(alu_control_signal),
        .zero(zero),.alu_result(alu_result));

    // Branch Adder
    riscv_adders branch_adder (.in1(pc),
        .in2(imm_ext),.sum(sum_branch));

    // Branch condition logic
    and_logic andgate (.branch(branch),
        .zero(zero),.and_out(pc_sel));

    // PC selection mux
    mux2 pcmux (.sel2(pc_sel),.a2(pc_next),.b2(sum_branch),.y2(pc_in));

    // Data Memory
    data_memory DMEM (.clk(clk),.reset(reset),.addr(alu_result),.write_data(rd_data2),.mem_rd(mem_rd),
        .mem_wr(mem_wr),.read_data(mem_out) );

    // Write-back mux
    mux3 wb_mux (.sel3(memtoreg),.a3(alu_result),.b3(mem_out),.y3(wr_back));

    // Assign outputs
    assign instruction = instr;
    assign alu_out     = alu_result;
    assign reg1_data   = rd_data1;
    assign reg2_data   = rd_data2;
    assign data_memory_out = mem_out;  

endmodule
