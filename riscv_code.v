`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.08.2025 11:24:34
// Design Name: 
// Module Name: top
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////



// Program Counter
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
// Adder for PC
module adderforpc(input [31:0] frompc, output [31:0] nxtpc);
    assign nxtpc = frompc + 4;
endmodule
//ins_mem
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
        imem[3] <= 32'h00000013; // NOP
    end
endmodule

//register File
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
// Immediate Generator
module imm_gen(
    input [6:0] opcode,
    input [31:0] ins,
    output reg [31:0] imm_op
);
    always @(*) begin
        case (opcode)
            7'b0000011,  // Load
            7'b0010011:  // I-type ALU
                imm_op = {{20{ins[31]}}, ins[31:20]};
            default: imm_op = 32'b0;
        endcase
    end
endmodule
// Control Unit
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
        branch   = 0;
        reg_wr   = 0;
        alusrc   = 0;
        mem_rd   = 0;
        mem_wr   = 0;
        memtoreg = 0;
        aluop    = 2'b00;

        case(opcode)
            7'b0010011: begin // I-type ALU
                alusrc   = 1;
                reg_wr   = 1;
                memtoreg = 0;
                aluop    = 2'b10;
            end
        endcase
    end
endmodule
// ALU

module alu_unit(
    input [31:0] a, b,
    input [3:0] control_in,
    output reg zero,
    output reg [31:0] alu_result
);
    always @(*) begin
        case (control_in)
            4'b0000: alu_result = a & b;
            4'b0001: alu_result = a | b;
            4'b0010: alu_result = a + b;
            4'b0011: alu_result = a ^ b;
            default: alu_result = 32'b0;
        endcase
        zero = (alu_result == 32'b0);
    end
endmodule

// ALU Control

module alu_control(
    input [1:0] aluop,
    input [2:0] fun3,
    output reg [3:0] control_out
);
    always @(*) begin
        case (aluop)
            2'b10: begin
                case (fun3)
                    3'b000: control_out = 4'b0010; // ADDI
                    3'b111: control_out = 4'b0000; // ANDI
                    3'b110: control_out = 4'b0001; // ORI
                    3'b100: control_out = 4'b0011; // XORI
                    default: control_out = 4'b1111;
                endcase
            end
            default: control_out = 4'b1111;
        endcase
    end
endmodule
// Data Memory

module data_memory (
    input clk,
    input reset,
    input mem_wr,
    input mem_rd,
    input [31:0] rd_add,
    input [31:0] wr_data,
    output reg [31:0] mem_data_out
);
    reg [31:0] d_mem [0:63];
    integer i;

    always @(posedge clk) begin
        if (reset) begin
            for (i=0; i<64; i=i+1) d_mem[i] <= 0;
        end
        else if (mem_wr) begin
            d_mem[rd_add[7:2]] <= wr_data;
        end
        else if (mem_rd) begin
            mem_data_out <= d_mem[rd_add[7:2]];
        end
    end
endmodule

// all Muxes

module mux1(input sel, input [31:0] a, b, output [31:0] y);
    assign y = sel ? b : a;
endmodule
module mux2(input sel, input [31:0] a, b, output [31:0] y);
    assign y = sel ? b : a;
endmodule
module mux3(input sel, input [31:0] a, b, output [31:0] y);
    assign y = sel ? b : a;
endmodule

module adder(
    input  [31:0] in1,
    input  [31:0] in2,
    output [31:0] sum
);
    assign sum = in1 + in2;
endmodule
// Branch AND gate
module and_logic(input branch, zero, output and_out);
    assign and_out = branch & zero;
endmodule
// RISC-V Top Module
module top(
    input clk,
    input reset,
    output [31:0] pc,
    output [31:0] instruction,
    output [31:0] alu_out,
    output [31:0] reg1_data,
    output [31:0] reg2_data
);

   
    wire [31:0] pc_next, pc_in;
    wire [31:0] instr;
    wire [31:0] rd_data1, rd_data2;
    wire [31:0] imm_ext, alu_src_b, alu_result;
    wire [31:0] sum_branch, mem_data, wr_back;
    wire [3:0] alu_control_signal;
    wire [1:0] alu_op;
    wire reg_wr, alusrc, zero, branch, memtoreg, memwrite, memread, pc_sel;

    // Program Counter
    program_counter PC (.clk(clk), .reset(reset), .pc_in(pc_in), .pc_out(pc));

    // PC+4
    adderforpc pcadder (.frompc(pc), .nxtpc(pc_next));

    // Instruction Memory
    instruction_mem imem (.clk(clk), .reset(reset), .rd_add(pc), .ins_out(instr));

    // Register File
    reg_file rf (.clk(clk), .reset(reset), .reg_write(reg_wr),
                 .rs1(instr[19:15]), .rs2(instr[24:20]), .rd(instr[11:7]),
                 .wr_data(wr_back), .rd_data1(rd_data1), .rd_data2(rd_data2));

    // Immediate Generator
    imm_gen ig (.opcode(instr[6:0]), .ins(instr), .imm_op(imm_ext));

    // Control Unit
    con_unit cu (.opcode(instr[6:0]), .funct3(instr[14:12]),
                 .branch(branch), .reg_wr(reg_wr), .alusrc(alusrc),
                 .mem_rd(memread), .mem_wr(memwrite), .memtoreg(memtoreg),
                 .aluop(alu_op));

    // ALU Control
    alu_control aluctrl (.aluop(alu_op), .fun3(instr[14:12]),
                         .control_out(alu_control_signal));

    // ALU operand2 mux
    mux1 alu_mux (.sel(alusrc), .a(rd_data2), .b(imm_ext), .y(alu_src_b));

    // ALU
    alu_unit alu (.a(rd_data1), .b(alu_src_b), .control_in(alu_control_signal),
                  .zero(zero), .alu_result(alu_result));

    // Branch Adder
    adder branch_adder (.in1(pc), .in2(imm_ext), .sum(sum_branch));

    // Branch condition
    and_logic andgate (.branch(branch), .zero(zero), .and_out(pc_sel));

    // PC selection
    mux2 pcmux (.sel(pc_sel), .a(pc_next), .b(sum_branch), .y(pc_in));

    // Data Memory
    data_memory dmem (.clk(clk), .reset(reset), .mem_wr(memwrite),
                      .mem_rd(memread), .rd_add(alu_result), .wr_data(rd_data2),
                      .mem_data_out(mem_data));

    // Write-back mux
    mux3 wb_mux (.sel(memtoreg), .a(alu_result), .b(mem_data), .y(wr_back));
    // Connect internal signals to outputs 
    assign instruction = instr;
    assign alu_out     = alu_result;
    assign reg1_data   = rd_data1;
    assign reg2_data   = rd_data2;

endmodule


