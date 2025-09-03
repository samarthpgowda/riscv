`timescale 1ns / 1ps

module tb_riscv_processor;
    reg clk;
    reg reset;
    wire [31:0] pc;
    wire [31:0] instruction;
    wire [31:0] alu_out;
    wire [31:0] reg1_data;
    wire [31:0] reg2_data;
    wire [31:0] data_memory_out;
    top uut (.clk(clk),.reset(reset),.pc(pc),.instruction(instruction),.alu_out(alu_out),.reg1_data(reg1_data),
        .reg2_data(reg2_data),.data_memory_out(data_memory_out));
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    initial begin
        $display("Time\t PC\t Instruction\t ALU_Out\t Reg1\t Reg2\t DataMem");
        reset = 1;
        #15;  
        reset = 0;
        repeat (20) begin  //20clock cycles
            @(posedge clk);
            #1; 
            $display("%0t\t %h\t %h\t %h\t %h\t %h\t %h", 
                     $time, pc, instruction, alu_out, reg1_data, reg2_data, data_memory_out);
            
            
            case (instruction[6:0])
                7'b0010011: $display("     -> ADDI x%0d, x%0d, %0d", 
                           instruction[11:7], instruction[19:15], $signed(instruction[31:20]));
                7'b0110011: begin
                    case (instruction[14:12])
                        3'b000: $display("     -> ADD x%0d, x%0d, x%0d", 
                               instruction[11:7], instruction[19:15], instruction[24:20]);
                        3'b111: $display("     -> AND x%0d, x%0d, x%0d", 
                               instruction[11:7], instruction[19:15], instruction[24:20]);
                        3'b110: $display("     -> OR x%0d, x%0d, x%0d", 
                               instruction[11:7], instruction[19:15], instruction[24:20]);
                        default: $display("     -> Unknown R-type");
                    endcase
                end
                7'b0000011: $display("     -> LW x%0d, %0d(x%0d)", 
                           instruction[11:7], $signed(instruction[31:20]), instruction[19:15]);
                7'b0100011: $display("     -> SW x%0d, %0d(x%0d)", 
                           instruction[24:20], $signed({instruction[31:25], instruction[11:7]}), instruction[19:15]);
                7'b0000000: $display("     -> NOP");
                default: $display("     -> Unknown instruction");
            endcase
        end
        $finish;
    end
    initial begin
        $monitor("At time %t: PC=%h, Instr=%h, Control signals: RegWr=%b, ALUSrc=%b, MemRd=%b, MemWr=%b", 
                 $time, pc, instruction, uut.reg_wr, uut.alusrc, uut.mem_rd, uut.mem_wr);
    end

endmodule