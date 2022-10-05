// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: memory_bare_emu.sv
// Author: Michele Caon
// Date: 01/08/2022

`include "uvm_macros.svh"
import uvm_pkg::*;

`include "memory_class.svh"
`include "len5_config.svh"

import memory_pkg::*;
import len5_pkg::*;
import expipe_pkg::*;

module memory_bare_emu #(
    parameter   DUMP_PERIOD         = 0, // cycles, zero to disable
    parameter   PIPE_NUM            = 0, // number of pipeline registers 
    parameter   SKIP_INS_ANS_REG    = 0, // instruction from memory is directly passed to fetch
    parameter   SKIP_DATA_ANS_REG   = 0  // data from memory is directly passed to LSU
) (
    input   logic           clk_i,
    input   logic           rst_n_i,
    input   logic           flush_i,

    input   string          mem_file_i,
    input   string          mem_dump_file_i,

    // Instruction port (read-only)
    input   logic           ins_valid_i,
    input   logic           ins_ready_i,
    output  logic           ins_valid_o,
    output  logic           ins_ready_o,
    input   mem_req_t       ins_req_i,
    output  mem_ans_t       ins_ans_o,

    // Data port
    input   logic           data_valid_i,
    input   logic           data_ready_i,
    output  logic           data_valid_o,
    output  logic           data_ready_o,
    input   mem_req_t       data_req_i,
    output  mem_ans_t       data_ans_o
);

    // INTERNAL SIGNALS
    // ----------------
    // Instruction and data memory
    mem_ans_t       ins_ans, data_ans;  // answer to the core
    memory_class    i_mem, d_mem;       // memory objects (the memory array itself is a static member)
    int             i_ret, d_ret;       // memory emulator return value

    // Pipeline registers
    logic           ins_pipe_en, data_pipe_en;
    logic           ins_pipe_valid[PIPE_NUM+1], data_pipe_valid[PIPE_NUM+1];
    mem_ans_t       ins_pipe_reg[PIPE_NUM+1], data_pipe_reg[PIPE_NUM+1];

    // Memory initialization
    // ---------------------
    initial begin
        #1;
        `uvm_info("MEM EMU", $sformatf("Flashing memory image '%s'...", mem_file_i), UVM_HIGH);
        i_mem = new(mem_file_i);
        d_mem = new(mem_file_i);
        if (i_mem.LoadMem() <= 0) begin
            `uvm_fatal("MEM EMU", "Unable to load instruction memory")
        end
    end

    // Memory dump
    // -----------
    // Dump the memory content in each cycle 
    generate
        if (DUMP_PERIOD > 0) begin: mem_dump
            initial begin
                while (1) begin
                    repeat (DUMP_PERIOD) @(posedge clk_i);
                    if (i_mem.PrintMem(mem_dump_file_i)) begin
                        `uvm_error("MEM EMU", "Unable to dump memory content to file");
                    end
                end
            end
        end
    endgenerate

    // INSTRUCTION REQUEST
    // -------------------
    always_comb begin : p_ins_mem_req
        ins_ans.tag             = ins_req_i.tag;
        ins_ans.acc_type        = ins_req_i.acc_type;
        ins_ans.addr            = ins_req_i.addr;
        ins_ans.value           = 'h0;
        ins_ans.except_raised   = 1'b0;
        ins_ans.except_code     = E_UNKNOWN;

        if (ins_valid_i) begin
            case (ins_req_i.acc_type)
                MEM_ACC_INSTR: begin: read_instruction
                    i_ret             = i_mem.ReadW(ins_req_i.addr);
                    ins_ans.value   = {'0, i_mem.read_word};
                end
                default: begin
                    `uvm_error("MEM EMU", "Unsupported instruction request");
                end
            endcase

            // Exception handling
            case (i_ret)
                0: ins_ans.except_raised = 1'b0;
                1: begin: address_misaligned
                    ins_ans.except_raised   = 1'b1;
                    case (ins_req_i.acc_type)
                        MEM_ACC_INSTR:  ins_ans.except_code = E_I_ADDR_MISALIGNED;
                        default:        ins_ans.except_code = E_UNKNOWN;
                    endcase
                end
                2: begin: access_fault
                    ins_ans.except_raised   = 1'b1;
                    case (ins_req_i.acc_type)
                        MEM_ACC_INSTR:  ins_ans.except_code = E_I_ACCESS_FAULT;
                        default:        ins_ans.except_code = E_UNKNOWN;
                    endcase
                end
                default: begin
                    ins_ans.except_raised   = 1'b1;
                    ins_ans.except_code = E_UNKNOWN;
                end
            endcase
        end
    end

    // DATA REQUEST
    // ------------
    always_ff @( negedge clk_i ) begin : p_data_mem_req
        data_ans.tag             <= data_req_i.tag;
        data_ans.acc_type        <= data_req_i.acc_type;
        data_ans.addr            <= data_req_i.addr;
        data_ans.value           <= 'h0;
        data_ans.except_raised   <= 1'b0;
        data_ans.except_code     <= E_UNKNOWN;

        if (data_valid_i) begin
            
            case (data_req_i.acc_type)
                MEM_ACC_ST: begin: store_data
                    case (data_req_i.ls_type)
                        LS_BYTE, LS_BYTE_U: begin
                            d_mem.WriteB(data_req_i.addr, data_req_i.value[7:0]);
                        end
                        LS_HALFWORD, LS_HALFWORD_U: begin
                            d_ret = d_mem.WriteHW(data_req_i.addr, data_req_i.value[15:0]);
                        end
                        LS_WORD, LS_WORD_U: begin
                            d_ret = d_mem.WriteW(data_req_i.addr, data_req_i.value[31:0]);
                        end
                        LS_DOUBLEWORD: begin
                            d_ret = d_mem.WriteDW(data_req_i.addr, data_req_i.value);
                        end
                        default: begin
                            `uvm_error("MEM EMU", "Unsupported data store request");
                        end
                    endcase
                end
                MEM_ACC_LD: begin: load_data
                    case (data_req_i.ls_type)
                        LS_BYTE, LS_BYTE_U: begin
                            d_ret           = d_mem.ReadB(data_req_i.addr);
                            data_ans.value  <= {'0, d_mem.read_byte};
                        end
                        LS_HALFWORD, LS_HALFWORD_U: begin
                            d_ret           = d_mem.ReadHW(data_req_i.addr);
                            data_ans.value  <= {'0, d_mem.read_halfword};
                        end
                        LS_WORD, LS_WORD_U: begin
                            d_ret           = d_mem.ReadW(data_req_i.addr);
                            data_ans.value  <= {'0, d_mem.read_word};
                        end
                        LS_DOUBLEWORD: begin
                            d_ret           = d_mem.ReadDW(data_req_i.addr);
                            data_ans.value  <= {'0, d_mem.read_doubleword};
                        end
                        default: begin
                            `uvm_error("MEM EMU", "Unsupported data load request");
                        end
                    endcase
                end
                default: begin
                    `uvm_error("MEM EMU", "Unsupported data request");
                end
            endcase

            // Exception handling
            case (d_ret)
                0: data_ans.except_raised <= 1'b0;
                1: begin: address_misaligned
                    data_ans.except_raised   <= 1'b1;
                    case (data_req_i.acc_type)
                        MEM_ACC_INSTR:  data_ans.except_code <= E_I_ADDR_MISALIGNED;
                        MEM_ACC_LD:     data_ans.except_code <= E_LD_ADDR_MISALIGNED;
                        MEM_ACC_ST:     data_ans.except_code <= E_ST_ADDR_MISALIGNED;
                        default:        data_ans.except_code <= E_UNKNOWN;
                    endcase
                end
                2: begin: access_fault
                `ifndef MEM_EMU_RAISE_READ_ACCESS_FAULT
                    data_ans.except_raised   <= 1'b0;
                    data_ans.value           <= '0;
                `else
                    data_ans.except_raised   <= 1'b1;
                    case (data_req_i.acc_type)
                        MEM_ACC_INSTR:  data_ans.except_code <= E_I_ACCESS_FAULT;
                        MEM_ACC_LD:     data_ans.except_code <= E_LD_ACCESS_FAULT;
                        MEM_ACC_ST:     data_ans.except_code <= E_ST_ACCESS_FAULT;
                        default:        data_ans.except_code <= E_UNKNOWN;
                    endcase
                `endif /* MEM_EMU_RAISE_READ_ACCESS_FAULT */
                end
                default: begin
                    data_ans.except_raised  <= 1'b1;
                    data_ans.except_code    <= E_UNKNOWN;
                end
            endcase
        end
    end

    // Memory pipeline registers
    // -------------------------
    // NOTE: Theese emulate high-latency memory accesses
    assign  ins_pipe_en         = ins_ready_o;
    assign  ins_pipe_valid[0]   = ins_valid_i;
    assign  ins_pipe_reg[0]     = ins_ans;
    assign  data_pipe_en        = data_ready_o;
    assign  data_pipe_valid[0]  = data_valid_i;
    assign  data_pipe_reg[0]    = data_ans;
    generate
        for (genvar i = 1; i < PIPE_NUM+1; i++) begin
            always_ff @( posedge clk_i ) begin : mem_pipe_reg
                if (!rst_n_i) begin
                    ins_pipe_valid[i]   <= 1'b0;
                    ins_pipe_reg[i]     <= '0;
                    data_pipe_valid[i]  <= 1'b0;
                    data_pipe_reg[i]    <= '0;
                end else if (flush_i) begin
                    ins_pipe_valid[i]   <= 1'b0;
                    ins_pipe_reg[i]     <= '0;
                    data_pipe_valid[i]  <= 1'b0;
                    data_pipe_reg[i]    <= '0;
                end else begin
                    if (ins_pipe_en) begin
                        ins_pipe_valid[i]   <= ins_pipe_valid[i-1];
                        ins_pipe_reg[i]     <= ins_pipe_reg[i-1];
                    end
                    if (data_pipe_en) begin
                        data_pipe_valid[i]  <= data_pipe_valid[i-1];
                        data_pipe_reg[i]    <= data_pipe_reg[i-1];
                    end
                end
            end
        end
    endgenerate

    // Output registers
    // ----------------
    spill_cell_flush #(
        .DATA_T (mem_ans_t        ),
        .SKIP   (SKIP_INS_ANS_REG )
    ) u_ins_out_reg (
    	.clk_i   (clk_i                    ),
        .rst_n_i (rst_n_i                  ),
        .flush_i (flush_i                  ),
        .valid_i (ins_pipe_valid[PIPE_NUM] ),
        .ready_i (ins_ready_i              ),
        .valid_o (ins_valid_o              ),
        .ready_o (ins_ready_o              ),
        .data_i  (ins_pipe_reg[PIPE_NUM]   ),
        .data_o  (ins_ans_o                )
    );

    spill_cell_flush #(
        .DATA_T (mem_ans_t        ),
        .SKIP   (SKIP_DATA_ANS_REG )
    ) u_data_out_reg (
    	.clk_i   (clk_i                     ),
        .rst_n_i (rst_n_i                   ),
        .flush_i (flush_i                   ),
        .valid_i (data_pipe_valid[PIPE_NUM] ),
        .ready_i (data_ready_i              ),
        .valid_o (data_valid_o              ),
        .ready_o (data_ready_o              ),
        .data_i  (data_pipe_reg[PIPE_NUM]   ),
        .data_o  (data_ans_o                )
    );
    
endmodule