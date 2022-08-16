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

`include "memory_class.svh"
`include "uvm_macros.svh"

import uvm_pkg::*;
import memory_pkg::*;
import len5_pkg::*;

module memory_bare_emu #(
    parameter   MEM_FILE    = "memory.txt",
    parameter   DUMP_FILE   = "memory_dump.txt"
) (
    input   logic           clk_i,
    input   logic           rst_n_i,

    input   logic           valid_i,
    input   logic           ready_i,
    output  logic           valid_o,
    output  logic           ready_o,
    input   mem_req_t       req_i,
    output  mem_ans_t       ans_o
);

    // INTERNAL SIGNALS
    // ----------------
    mem_ans_t       ans;    // answer to the core
    memory_class    mem;    // memory object
    int             ret;    // memory emulator return value

    // Memory initialization
    // ---------------------
    initial begin
        mem = new(MEM_FILE);
        mem.LoadMem();

        // Dump the memory content in each cycle 
        while (1) begin
            @(posedge clk_i);
            mem.PrintMem(DUMP_FILE);
        end
    end

    // Process a memory request
    // ------------------------
    always_comb begin : p_mem_req
        ans.tag             = req_i.tag;
        ans.acc_type        = req_i.acc_type;
        ans.addr            = req_i.addr;
        ans.value           = 'h0;
        ans.except_raised   = 1'b0;
        ans.except_code     = E_UNKNOWN;

        if (valid_i) begin
            
            case (req_i.acc_type)
                MEM_ACC_INSTR: begin: read_instruction
                    ret         = mem.ReadW(req_i.addr);
                    ans.value   = {'0, mem.read_word};
                end
                MEM_ACC_ST: begin
                    case (req_i.ls_type)
                        LS_BYTE, LS_BYTE_U: begin
                            ret = mem.WriteB(req_i.addr, req_i.value[7:0]);
                        end
                        LS_HALFWORD, LS_HALFWORD_U: begin
                            ret = mem.WriteHW(req_i.addr, req_i.value[15:0]);
                        end
                        LS_WORD, LS_WORD_U: begin
                            ret = mem.WriteW(req_i.addr, req_i.value[31:0]);
                        end
                        default: begin
                            ret = mem.WriteDW(req_i.addr, req_i.value[63:0]);
                        end
                    endcase
                end
                default: begin: load_data
                    case (req_i.ls_type)
                        LS_BYTE, LS_BYTE_U: begin
                            ret         = mem.ReadB(req_i.addr);
                            ans.value   = {'0, mem.read_byte};
                        end
                        LS_HALFWORD, LS_HALFWORD_U: begin
                            ret         = mem.ReadHW(req_i.addr);
                            ans.value   = {'0, mem.read_halfword};
                        end
                        LS_WORD, LS_WORD_U: begin
                            ret         = mem.ReadW(req_i.addr);
                            ans.value   = {'0, mem.read_word};
                        end
                        default: begin
                            ret         = mem.ReadDW(req_i.addr);
                            ans.value   = mem.read_doubleword;
                        end
                    endcase
                end
            endcase

            // Exception handling
            case (ret)
                0: ans.except_raised = 1'b0;
                1: begin: address_misaligned
                    ans.except_raised   = 1'b1;
                    case (req_i.acc_type)
                        MEM_ACC_INSTR:  ans.except_code = E_I_ADDR_MISALIGNED;
                        MEM_ACC_LD:     ans.except_code = E_LD_ADDR_MISALIGNED;
                        MEM_ACC_ST:     ans.except_code = E_ST_ADDR_MISALIGNED;
                        default:        ans.except_code = E_UNKNOWN;
                    endcase
                end
                2: begin: access_fault
                    ans.except_raised   = 1'b1;
                    case (req_i.acc_type)
                        MEM_ACC_INSTR:  ans.except_code = E_I_ACCESS_FAULT;
                        MEM_ACC_LD:     ans.except_code = E_LD_ACCESS_FAULT;
                        MEM_ACC_ST:     ans.except_code = E_ST_ACCESS_FAULT;
                        default:        ans.except_code = E_UNKNOWN;
                    endcase
                end
                default: begin
                    ans.except_raised   = 1'b1;
                    ans.except_code = E_UNKNOWN;
                end
            endcase
        end
    end

    // Output register
    // ---------------
    spill_cell #(
        .DATA_T (mem_ans_t )
    ) u_spill_cell (
    	.clk_i   (clk_i    ),
        .rst_n_i (rst_n_i  ),
        .valid_i (valid_i  ),
        .ready_i (ready_i  ),
        .valid_o (valid_o  ),
        .ready_o (ready_o  ),
        .data_i  (ans      ),
        .data_o  (ans_o    )
    );
    
endmodule