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
// File: fetch_mem_if.sv
// Author: Michele Caon
// Date: 04/08/2022

import len5_pkg::XLEN;
import len5_pkg::ILEN;
import len5_pkg::except_code_t;
import len5_pkg::instr_t;
import memory_pkg::*;
import fetch_pkg::mem_if_ans_reg_t;

module fetch_mem_if #(
    parameter   PC_FIFO_DEPTH = 2   // number of request that the memory can accept before providing an answer
) (
    input   logic               clk_i,
    input   logic               rst_n_i,

    // Fetch unit
    input   logic               fetch_valid_i,
    input   logic               fetch_ready_i,
    output  logic               fetch_valid_o,
    output  logic               fetch_ready_o,
    input   logic [XLEN-1:0]    fetch_pc_i, // requested PC
    output  instr_t             fetch_instr_o,
    output  logic [XLEN-1:0]    fetch_pc_o, // served PC
    output  logic               fetch_except_raised_o,
    output  except_code_t       fetch_except_code_o,

    // Memory
    input   logic               mem_valid_i,
    input   logic               mem_ready_i,
    output  logic               mem_valid_o,
    output  logic               mem_ready_o,
    input   mem_ans_t           mem_ans_i,
    output  mem_req_t           mem_req_o
);

    // INTERNAL SIGNALS
    // ----------------
    logic [XLEN-1:0]    pc;
    logic               ans_valid;
    mem_if_ans_reg_t    ans_reg_in, ans_reg_out;

    // REQUEST REGISTER
    // ----------------
    spill_cell #(
        .DATA_T (logic [XLEN-1:0] ),
        .SKIP   (0                )
    ) u_req_reg (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .valid_i (fetch_valid_i ),
        .ready_i (mem_ready_i   ),
        .valid_o (mem_valid_o   ),
        .ready_o (fetch_ready_o ),
        .data_i  (fetch_pc_i    ),
        .data_o  (pc            )
    );

    // ANSWER REGISTER
    // ---------------

    // Accept instruction answers only
    assign  ans_valid    = mem_valid_i & (mem_ans_i.acc_type == MEM_ACC_INSTR);

    // Answer register data
    assign  ans_reg_in.instr            = mem_ans_i.value[ILEN-1:0];
    assign  ans_reg_in.addr             = mem_ans_i.addr;
    assign  ans_reg_in.except_raised    = mem_ans_i.except_raised;
    assign  ans_reg_in.except_code      = mem_ans_i.except_code;
    
    spill_cell #(
        .DATA_T (mem_if_ans_reg_t ),
        .SKIP   (0                )
    ) u_ans_reg (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .valid_i (ans_valid     ),
        .ready_i (fetch_ready_i ),
        .valid_o (fetch_valid_o ),
        .ready_o (mem_ready_o   ),
        .data_i  (ans_reg_in    ),
        .data_o  (ans_reg_out   )
    );

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    // Memory request
    assign  mem_req_o.tag       = '0;
    assign  mem_req_o.acc_type  = MEM_ACC_INSTR;
    assign  mem_req_o.ls_type   = LS_WORD;
    assign  mem_req_o.addr      = pc;
    assign  mem_req_o.value     = '0;

    // Fetched instruction
    assign  fetch_instr_o.raw       = ans_reg_out.instr;
    assign  fetch_pc_o              = ans_reg_out.addr;
    assign  fetch_except_raised_o   = ans_reg_out.except_raised;
    assign  fetch_except_code_o     = ans_reg_out.except_code;
    
endmodule