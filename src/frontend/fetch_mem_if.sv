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

`include "len5_config.svh"

import len5_pkg::XLEN;
import len5_pkg::ILEN;
import len5_pkg::except_code_t;
import len5_pkg::instr_t;
import memory_pkg::*;
import expipe_pkg::*;
import fetch_pkg::mem_if_ans_reg_t;
import fetch_pkg::prediction_t;

module fetch_mem_if #(
    parameter   MAX_MEM_OUTSTANDING_REQUESTS = 2 // at least the number of requests that the memory can accept simultaneously
) (
    input   logic               clk_i,
    input   logic               rst_n_i,
    input   logic               flush_i,

    // Fetch unit (BPU and PC generator)
    input   logic               fetch_valid_i,
    output  logic               fetch_ready_o,
    input   prediction_t        fetch_pred_i,   // contains the current PC

    // Issue stage
    output  logic               issue_valid_o,
    input   logic               issue_ready_i,
    output  instr_t             issue_instr_o,
    output  prediction_t        issue_pred_o,   // contains the served PC
    output  logic               issue_except_raised_o,
    output  except_code_t       issue_except_code_o,

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
    prediction_t        req_reg_out;
    logic               pred_fifo_push, pred_fifo_pop;
    prediction_t        pred_fifo_out;
    logic               ans_valid;
    mem_if_ans_reg_t    ans_reg_in, ans_reg_out;

    // -------
    // MODULES
    // -------

    //             / MEMORY \
    // FETCH STAGE           } FETCH STAGE
    //             \  FIFO  /
    // 
    // While waiting for the memory to serve the requested PC, the prediction
    // data is stored in a FIFO buffer. 
    // IMPORTANT: the prediction FIFO must be large enough to contain all the
    // pending memory requests! With the bare metal emulator, this is at most
    // 2, since the memory emulator uses a single spill cell (2 registers) as
    // output register. Moreover, a FIFO works only if the memory processes 
    // the requests in order.

    // REQUEST REGISTER
    // ----------------
    spill_cell_flush #(
        .DATA_T (prediction_t         ),
        .SKIP   (FETCH_REQ_SPILL_SKIP )
    ) u_req_reg (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .flush_i (flush_i       ),
        .valid_i (fetch_valid_i ),
        .ready_i (mem_ready_i   ),
        .valid_o (mem_valid_o   ),
        .ready_o (fetch_ready_o ),
        .data_i  (fetch_pred_i  ),
        .data_o  (req_reg_out   )
    );

    // PREDICTION BUFFER
    // -----------------
    // Holds branch prediction data while the current instruction is fetched
    // from the memory
    assign  pred_fifo_push  = mem_valid_o & mem_ready_i;
    assign  pred_fifo_pop   = mem_valid_i & mem_ready_o;
    fifo_nohs #(
        .DATA_T (prediction_t                 ),
        .DEPTH  (MAX_MEM_OUTSTANDING_REQUESTS )
    ) u_pred_fifo (
    	.clk_i   (clk_i          ),
        .rst_n_i (rst_n_i        ),
        .flush_i (flush_i        ),
        .push_i  (pred_fifo_push ),
        .pop_i   (pred_fifo_pop  ),
        .data_i  (req_reg_out    ),
        .data_o  (pred_fifo_out  )
    );

    // ANSWER REGISTER
    // ---------------

    // Accept instruction answers only
    assign  ans_valid    = mem_valid_i & (mem_ans_i.acc_type == MEM_ACC_INSTR);

    // Answer register data
    assign  ans_reg_in.instr            = mem_ans_i.value[ILEN-1:0];
    assign  ans_reg_in.pred_data        = pred_fifo_out;
    assign  ans_reg_in.except_raised    = mem_ans_i.except_raised;
    assign  ans_reg_in.except_code      = mem_ans_i.except_code;
    
    spill_cell_flush #(
        .DATA_T (mem_if_ans_reg_t     ),
        .SKIP   (FETCH_ANS_SPILL_SKIP )
    ) u_ans_reg (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .flush_i (flush_i       ),
        .valid_i (ans_valid     ),
        .ready_i (issue_ready_i ),
        .valid_o (issue_valid_o ),
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
    assign  mem_req_o.addr      = req_reg_out.pc;
    assign  mem_req_o.value     = '0;

    // Fetched instruction
    assign  issue_instr_o.raw       = ans_reg_out.instr;
    assign  issue_pred_o            = ans_reg_out.pred_data;
    assign  issue_except_raised_o   = ans_reg_out.except_raised;
    assign  issue_except_code_o     = ans_reg_out.except_code;
    
endmodule