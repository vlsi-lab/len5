// Copyright 2019 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: fetch_stage.sv
// Author: Marco Andorno
// Date: 07/10/2019

import len5_pkg::*;
import memory_pkg::*;
import expipe_pkg::*;
import fetch_pkg::*;

module fetch_stage
#(
    parameter HLEN = 4,
    parameter BTB_BITS = 4,
    parameter BOOT_PC = 64'h0
)
(
    input   logic               clk_i,
    input   logic               rst_n_i,
    input   logic               flush_i,

    // From/to memory
    input   logic               mem_valid_i,
    input   logic               mem_ready_i,
    output  logic               mem_valid_o,
    output  logic               mem_ready_o,
    input   mem_ans_t           mem_ans_i,
    output  mem_req_t           mem_req_o,

    // From/to instruction decode
    input   logic               issue_ready_i,
    output  logic               issue_valid_o,
    output  instr_t             instruction_o,
    output  logic [XLEN-1:0]    curr_pc_o,
    output  prediction_t        pred_o,

    // To backend
    output  logic               except_raised_o,
    output  except_code_t       except_code_o,

    // From commit unit
    input   logic               except_raised_i,
    input   logic [XLEN-1:0]    except_pc_i,
    input   logic               res_valid_i,
    input   resolution_t        res_i  
);

    // INTERNAL SIGNALS
    // ----------------

    // -------
    // MODULES
    // -------

    // BRANCH PREDICTION UNIT
    // ----------------------

    // PC GENERATOR
    // ------------
    pc_gen #(
        .BOOT_PC (BOOT_PC )
    ) u_pc_gen(
    	.clk_i           (clk_i           ),
        .rst_n_i         (rst_n_i         ),
        .except_raised_i (except_raised_i ),
        .except_pc_i     (except_pc_i     ),
        .res_valid_i     (res_valid_i     ),
        .res_i           (res_i           ),
        .pred_valid_i    (pred_valid_i    ),
        .pred_i          (pred_i          ),
        .fetch_ready_i   (fetch_ready_i   ),
        .pc_o            (pc_o            )
    );

    // MEMORY INTERFACE
    // ----------------
    fetch_mem_if u_mem_if (	
        .clk_i                 (clk_i                 ),
        .rst_n_i               (rst_n_i               ),
        .fetch_valid_i         (fetch_valid_i         ),
        .fetch_ready_i         (fetch_ready_i         ),
        .fetch_valid_o         (fetch_valid_o         ),
        .fetch_ready_o         (fetch_ready_o         ),
        .fetch_pc_i            (fetch_pc_i            ),
        .fetch_instr_o         (fetch_instr_o         ),
        .fetch_pc_o            (fetch_pc_o            ),
        .fetch_except_raised_o (fetch_except_raised_o ),
        .fetch_except_code_o   (fetch_except_code_o   ),
        .mem_valid_i           (mem_valid_i           ),
        .mem_ready_i           (mem_ready_i           ),
        .mem_valid_o           (mem_valid_o           ),
        .mem_ready_o           (mem_ready_o           ),
        .mem_ans_i             (mem_ans_i             ),
        .mem_req_o             (mem_req_o             )
    );

endmodule
