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
    input   logic               flush_bpu_i,

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
    output  instr_t             issue_instr_o,
    output  prediction_t        issue_pred_o,
    output  logic               issue_except_raised_o,
    output  except_code_t       issue_except_code_o,


    // From commit unit
    input   logic               comm_except_raised_i,
    input   logic [XLEN-1:0]    comm_except_pc_i,
    input   logic               comm_res_valid_i,
    input   resolution_t        comm_res_i  
);

    // INTERNAL SIGNALS
    // ----------------

    // Current program counter
    logic [XLEN-1:0]        curr_pc;
    prediction_t            curr_pred;

    // Memory Interface <--> PC generator
    logic       memif_pcgen_ready;
    logic       pcgen_memif_valid;

    // -------
    // MODULES
    // -------

    // BPU      \
    //           }  MEMORY INTERFACE > ISSUE STAGE
    // PC GEN   /

    // BRANCH PREDICTION UNIT
    // ----------------------
    // NOTE: the prediction is provided in the same cycle as the PC, so no
    //       synchronization is required.
    bpu #(
        .HLEN     (HLEN     ),
        .BTB_BITS (BTB_BITS )
    ) u_bpu (
    	.clk_i            (clk_i            ),
        .rst_n_i          (rst_n_i          ),
        .flush_i          (flush_bpu_i      ),
        .curr_pc_i        (curr_pc          ),
        .comm_res_valid_i (comm_res_valid_i ),
        .comm_res_i       (comm_res_i       ),
        .pred_o           (curr_pred        )
    );

    // PC GENERATOR
    // ------------
    pc_gen #(
        .BOOT_PC (BOOT_PC )
    ) u_pc_gen(
    	.clk_i                (clk_i                ),
        .rst_n_i              (rst_n_i              ),
        .comm_except_raised_i (comm_except_raised_i ),
        .comm_except_pc_i     (comm_except_pc_i     ),
        .comm_res_valid_i     (comm_res_valid_i     ),
        .comm_res_i           (comm_res_i           ),
        .pred_i               (curr_pred            ),
        .mem_ready_i          (memif_pcgen_ready    ),
        .valid_o              (pcgen_memif_valid    ),
        .pc_o                 (curr_pc              )
    );

    // MEMORY INTERFACE
    // ----------------
    fetch_mem_if u_mem_if (	
        .clk_i                 (clk_i                 ),
        .rst_n_i               (rst_n_i               ),
        .flush_i               (flush_i               ),
        .fetch_valid_i         (pcgen_memif_valid     ),
        .fetch_ready_o         (memif_pcgen_ready     ),
        .fetch_pred_i          (curr_pred             ),
        .issue_valid_o         (issue_valid_o         ),
        .issue_ready_i         (issue_ready_i         ),
        .issue_instr_o         (issue_instr_o         ),
        .issue_pred_o          (issue_pred_o          ),
        .issue_except_raised_o (issue_except_raised_o ),
        .issue_except_code_o   (issue_except_code_o   ),
        .mem_valid_i           (mem_valid_i           ),
        .mem_ready_i           (mem_ready_i           ),
        .mem_valid_o           (mem_valid_o           ),
        .mem_ready_o           (mem_ready_o           ),
        .mem_ans_i             (mem_ans_i             ),
        .mem_req_o             (mem_req_o             )
    );

endmodule
