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
// File: frontend.sv
// Author: Marco Andorno
// Date: 07/10/2019

import len5_pkg::*;
import memory_pkg::*;
import expipe_pkg::*;
import fetch_pkg::*;

module frontend
#(
    parameter HLEN = 4,
    parameter BTB_BITS = 4,
    parameter [XLEN-1:0] BOOT_PC = 'h0
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
    output  logic [ILEN-1:0]    instruction_o,
    output  logic [XLEN-1:0]    curr_pc_o,
    output  prediction_t        pred_o,

    // From branch unit (ex stage)
    input   logic               res_valid_i,
    input   resolution_t        res_i,

    // To backend
    output  logic               except_raised_o,
    output  except_code_t       except_code_o,
    

    // For pc_gen from or to back end
    input   logic               except_i,
    input   logic [XLEN-1:0]    except_pc_i  
);

    // Signal declarations
    logic             fetch_ready_o;
    prediction_t      pred_i;
    logic [XLEN-1:0]  pc_o;
    icache_out_t      icache_data;

    assign  icache_data.pc    = icache_frontend_ans_i.vaddr;
    assign  icache_data.line  = icache_frontend_ans_i.line;

    fetch_stage #(
        .HLEN     (HLEN     ),
        .BTB_BITS (BTB_BITS )
    ) u_fetch_stage(
    	.clk_i           (clk_i           ),
        .rst_n_i         (rst_n_i         ),
        .flush_i         (flush_i         ),
        .pc_i            (pc_i            ),
        .mem_valid_i     (mem_valid_i     ),
        .mem_ready_i     (mem_ready_i     ),
        .mem_valid_o     (mem_valid_o     ),
        .mem_ready_o     (mem_ready_o     ),
        .mem_ans_i       (mem_ans_i       ),
        .mem_req_o       (mem_req_o       ),
        .issue_ready_i   (issue_ready_i   ),
        .issue_valid_o   (issue_valid_o   ),
        .instruction_o   (instruction_o   ),
        .curr_pc_o       (curr_pc_o       ),
        .pred_o          (pred_o          ),
        .except_raised_o (except_raised_o ),
        .except_code_o   (except_code_o   ),
        .res_valid_i     (res_valid_i     ),
        .res_i           (res_i           )
    );
    

    pc_gen_stage #(.BOOT_PC(BOOT_PC)) pc_gen_stage_u
    (
        .clk_i    		(clk_i),
        .rst_n_i  		(rst_n_i),
        .except_i		(except_i),
        .except_pc_i	(except_pc_i),
        .res_i			(res_i),
        .pred_i			(pred_i),
        .fetch_ready_i	(fetch_ready_o),
        .pc_o			(pc_o)
    );

    // If the flush is caused by a misprediction,
    // there no need to flush the BPU, just update it
    assign pred_o = pred_i;

endmodule
