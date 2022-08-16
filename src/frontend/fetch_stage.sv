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
    parameter BTB_BITS = 4
)
(
    input   logic               clk_i,
    input   logic               rst_n_i,
    input   logic               flush_i,
    
    // From/to PC gen stage
    input   logic [XLEN-1:0]    pc_i,
    // output  logic               fetch_ready_o,

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

    // MEMORY INTERFACE
    // ----------------

endmodule
