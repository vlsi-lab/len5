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

module front_end
#(
  parameter HLEN = 4,
  parameter BTB_BITS = 4,
  parameter [XLEN-1:0] BOOT_PC = 'h0
)
(
  input   logic             clk_i,
  input   logic             rst_n_i,
  input   logic             flush_i,
  // input logic stall,

  // From/to i-cache
  output  logic [XLEN-1:0]  addr_o,
  output  logic             addr_valid_o,
  input   logic             addr_ready_i,
  input   var icache_out_t      data_i,
  input   logic             data_valid_i,
  output  logic             data_ready_o,

  // From/to instruction decode
  input   logic             issue_ready_i,
  output  logic             issue_valid_o,
  output  logic [ILEN-1:0]  instruction_o,
  output  prediction_t      pred_o,

  // From branch unit (ex stage)
  input   var resolution_t      res_i,

  // From Icache
  input icache_frontend_ans_t icache_frontend_ans_i,

  // To backend
  output logic except_o,
  //output logic [ROB_EXCEPT_LEN-1:0] except_code_o,
  output except_code_t except_code_o,
  

  // For pc_gen from or to back end
  input   logic             except_i,
  input   logic [XLEN-1:0]  except_pc_i  
);

  // Signal declarations
  logic             fetch_ready_o;
  prediction_t      pred_i;
  logic [XLEN-1:0]  pc_o;

fetch_stage #(.HLEN(HLEN),.BTB_BITS(BTB_BITS)) fetch_stage_u
(
  	.clk_i    (clk_i),
    .rst_n_i  (rst_n_i),
    .flush_i  (flush_i),
  
  // From/to PC gen stage
  .pc_i				(pc_o),
  .fetch_ready_o	(fetch_ready_o),

  // From/to i-cache
  .addr_o			(addr_o),
  .addr_valid_o		(addr_valid_o),
  .addr_ready_i		(addr_ready_i),
  .data_i			(data_i),
  .data_valid_i		(data_valid_i),
  .data_ready_o		(data_ready_o),

  // From/to instruction decode
  .issue_ready_i	(issue_ready_i),
  .issue_valid_o	(issue_valid_o),
  .instruction_o	(instruction_o),
  .pred_o			(pred_i),

  .icache_frontend_ans_i(icache_frontend_ans_i),

  .except_o(except_o),
  .except_code_o(except_code_o),

  // From branch unit (ex stage)
  .res_i			(res_i)  
);

pc_gen_stage #(.BOOT_PC(BOOT_PC)) pc_gen_stage_u
(
  .clk_i    		(clk_i),
  .rst_n_i  		(rst_n_i),
  .except_i			(except_i),
  .except_pc_i		(except_pc_i),
  .res_i			(res_i),
  .pred_i			(pred_i),
  .fetch_ready_i	(fetch_ready_o),
  .pc_o				(pc_o)
);

  // If the flush is caused by a misprediction,
  // there no need to flush the BPU, just update it
  assign pred_o = pred_i;

endmodule
