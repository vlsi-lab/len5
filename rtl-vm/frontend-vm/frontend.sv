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

module frontend #(
    parameter HLEN = 4,
    parameter BTB_BITS = 4,
    parameter [len5_pkg::XLEN-1:0] BOOT_PC = 'h0
) (
    input logic clk_i,
    input logic rst_ni,
    input logic flush_i,

    // From/to i-cache
    output logic                 [len5_pkg::XLEN-1:0] addr_o,
    output logic                            addr_valid_o,
    input  logic                            addr_ready_i,
    output logic                            data_ready_o,
    input  icache_frontend_ans_t            icache_frontend_ans_i,

    // From/to instruction decode
    input  logic                   issue_ready_i,
    output logic                   issue_valid_o,
    output logic        [ILEN-1:0] instruction_o,
    output logic        [len5_pkg::XLEN-1:0] curr_pc_o,
    output prediction_t            pred_o,

    // From branch unit (ex stage)
    input resolution_t res_i,

    // To backend
    output logic         except_o,
    output except_code_t except_code_o,


    // For pc_gen from or to back end
    input logic            except_i,
    input logic [len5_pkg::XLEN-1:0] except_pc_i
);

  // Signal declarations
  logic                   fetch_ready_o;
  prediction_t            pred_i;
  logic        [XLEN-1:0] pc_o;
  icache_out_t            icache_data;

  assign icache_data.pc   = icache_frontend_ans_i.vaddr;
  assign icache_data.line = icache_frontend_ans_i.line;

  fetch_stage #(
      .HLEN(HLEN),
      .BTB_BITS(BTB_BITS)
  ) fetch_stage_u (
      .clk_i  (clk_i),
      .rst_ni(rst_ni),
      .flush_i(flush_i),

      // From/to PC gen stage
      .pc_i         (pc_o),
      .fetch_ready_o(fetch_ready_o),

      // From/to i-cache
      .addr_o      (addr_o),
      .addr_valid_o(addr_valid_o),
      .addr_ready_i(addr_ready_i),
      .data_i      (icache_data),
      .data_valid_i(icache_frontend_ans_i.valid),
      .data_ready_o(data_ready_o),

      // From/to instruction decode
      .issue_ready_i(issue_ready_i),
      .issue_valid_o(issue_valid_o),
      .instruction_o(instruction_o),
      .curr_pc_o    (curr_pc_o),
      .pred_o       (pred_i),

      .icache_frontend_ans_i(icache_frontend_ans_i),

      .except_o(except_o),
      .except_code_o(except_code_o),

      // From branch unit (ex stage)
      .res_i(res_i)
  );

  pc_gen #(
      .BOOT_PC(BOOT_PC)
  ) pc_gen_u (
      .clk_i        (clk_i),
      .rst_ni      (rst_ni),
      .except_i     (except_i),
      .except_pc_i  (except_pc_i),
      .res_i        (res_i),
      .pred_target_i(pred_i.target),
      .pred_taken_i(pred_i.taken),
      .fetch_ready_i(fetch_ready_o),
      .pc_o         (pc_o)
  );

  // If the flush is caused by a misprediction,
  // there no need to flush the BPU, just update it
  assign pred_o = pred_i;

endmodule
