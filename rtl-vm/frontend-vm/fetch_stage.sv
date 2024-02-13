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

module fetch_stage #(
    parameter HLEN = 4,
    parameter BTB_BITS = 4
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,

    // From/to PC gen stage
    input  logic [len5_pkg::XLEN-1:0] pc_i,
    output logic            fetch_ready_o,

    // From/to i-cache
    output logic        [XLEN-1:0] addr_o,
    output logic                   addr_valid_o,
    input  logic                   addr_ready_i,
    input  icache_out_t            data_i,
    input  logic                   data_valid_i,
    output logic                   data_ready_o,

    // From/to instruction decode
    input  logic                   issue_ready_i,
    output logic                   issue_valid_o,
    output logic        [ILEN-1:0] instruction_o,
    output logic        [XLEN-1:0] curr_pc_o,
    output prediction_t            pred_o,

    // From Icache
    input icache_frontend_ans_t icache_frontend_ans_i,

    // To backend
    output logic except_o,
    //output except_code_t except_code_o,
    output except_code_t except_code_o,

    // From branch unit (ex stage)
    input resolution_t res_i
);

  // Signal declarations
  logic read_req, read_done, bpu_flush;
  icache_out_t cache_out;

  // -----------------
  // I-cache interface
  // -----------------
  icache_ifc u_icache_ifc (
      .clk_i  (clk_i),
      .rst_n_i(rst_n_i),
      .flush_i(flush_i),

      // From/to IF
      .pc_i       (pc_i),
      .read_req_i (read_req),
      .cache_out_o(cache_out),
      .read_done_o(read_done),

      // From/to icache
      .addr_o      (addr_o),
      .addr_valid_o(addr_valid_o),
      .addr_ready_i(addr_ready_i),
      .data_i      (data_i),
      .data_valid_i(data_valid_i),
      .data_ready_o(data_ready_o)
  );

  // ----------
  // Fetch unit
  // ----------
  ifu u_ifu (
      .clk_i  (clk_i),
      .rst_n_i(rst_n_i),
      .flush_i(flush_i),

      // From/to PC gen
      .pc_i         (pc_i),
      .fetch_ready_o(fetch_ready_o),

      // From/to i-cache interface
      .cache_out_i(cache_out),
      .read_done_i(read_done),
      .read_req_o (read_req),

      .icache_frontend_ans_i(icache_frontend_ans_i),

      .except_o(except_o),
      .except_code_o(except_code_o),

      // From/to instruction decode
      .issue_ready_i(issue_ready_i),
      .issue_valid_o(issue_valid_o),
      .instruction_o(instruction_o),
      .curr_pc_o    (curr_pc_o)
  );

  // ---------
  //    BPU
  // ---------
  bpu #(
      .HLEN    (HLEN),
      .BTB_BITS(BTB_BITS)
  ) u_bpu (
      .clk_i  (clk_i),
      .rst_n_i(rst_n_i),
      .flush_i(bpu_flush),
      .pc_i   (pc_i),
      .res_i  (res_i),

      .pred_o(pred_o)
  );

  // If the flush is caused by a misprediction,
  // there no need to flush the BPU, just update it
  assign bpu_flush = flush_i & ~res_i.mispredict;

endmodule
