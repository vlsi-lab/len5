// Copyright 2021 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: datapath.sv
// Author: Michele Caon
// Date: 19/11/2021

import len5_pkg::*;
import memory_pkg::*;
import fetch_pkg::*;
import csr_pkg::csr_priv_t;

module datapath #(
    parameter FETCH_MEMIF_FIFO_DEPTH = 2,
    parameter BOOT_PC = BOOT_PC
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_n_i,

    // Datapath <--> memory emulator
    output logic     mem_flush_o,

    input  logic     ins_mem_valid_i,
    input  logic     ins_mem_ready_i,
    output logic     ins_mem_valid_o,
    output logic     ins_mem_ready_o,
    input  mem_ans_t ins_mem_ans_i,
    output mem_req_t ins_mem_req_o,

    input  logic     data_mem_valid_i,
    input  logic     data_mem_ready_i,
    output logic     data_mem_valid_o,
    output logic     data_mem_ready_o,
    input  mem_ans_t data_mem_ans_i,
    output mem_req_t data_mem_req_o
);

  // ----------------
  // INTERNAL SIGNALS
  // ----------------

  // Frontend <--> backend
  // ---------------------
  logic                    fe_be_valid;
  logic                    be_fe_ready;
  logic         [ILEN-1:0] fe_be_instr;
  prediction_t             fe_be_pred;
  logic                    fe_be_except_raised;
  except_code_t            fe_be_except_code;
  logic                    be_fe_mis_flush;
  logic                    be_fe_bpu_flush;
  logic                    be_fe_res_valid;
  resolution_t             be_fe_res;
  logic                    be_fe_except_raised;
  logic         [XLEN-1:0] be_fe_except_pc;
  logic                    fe_be_comm_ready;

  // ---------
  // FRONT-END
  // ---------

  fetch_stage #(
      .HLEN             (HLEN                   ),
      .BTB_BITS         (BTB_BITS               ),
      .BOOT_PC          (BOOT_PC                ),
      .INIT_C2B         (INIT_C2B               ),
      .MEMIF_FIFO_DEPTH (FETCH_MEMIF_FIFO_DEPTH )
  ) u_fetch_stage (
      .clk_i                (clk_i),
      .rst_n_i              (rst_n_i),
      .flush_i              (be_fe_mis_flush),
      .flush_bpu_i          (be_fe_bpu_flush),
      .mem_valid_i          (ins_mem_valid_i),
      .mem_ready_i          (ins_mem_ready_i),
      .mem_valid_o          (ins_mem_valid_o),
      .mem_ready_o          (ins_mem_ready_o),
      .mem_ans_i            (ins_mem_ans_i),
      .mem_req_o            (ins_mem_req_o),
      .issue_ready_i        (be_fe_ready),
      .issue_valid_o        (fe_be_valid),
      .issue_instr_o        (fe_be_instr),
      .issue_pred_o         (fe_be_pred),
      .issue_except_raised_o(fe_be_except_raised),
      .issue_except_code_o  (fe_be_except_code),
      .comm_except_raised_i (be_fe_except_raised),
      .comm_except_pc_i     (be_fe_except_pc),
      .comm_res_valid_i     (be_fe_res_valid),
      .comm_res_i           (be_fe_res),
      .comm_ready_o         (fe_be_comm_ready)
  );

  // --------
  // BACK-END
  // --------

  backend u_backend (
      .clk_i                (clk_i),
      .rst_n_i              (rst_n_i),
      .fetch_valid_i        (fe_be_valid),
      .fetch_ready_i        (fe_be_comm_ready),
      .fetch_ready_o        (be_fe_ready),
      .fetch_instr_i        (fe_be_instr),
      .fetch_pred_i         (fe_be_pred),
      .fetch_except_raised_i(fe_be_except_raised),
      .fetch_except_code_i  (fe_be_except_code),
      .fetch_mis_flush_o    (be_fe_mis_flush),
      .fetch_bpu_flush_o    (be_fe_bpu_flush),
      .fetch_res_valid_o    (be_fe_res_valid),
      .fetch_res_o          (be_fe_res),
      .fetch_except_raised_o(be_fe_except_raised),
      .fetch_except_pc_o    (be_fe_except_pc),
      .mem_valid_i          (data_mem_valid_i),
      .mem_ready_i          (data_mem_ready_i),
      .mem_valid_o          (data_mem_valid_o),
      .mem_ready_o          (data_mem_ready_o),
      .mem_req_o            (data_mem_req_o),
      .mem_ans_i            (data_mem_ans_i)
  );

  // -------------
  // MEMORY-SYSTEM
  // -------------
  // NOTE: in the bare-metal version, the load-store unit and the fetch stage are
  // directly connected to the memory.

  // -----------------
  // OUTPUT EVALUATION
  // -----------------

  // Memory misprediction flush
  assign mem_flush_o = be_fe_mis_flush;

endmodule
