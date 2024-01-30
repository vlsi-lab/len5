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

module fetch_stage #(
  parameter int unsigned HLEN = 4,
  parameter int unsigned BTB_BITS = 4,
  parameter int unsigned BOOT_PC = 64'h0,
  parameter c2b_t INIT_C2B = WNT,
  parameter int unsigned MEMIF_FIFO_DEPTH = 2  // equal to the max number of outstanding requests the memory can accept
) (
  input logic clk_i,
  input logic rst_n_i,
  input logic flush_i,
  input logic flush_bpu_i,

  // From/to memory
  input  logic                            instr_valid_i,
  input  logic                            instr_ready_i,
  output logic                            instr_ready_o,
  output logic                            instr_valid_o,
  output logic                            instr_we_o,
  input  logic         [        XLEN-1:0] instr_rdata_i,        // old: ins_mem_ans_i.value
  input  logic         [BUFF_IDX_LEN-1:0] instr_tag_i,          // old: ins_mem_ans_i.tag
  output logic         [        XLEN-1:0] instr_addr_o,         // old: ins_mem_req_o.addr
  output logic         [BUFF_IDX_LEN-1:0] instr_tag_o,          // old: ins_mem_req_o.tag
  input  logic                            instr_except_raised,
  input  except_code_t                    instr_except_code,

  // From/to instruction decode
  input  logic         issue_ready_i,
  output logic         issue_valid_o,
  output instr_t       issue_instr_o,
  output prediction_t  issue_pred_o,
  output logic         issue_except_raised_o,
  output except_code_t issue_except_code_o,

  // From branch unit
  output logic        bu_ready_o,
  input  logic        bu_res_valid_i,
  input  resolution_t bu_res_i,

  // From commit unit
  input logic            comm_except_raised_i,
  input logic [XLEN-1:0] comm_except_pc_i
);

  // INTERNAL SIGNALS
  // ----------------

  // Current program counter
  logic        [XLEN-1:0] curr_pc;
  prediction_t            curr_pred;

  // Memory Interface <--> PC generator
  logic                   memif_pcgen_ready;
  logic                   pcgen_memif_valid;

  // -------
  // MODULES
  // -------

  // BPU      \
    //           }  MEMORY INTERFACE > ISSUE STAGE
    // PC GEN   /

    // TODO: add return-address stack for jumps/branches according to specs
    // Section 2.5.

    // BRANCH PREDICTION UNIT
    // ----------------------
    // NOTE: the prediction is provided in the same cycle as the PC, so no
    //       synchronization is required.
    bpu #(
    .HLEN    (HLEN),
    .BTB_BITS(BTB_BITS),
    .INIT_C2B(INIT_C2B)
  ) u_bpu (
    .clk_i         (clk_i),
    .rst_n_i       (rst_n_i),
    .flush_i       (flush_bpu_i),
    .curr_pc_i     (curr_pc),
    .bu_res_valid_i(bu_res_valid_i),
    .bu_res_i      (bu_res_i),
    .pred_o        (curr_pred)
  );

  // PC GENERATOR
  // ------------
  pc_gen #(
    .BOOT_PC(BOOT_PC)
  ) u_pc_gen (
    .clk_i               (clk_i),
    .rst_n_i             (rst_n_i),
    .comm_except_raised_i(comm_except_raised_i),
    .comm_except_pc_i    (comm_except_pc_i),
    .bu_res_valid_i      (bu_res_valid_i),
    .bu_res_i            (bu_res_i),
    .pred_i              (curr_pred),
    .mem_ready_i         (memif_pcgen_ready),
    .valid_o             (pcgen_memif_valid),
    .bu_ready_o          (bu_ready_o),
    .pc_o                (curr_pc)
  );

  // MEMORY INTERFACE
  // ----------------
  fetch_mem_if #(
    .MAX_MEM_OUTSTANDING_REQUESTS(MEMIF_FIFO_DEPTH)
  ) u_mem_if (
    .clk_i                (clk_i),
    .rst_n_i              (rst_n_i),
    .flush_i              (flush_i),
    .fetch_valid_i        (pcgen_memif_valid),
    .fetch_ready_o        (memif_pcgen_ready),
    .fetch_pred_i         (curr_pred),
    .issue_valid_o        (issue_valid_o),
    .issue_ready_i        (issue_ready_i),
    .issue_instr_o        (issue_instr_o),
    .issue_pred_o         (issue_pred_o),
    .issue_except_raised_o(issue_except_raised_o),
    .issue_except_code_o  (issue_except_code_o),
    .instr_valid_i        (instr_valid_i),
    .instr_ready_i        (instr_ready_i),
    .instr_ready_o        (instr_ready_o),
    .instr_valid_o        (instr_valid_o),
    .instr_we_o           (instr_we_o),
    .instr_rdata_i        (instr_rdata_i),
    .instr_tag_i          (instr_tag_i),
    .instr_addr_o         (instr_addr_o),
    .instr_tag_o          (instr_tag_o),
    .instr_except_raised_i(instr_except_raised),
    .instr_except_code    (instr_except_code)
  );

endmodule
