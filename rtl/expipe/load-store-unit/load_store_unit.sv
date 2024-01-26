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
// File: load_store_unit.sv
// Author: Michele Caon
// Date: 15/07/2022

import len5_config_pkg::*;
import len5_pkg::BUFF_IDX_LEN;
import expipe_pkg::*;
import len5_pkg::*;
import memory_pkg::*;

/**
 * @brief	Bare-metal load-store unit.
 *
 * @details	This module contains the load and store buffers, and to each is
 *          associated an adder tpcompute the target memory address.
 *          It is meant to be directly attached to a memory
 */
module load_store_unit #(
  parameter LB_DEPTH = 4,
  parameter SB_DEPTH = 4
) (
  input logic clk_i,
  input logic rst_n_i,
  input logic mis_flush_i,
  input logic except_flush_i,

  /* Issue stage */
  input  logic                   issue_lb_valid_i,
  input  logic                   issue_sb_valid_i,
  output logic                   issue_lb_ready_o,
  output logic                   issue_sb_ready_o,
  input  ldst_width_t            issue_type_i,         // byte, halfword, ...
  input  op_data_t               issue_rs1_i,          // base address
  input  op_data_t               issue_rs2_i,          // data to store
  input  logic        [XLEN-1:0] issue_imm_i,          // offset
  input  rob_idx_t               issue_dest_rob_idx_i,

  /* Commit stage */
  input logic     comm_spec_instr_i,
  input rob_idx_t comm_rob_head_idx_i,

  /* Common data bus (CDB) */
  input  logic      cdb_valid_i,
  input  logic      cdb_lb_ready_i,
  input  logic      cdb_sb_ready_i,
  output logic      cdb_lb_valid_o,
  output logic      cdb_sb_valid_o,
  input  cdb_data_t cdb_data_i,
  output cdb_data_t cdb_lb_data_o,
  output cdb_data_t cdb_sb_data_o,

  /* Memory system */
  output logic                            mem_load_valid_o,
  input  logic                            mem_load_ready_i,
  input  logic                            mem_load_valid_i,
  output logic                            mem_load_ready_o,
  output logic                            mem_load_we_o,
  output logic         [        XLEN-1:0] mem_load_addr_o,
  output logic         [             3:0] mem_load_be_o,
  output logic         [BUFF_IDX_LEN-1:0] mem_load_tag_o,
  input  logic         [        XLEN-1:0] mem_load_rdata_i,
  input  logic         [BUFF_IDX_LEN-1:0] mem_load_tag_i,
  input  logic                            mem_load_except_raised_i,
  input  except_code_t                    mem_load_except_code_i,

  output logic                            mem_store_valid_o,
  input  logic                            mem_store_ready_i,
  input  logic                            mem_store_valid_i,
  output logic                            mem_store_ready_o,
  output logic                            mem_store_we_o,
  output logic         [        XLEN-1:0] mem_store_addr_o,
  output logic         [             3:0] mem_store_be_o,
  input  logic         [        XLEN-1:0] mem_store_wdata_o,
  output logic         [BUFF_IDX_LEN-1:0] mem_store_tag_o,
  input  logic         [BUFF_IDX_LEN-1:0] mem_store_tag_i,
  input  logic                            mem_store_except_raised_i,
  input  except_code_t                    mem_store_except_code_i
);
  localparam ST_IDX_W = $clog2(SB_DEPTH);
  localparam L0_TAG_W = XLEN - ST_IDX_W;

  // INTERNAL SIGNALS
  // ----------------

  // Load buffer <--> store buffer
  logic                    sb_lb_latest_valid;
  logic [STBUFF_TAG_W-1:0] sb_lb_latest_idx;
  logic                    sb_lb_oldest_completed;
  logic [STBUFF_TAG_W-1:0] sb_lb_oldest_idx;

  // Load/store buffer  <--> address adder
  logic lb_adder_valid, sb_adder_valid;
  logic lb_adder_ready, sb_adder_ready;
  logic adder_lb_valid, adder_sb_valid;
  logic adder_lb_ready, adder_sb_ready;
  adder_req_t lb_adder_req, sb_adder_req;
  adder_ans_t adder_lb_ans, adder_sb_ans;

  // Load-store buffers <--> level-zero cache control
`ifdef LEN5_STORE_LOAD_FWD_EN
  logic                sb_l0_valid;
  logic [    XLEN-1:0] sb_l0_addr;
  logic [ST_IDX_W-1:0] sb_l0_idx;
  logic [L0_TAG_W-1:0] sb_l0_tag;
  logic                sb_l0_cached;
  logic [         3:0] sb_l0_width;
  logic [    XLEN-1:0] sb_l0_value;
  logic [    XLEN-1:0] lb_l0_addr;
  logic [         3:0] lb_l0_width;
  logic [ST_IDX_W-1:0] l0_sb_idx;
  logic                l0_lb_valid;
  logic [    XLEN-1:0] l0_lb_value;
`endif  /* LEN5_STORE_LOAD_FWD_EN */

  // --------------
  // LSU SUBSYSTEMS
  // --------------

  // LOAD BUFFER
  // -----------
  load_buffer #(
    .DEPTH(LB_DEPTH)
  ) u_load_buffer (
    .clk_i                (clk_i),
    .rst_n_i              (rst_n_i),
    .flush_i              (mis_flush_i),
    .issue_valid_i        (issue_lb_valid_i),
    .issue_ready_o        (issue_lb_ready_o),
    .issue_type_i         (issue_type_i),
    .issue_rs1_i          (issue_rs1_i),
    .issue_imm_i          (issue_imm_i),
    .issue_dest_rob_idx_i (issue_dest_rob_idx_i),
    .cdb_valid_i          (cdb_valid_i),
    .cdb_ready_i          (cdb_lb_ready_i),
    .cdb_valid_o          (cdb_lb_valid_o),
    .cdb_data_i           (cdb_data_i),
    .cdb_data_o           (cdb_lb_data_o),
    .sb_latest_valid_i    (sb_lb_latest_valid),
    .sb_latest_idx_i      (sb_lb_latest_idx),
    .sb_oldest_completed_i(sb_lb_oldest_completed),
    .sb_oldest_idx_i      (sb_lb_oldest_idx),
    .adder_valid_i        (adder_lb_valid),
    .adder_ready_i        (adder_lb_ready),
    .adder_valid_o        (lb_adder_valid),
    .adder_ready_o        (lb_adder_ready),
    .adder_ans_i          (adder_lb_ans),
    .adder_req_o          (lb_adder_req),
`ifdef LEN5_STORE_LOAD_FWD_EN
    .l0_valid_i           (l0_lb_valid),
    .l0_value_i           (l0_lb_value),
`endif  /* LEN5_STORE_LOAD_FWD_EN */
    .mem_valid_o          (mem_load_valid_o),
    .mem_ready_i          (mem_load_ready_i),
    .mem_valid_i          (mem_load_valid_i),
    .mem_ready_o          (mem_load_ready_o),
    .mem_we_o             (mem_load_we_o),
    .mem_addr_o           (mem_load_addr_o),
    .mem_be_o             (mem_load_be_o),
    .mem_tag_o            (mem_load_tag_o),
    .mem_rdata_i          (mem_load_rdata_i),
    .mem_tag_i            (mem_load_tag_i),
    .mem_except_raised_i  (mem_load_except_raised_i),
    .mem_except_code_i    (mem_load_except_code_i)
  );

  // STORE BUFFER
  // ------------
  store_buffer #(
    .DEPTH(SB_DEPTH)
  ) u_store_buffer (
    .clk_i                (clk_i),
    .rst_n_i              (rst_n_i),
    .flush_i              (mis_flush_i),
    .issue_valid_i        (issue_sb_valid_i),
    .issue_ready_o        (issue_sb_ready_o),
    .issue_type_i         (issue_type_i),
    .issue_rs1_i          (issue_rs1_i),
    .issue_rs2_i          (issue_rs2_i),
    .issue_imm_i          (issue_imm_i),
    .issue_dest_rob_idx_i (issue_dest_rob_idx_i),
    .comm_spec_instr_i    (comm_spec_instr_i),
    .comm_rob_head_idx_i  (comm_rob_head_idx_i),
    .cdb_valid_i          (cdb_valid_i),
    .cdb_ready_i          (cdb_sb_ready_i),
    .cdb_valid_o          (cdb_sb_valid_o),
    .cdb_data_i           (cdb_data_i),
    .cdb_data_o           (cdb_sb_data_o),
    .lb_latest_valid_o    (sb_lb_latest_valid),
    .lb_latest_idx_o      (sb_lb_latest_idx),
    .lb_oldest_completed_o(sb_lb_oldest_completed),
    .lb_oldest_idx_o      (sb_lb_oldest_idx),
    .adder_valid_i        (adder_sb_valid),
    .adder_ready_i        (adder_sb_ready),
    .adder_valid_o        (sb_adder_valid),
    .adder_ready_o        (sb_adder_ready),
    .adder_ans_i          (adder_sb_ans),
    .adder_req_o          (sb_adder_req),
`ifdef LEN5_STORE_LOAD_FWD_EN
    .l0_idx_i             (l0_sb_idx),
    .l0_tag_o             (sb_l0_tag),
    .l0_cached_o          (sb_l0_cached),
    .l0_width_o           (sb_l0_width),
    .l0_value_o           (sb_l0_value),
`endif  /* LEN5_STORE_LOAD_FWD_EN */
    .mem_valid_o          (mem_store_valid_o),
    .mem_ready_i          (mem_store_ready_i),
    .mem_valid_i          (mem_store_valid_i),
    .mem_ready_o          (mem_store_ready_o),
    .mem_we_o             (mem_store_we_o),
    .mem_addr_o           (mem_store_addr_o),
    .mem_be_o             (mem_store_be_o),
    .mem_wdata_o          (mem_store_wdata_o),
    .mem_tag_o            (mem_store_tag_o),
    .mem_tag_i            (mem_store_tag_i),
    .mem_except_raised_i  (mem_store_except_raised_i),
    .mem_except_code_i    (mem_store_except_code_i)
  );

  // LOAD ADDRESS ADDER
  // -------------
  address_adder u_address_adder_load (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .flush_i(mis_flush_i),
    .valid_i(lb_adder_valid),
    .ready_i(lb_adder_ready),
    .valid_o(adder_lb_valid),
    .ready_o(adder_lb_ready),
    .req_i  (lb_adder_req),
    .ans_o  (adder_lb_ans)
  );

  // STORE ADDRESS ADDER
  // -------------
  address_adder u_address_adder_store (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .flush_i(mis_flush_i),
    .valid_i(sb_adder_valid),
    .ready_i(sb_adder_ready),
    .valid_o(adder_sb_valid),
    .ready_o(adder_sb_ready),
    .req_i  (sb_adder_req),
    .ans_o  (adder_sb_ans)
  );

  // LEVEL-ZERO CACHE CONTROL
  // ------------------------
`ifdef LEN5_STORE_LOAD_FWD_EN  // TO-DO: Check if L0 works correctly
  assign sb_l0_valid = mem_store_valid_o & mem_store_ready_i;
  assign sb_l0_addr  = mem_store_addr_o;
  assign sb_l0_idx   = mem_store_tag_i;
  assign lb_l0_addr  = mem_load_addr_o;
  assign lb_l0_width = mem_load_be_o;
  l0_cache #(
    .STBUFF_DEPTH(SB_DEPTH)
  ) u_l0_cache (
    .clk_i      (clk_i),
    .rst_n_i    (rst_n_i),
    .flush_i    (except_flush_i),
    .st_valid_i (sb_l0_valid),
    .st_addr_i  (sb_l0_addr),
    .st_idx_i   (sb_l0_idx),
    .st_tag_i   (sb_l0_tag),
    .st_cached_i(sb_l0_cached),
    .st_width_i (sb_l0_width),
    .st_value_i (sb_l0_value),
    .ld_addr_i  (lb_l0_addr),
    .ld_width_i (lb_l0_width),
    .st_idx_o   (l0_sb_idx),
    .ld_valid_o (l0_lb_valid),
    .ld_value_o (l0_lb_value)
  );
`endif  /* LEN5_STORE_LOAD_FWD_EN */

endmodule
