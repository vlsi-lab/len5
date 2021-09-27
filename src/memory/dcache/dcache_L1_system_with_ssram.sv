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
// File: dcache_L1_system_with_ssram.sv
// Author: Matteo Perotti
// Date: 21/10/2019
// Description: L1 data cache top module

import memory_pkg::*;

module dcache_L1_system_with_ssram
(
  // Main
  input  logic          clk_i,
  input  logic          rst_ni,
  input  logic          clr_i,              // Clear MSHR and other regs (synch clear)
  // Reset Block -> D-Cache
  input  var rst_l1dc_req_t rst_l1dc_req_i,     // Initial reset request
  // L2-Update -> D-Cache
  input  var upd_l1dc_req_t upd_l1dc_req_i,     // UpdateL2 block request
  // D-Cache -> L2-Update
  output logic          en_cnt_o,           // Address the next set
  output logic          wbb_empty_o,        // end of the synchronization
  // LSQ -> D-Cache
  input  var lsq_l1dc_req_t lsq_l1dc_req_i,     // LSQ request to the D-Cache
  output logic          l1dc_lsq_req_rdy_o,
  // D-Cache -> LSQ
  output l1dc_lsq_ans_t l1dc_lsq_ans_o,     // D-Cache answer to LSQ
  output l1dc_lsq_wup_t l1dc_lsq_wup_o,     // D-Cache wake-up signal to LSQ
  // D-Cache -> L2-Cache
  output l1dc_l2c_req_t l1dc_l2c_req_o,     // D-Cache request to L2-Cache
  input  logic          l2c_l1dc_req_rdy_i,
  // L2-Cache -> D-Cache
  input  var l2c_l1dc_ans_t l2c_l1dc_ans_i,     // L2-Cache answer to D-Cache
  output logic          l1dc_l2c_ans_rdy_o
);

  localparam N_WAY         = DCACHE_L1_ASSOCIATIVITY;
  localparam MEM_ADDR_LEN  = DCACHE_L1_IDX_A_LEN;
  localparam CACHE_LINES   = 2**MEM_ADDR_LEN;         // Number of lines of each cache block
  localparam TVD_WORD_LEN  = DCACHE_L1_TAG_A_LEN + 2; // Tag + Valid bit + Dirty bit
  localparam DATA_WORD_LEN = DCACHE_L1_LINE_LEN;      // The length of a line

  // Memory Interface
  dcache_addr_t           dcache_addr;
  tmem_ctrl_t [N_WAY-1:0] tmem_ctrl_vec;
  dmem_ctrl_t [N_WAY-1:0] dmem_ctrl_vec;
  tvd_mem_line_t          dcache_wtvd;
  dcache_line_t           dcache_wdata;
  tvd_mem_line_t          tvd_mem_out_vec [N_WAY];
  dcache_line_t           data_mem_out_vec [N_WAY];

  //----------------------\\
  // Cache Infrastructure \\
  //----------------------\\

  dcache_L1_system i_dcache_L1_system (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_i(clr_i),
    .rst_l1dc_req_i(rst_l1dc_req_i),
    .upd_l1dc_req_i(upd_l1dc_req_i),
    .en_cnt_o(en_cnt_o),
    .wbb_empty_o(wbb_empty_o),
    .lsq_l1dc_req_i(lsq_l1dc_req_i),
    .l1dc_lsq_req_rdy_o(l1dc_lsq_req_rdy_o),
    .l1dc_lsq_ans_o(l1dc_lsq_ans_o),
    .l1dc_lsq_wup_o(l1dc_lsq_wup_o),
    .l1dc_l2c_req_o(l1dc_l2c_req_o),
    .l2c_l1dc_req_rdy_i(l2c_l1dc_req_rdy_i),
    .l2c_l1dc_ans_i(l2c_l1dc_ans_i),
    .l1dc_l2c_ans_rdy_o(l1dc_l2c_ans_rdy_o),
    .dcache_addr_o(dcache_addr),
    .tmem_ctrl_vec_o(tmem_ctrl_vec),
    .dmem_ctrl_vec_o(dmem_ctrl_vec),
    .dcache_wtvd_o(dcache_wtvd),
    .dcache_wdata_o(dcache_wdata),
    .tvd_mem_out_vec_i(tvd_mem_out_vec),
    .data_mem_out_vec_i(data_mem_out_vec)
  );

  //----------------\\
  // PHYSICAL CACHE \\
  //----------------\\

  // Physical ssram memory for TAG, VALID BIT, DIRTY BIT
  for (genvar k = 0; k < N_WAY; k++) begin : tag_valid_dirty_ssram
    ssram #(
      .NUM_WORDS(CACHE_LINES),
      .DATA_LEN(TVD_WORD_LEN)
    ) i_tag_ssram (
      .clk_i(clk_i),
      .cs_i(tmem_ctrl_vec[k].cs),
      .we_i(tmem_ctrl_vec[k].we),
      .be_i(tmem_ctrl_vec[k].be),
      .addr_i(dcache_addr),
      .wdata_i(dcache_wtvd),
      .rdata_o(tvd_mem_out_vec[k])
    );
  end

  // Physical ssram memory for DATA
  for (genvar k = 0; k < N_WAY; k++) begin : data_ssram
    ssram #(
      .NUM_WORDS(CACHE_LINES),
      .DATA_LEN(DATA_WORD_LEN)
    ) i_tag_ssram (
      .clk_i(clk_i),
      .cs_i(dmem_ctrl_vec[k].cs),
      .we_i(dmem_ctrl_vec[k].we),
      .be_i(dmem_ctrl_vec[k].be),
      .addr_i(dcache_addr),
      .wdata_i(dcache_wdata),
      .rdata_o(data_mem_out_vec[k])
    );
  end

endmodule
