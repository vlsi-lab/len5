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
// File: dcache_L1_system.sv
// Author: Matteo Perotti
// Date: 21/10/2019
// Description: L1 data cache top module without ssram

import memory_pkg::*;

module dcache_L1_system
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
  output logic          l1dc_l2c_ans_rdy_o,
  // Memory Interface
  output dcache_addr_t                             dcache_addr_o,
  output tmem_ctrl_t [DCACHE_L1_ASSOCIATIVITY-1:0] tmem_ctrl_vec_o,
  output dmem_ctrl_t [DCACHE_L1_ASSOCIATIVITY-1:0] dmem_ctrl_vec_o,
  output tvd_mem_line_t                            dcache_wtvd_o,
  output dcache_line_t                             dcache_wdata_o,
  input  var tvd_mem_line_t                            tvd_mem_out_vec_i [DCACHE_L1_ASSOCIATIVITY],
  input  var dcache_line_t                             data_mem_out_vec_i [DCACHE_L1_ASSOCIATIVITY]
);

  // d0 -> d1 and d1 -> d0 signals
  d1_d0_req_t d1_d0_req;
  d0_d1_req_t d0_d1_req;
  logic       d1_d0_req_rdy;
  logic       d1_d0_stalled;

  //----\\
  // d0 \\
  //----\\

  // Block before the physical memory (it contains the physical memory too)
  dcache_L1_d0 i_dcache_L1_d0 (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_i(clr_i),
    .rst_l1dc_req_i(rst_l1dc_req_i),
    .upd_l1dc_req_i(upd_l1dc_req_i),
    .lsq_l1dc_req_i(lsq_l1dc_req_i),
    .l1dc_lsq_req_rdy_o(l1dc_lsq_req_rdy_o),
    .l2c_l1dc_ans_i(l2c_l1dc_ans_i),
    .l1dc_l2c_ans_rdy_o(l1dc_l2c_ans_rdy_o),
    .l1dc_lsq_wup_o(l1dc_lsq_wup_o),
    .d1_d0_req_i(d1_d0_req),
    .d0_d1_req_o(d0_d1_req),
    .d1_d0_req_rdy_i(d1_d0_req_rdy),
    .d1_d0_stalled_i(d1_d0_stalled),
    .dcache_addr_o(dcache_addr_o),
    .tmem_ctrl_vec_o(tmem_ctrl_vec_o),
    .dmem_ctrl_vec_o(dmem_ctrl_vec_o),
    .dcache_wtvd_o(dcache_wtvd_o),
    .dcache_wdata_o(dcache_wdata_o),
    .tvd_mem_out_vec_i(tvd_mem_out_vec_i),
    .data_mem_out_vec_i(data_mem_out_vec_i)
  );

  //----\\
  // d1 \\
  //----\\

  // Block after the physical memory
  dcache_L1_d1 i_dcache_L1_d1 (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_i(clr_i),
    .d0_d1_req_i(d0_d1_req),
    .d1_d0_req_rdy_o(d1_d0_req_rdy),
    .d1_d0_stalled_o(d1_d0_stalled),
    .d1_d0_req_o(d1_d0_req),
    .l1dc_lsq_ans_o(l1dc_lsq_ans_o),
    .l1dc_l2c_req_o(l1dc_l2c_req_o),
    .l2c_l1dc_req_rdy_i(l2c_l1dc_req_rdy_i),
    .l1dc_upd_cnt_en_o(en_cnt_o),
    .wbb_empty_o(wbb_empty_o)
  );

endmodule
