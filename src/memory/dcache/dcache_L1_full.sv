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

`include "memory_pkg.sv"
import memory_pkg::*;

`include "dcache_rst_block.sv"
`include "updateL2_block.sv"
`include "dcache_L1_system_with_ssram.sv"

module dcache_L1_full
(
  // Main
  input  logic          clk_i,
  input  logic          rst_ni,
  input  logic          clr_i,              // Clear MSHR and other regs (synch clear)
  
  // LSQ -> D-Cache
  input  lsq_l1dc_req_t lsq_l1dc_req_i,     // LSQ request to the D-Cache
  output logic          l1dc_lsq_req_rdy_o,

  // D-Cache -> LSQ
  output l1dc_lsq_ans_t l1dc_lsq_ans_o,     // D-Cache answer to LSQ
  output l1dc_lsq_wup_t l1dc_lsq_wup_o,     // D-Cache wake-up signal to LSQ

  // D-Cache -> L2-Cache
  output l1dc_l2c_req_t l1dc_l2c_req_o,     // D-Cache request to L2-Cache
  input  logic          l2c_l1dc_req_rdy_i,

  // L2-Cache -> D-Cache
  input  l2c_l1dc_ans_t l2c_l1dc_ans_i,     // L2-Cache answer to D-Cache
  output logic          l1dc_l2c_ans_rdy_o,

  // From the main system
  input  logic          synch_l1dc_l2c_i,
  output logic          l2c_update_done_o  // L2-Cache synch done
);

	// Definations
	rst_l1dc_req_t rst_l1dc_req_i;
	lsq_l1dc_req_t lsq_l1dc_req_i;
	logic          en_cnt_o;           // Address the next set
  	logic          wbb_empty_o;
	

dcache_L1_system_with_ssram u_dcache_L1_system_with_ssram
(
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
    .l1dc_l2c_ans_rdy_o(l1dc_l2c_ans_rdy_o)
);

dcache_rst_block #(.IDX_LEN(DCACHE_L1_IDX_A_LEN)) u_dcache_rst_block
(
  	.clk_i(clk_i),
    .rst_ni(rst_ni),
  	.rst_l1dc_req_o(rst_l1dc_req_i)
);

updateL2_block #(.IDX_LEN(DCACHE_L1_IDX_A_LEN)) u_updateL2_block
(
  	.clk_i(clk_i),
    .rst_ni(rst_ni),
  	.synch_l1dc_l2c_i(synch_l1dc_l2c_i), 
	.en_cnt_i(en_cnt_o),
    .wbb_empty_i(wbb_empty_o),
  	.upd_l1dc_req_o(upd_l1dc_req_i),   
  	.l2c_update_done_o(l2c_update_done_o)
);

endmodule
