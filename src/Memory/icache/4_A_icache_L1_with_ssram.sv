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
// File: icache_L1_with_ssram.sv
// Author: Matteo Perotti
// Date: 30/11/2019

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/len5_pkg.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/memory_pkg.sv"
//import mmm_pkg::*;
import len5_pkg::*;
import memory_pkg::*;

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/icache/3_A_icache_L1.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/util/ssram.sv"

module icache_L1_with_ssram (
  // main
  input logic                   clk_i,       // main clock
  input logic                   rst_ni,      // main reset signal
  // ctrl
  input logic                   flush_i,     // flush the whole cache
  input logic                   abort_i,     // abort current operation
  // front-end
  input  frontend_icache_req_t  ireq_i,      // incoming front-end instruction request channel
  output logic                  ready_o,     // ready for a front-end request
  output icache_frontend_ans_t  iresp_o,     // i-cache instruction response channel
  // TLB
  output icache_tlb_req_t       tlb_areq_o,  // address translation request to i-TLB
  input  logic                  tlb_ready_i, // TLB is ready for a request
  input  tlb_icache_ans_t       tlb_aresp_i, // i-TLB response channel
  // L2-arbiter
  output icache_l2_req_t        l2_req_o,    // request channel to L2-arbiter
  input  logic                  l2_ready,    // l2 level can accept requests
  input  l2_icache_ans_t        l2_resp_i    // response channel from L2-arbiter
);

  localparam NUM_WORDS     = 1 << ICACHE_L1_IDX_A_LEN;
  localparam VALID_TAG_LEN = 1 + ICACHE_L1_TAG_A_LEN; // valid bit + tag
  localparam LINE_LEN      = ICACHE_L1_LINE_LEN;

  // Memory interface
  icache_mem_ctrl_t                              mem_ctrl;
  icache_idx_addr_t                              cache_addr;
  icache_L1_vtag_t [ICACHE_L1_ASSOCIATIVITY-1:0] vtag_vec_in;
  icache_L1_vtag_t [ICACHE_L1_ASSOCIATIVITY-1:0] vtag_vec_out;
  icache_line_t                                  data_vec_out;
  icache_mem_out_t                               mem_out;

  icache_L1 i_icache_L1 (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .flush_i(flush_i),
    .abort_i(abort_i),
    .ireq_i(ireq_i),
    .ready_o(ready_o),
    .iresp_o(iresp_o),
    .tlb_areq_o(tlb_areq_o),
    .tlb_ready_i(tlb_ready_i),
    .tlb_aresp_i(tlb_aresp_i),
    .l2_req_o(l2_req_o),
    .l2_ready(l2_ready),
    .l2_resp_i(l2_resp_i),
    .mem_ctrl_o(mem_ctrl),
    .cache_addr_o(cache_addr),
    .vtag_vec_in_o(vtag_vec_in),
    .mem_out_i(mem_out)
  );

  for (genvar k = 0; k < ICACHE_L1_ASSOCIATIVITY; k++) begin : valid_tag_cache_block
    ssram #(
      .NUM_WORDS(NUM_WORDS),
      .DATA_LEN(VALID_TAG_LEN)
    ) vtag_ssram (
      .clk_i(clk_i),
      .cs_i(mem_ctrl.tvmem_vec[k].cs),
      .we_i(mem_ctrl.tvmem_vec[k].we),
      .be_i(mem_ctrl.tvmem_vec[k].be),
      .addr_i(cache_addr),
      .wdata_i(vtag_vec_in[k]),
      .rdata_o(vtag_vec_out[k])
    );
  end
  always_comb begin
    for (int k = 0; k < ICACHE_L1_ASSOCIATIVITY; k++) begin
      mem_out.valid_vec[k] = vtag_vec_out[k].valid;
      mem_out.tag_vec[k]   = vtag_vec_out[k].tag;
    end
  end

  for (genvar k = 0; k < ICACHE_L1_ASSOCIATIVITY; k++) begin : line_cache_block
    ssram #(
      .NUM_WORDS(NUM_WORDS),
      .DATA_LEN(LINE_LEN)
    ) data_ssram (
      .clk_i(clk_i),
      .cs_i(mem_ctrl.dmem_vec[k].cs),
      .we_i(mem_ctrl.dmem_vec[k].we),
      .be_i(mem_ctrl.dmem_vec[k].be),
      .addr_i(cache_addr),
      .wdata_i(l2_resp_i.line),
      .rdata_o(mem_out.data_vec[k])
    );
  end

endmodule
