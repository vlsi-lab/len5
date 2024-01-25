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
// File: icache_L1.sv
// Author: Matteo Perotti
// Date: 30/10/2019

import len5_pkg::*;
import memory_pkg::*;


module icache_L1 (
  // main
  input logic                   clk_i,       // main clock
  input logic                   rst_ni,      // main reset signal
  // ctrl
  input logic                   flush_i,     // flush the whole cache
  input logic                   abort_i,     // abort current operation
  // front-end
  input frontend_icache_req_t  ireq_i,      // incoming front-end instruction request channel
  output logic                  ready_o,     // ready for a front-end request
  output icache_frontend_ans_t  iresp_o,     // i-cache instruction response channel
  // TLB
  output icache_tlb_req_t       tlb_areq_o,  // address translation request to i-TLB
  input  logic                  tlb_ready_i, // TLB is ready for a request
  input tlb_icache_ans_t       tlb_aresp_i, // i-TLB response channel
  // L2-arbiter
  output icache_l2_req_t        l2_req_o,    // request channel to L2-arbiter
  input  logic                  l2_ready,    // l2 level can accept requests
  input l2_icache_ans_t        l2_resp_i,   // response channel from L2-arbiter
  // Memory Interface
  output icache_mem_ctrl_t                              mem_ctrl_o,
  output icache_idx_addr_t                              cache_addr_o,
  output icache_L1_vtag_t [ICACHE_L1_ASSOCIATIVITY-1:0] vtag_vec_in_o,
  input icache_mem_out_t                               mem_out_i
);

  // vaddr registers The address is "virtual" only if the virtual memory is on
  logic                                          vaddr_reg_en;     // vaddr regs enable
  icache_L1_addr_t                               vaddr_d, vaddr_q; // Input address and sampled one.
  // Tag register. Used when a line replacement occurs.
  logic                                          tag_reg_en;
  icache_L1_tag_t                                tag_q;
  // Cache control signals
  icache_idx_addr_t                              cache_addr;
  icache_mem_ctrl_t                              mem_ctrl;
  // Cache data in
  logic                                          valid_bit;
  icache_L1_vtag_t [ICACHE_L1_ASSOCIATIVITY-1:0] vtag_vec_in;
  // Cache data out
  icache_mem_out_t                               mem_out;
  icache_L1_vtag_t [ICACHE_L1_ASSOCIATIVITY-1:0] vtag_vec_out;
  // From Comparison Block
  logic                                          cache_hit;
  // To select the cache data source
  icache_addr_src_e                              addr_src;
  // From the flush counter
  icache_idx_addr_t                              flush_addr;
  // CU
  icache_ctrl_e                                  conditional_ctrl;
  logic                                          flushing;
  logic                                          comparing;
  logic                                          replaying;
  logic                                          waiting_tlb;
  logic                                          waiting_l2c;
  logic                                          is_last_set;
  logic                                          is_exception;
  // From the combinatorial ctrl block
  logic                                          mem_ctrl_en;
  // From the replacement block
  icache_replace_vec_t                           replace_vec;
  // To the replacement block
  logic                                          update_replacement;

  //----------------\\
  // VADDR REGISTER \\
  //----------------\\

  assign vaddr_d = ireq_i.vaddr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      vaddr_q <= '0;
    end else if (abort_i) begin
      vaddr_q <= '0;
    end else if (vaddr_reg_en) begin
      vaddr_q <= vaddr_d;
    end
  end

  assign tlb_areq_o.vaddr = vaddr_q;
  assign iresp_o.vaddr    = vaddr_q;

  //--------\\
  // SSRAM  \\
  //--------\\

  // Memory Interface
  assign mem_ctrl_o    = mem_ctrl;
  assign cache_addr_o  = cache_addr;
  assign vtag_vec_in_o = vtag_vec_in;
  assign mem_out       = mem_out_i;

  always_comb begin
    for (int k = 0; k < ICACHE_L1_ASSOCIATIVITY; k++) begin
      vtag_vec_in[k] = {tag_q, valid_bit};
    end
  end

  //------------------\\
  // COMPARISON BLOCK \\
  //------------------\\

  icache_comparison_block i_icache_comparison_block (
    .mem_out_i(mem_out),
    .tag_i(tlb_aresp_i.paddr.tag),
    .hit_o(cache_hit),
    .line_o(iresp_o.line)
  );

  //---------------\\
  // FLUSH COUNTER \\
  //---------------\\

  icache_flush_cnt i_icache_flush_cnt (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .flushing_i(flushing),
    .flush_addr_o(flush_addr),
    .last_set_to_flush_o(is_last_set)
  );

  //----\\
  // CU \\
  //----\\

  assign is_exception = (tlb_aresp_i.exception != NoException) ? 1'b1 : 1'b0;

  icache_moore_cu i_icache_moore_cu (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .flush_i(flush_i),
    .abort_op_i(abort_i),
    .is_last_set_i(is_last_set),
    .cache_hit_i(cache_hit),
    .fend_req_valid_i(ireq_i.valid),
    .itlb_rdy_i(tlb_ready_i),
    .itlb_hit_i(tlb_aresp_i.hit),
    .is_exception_i(is_exception),
    .l2c_req_rdy_i(l2_ready),
    .l2c_ans_valid_i(l2_resp_i.valid),
    .flushing_o(flushing),
    .comparing_o(comparing),
    .replaying_o(replaying),
    .waiting_tlb_o(waiting_tlb),
    .waiting_l2c_o(waiting_l2c),
    .icache_addr_src_o(addr_src),
    .icache_cond_ctrl_o(conditional_ctrl),
    .l2c_req_valid_o(l2_req_o.valid),
    .itlb_req_valid_o(tlb_areq_o.valid)
  );

  //----------------\\
  // MEMORY CONTROL \\
  //----------------\\

  icache_mem_ctrl i_icache_mem_ctrl (
    .cond_ctrl_i(conditional_ctrl),
    .mem_ctrl_en_i(mem_ctrl_en),
    .replace_vec_i(replace_vec),
    .mem_ctrl_o(mem_ctrl)
  );

  //----------------\\
  // DATA SEL BLOCK \\
  //----------------\\

  icache_data_sel i_icache_data_sel (
    .icache_addr_src_i(addr_src),
    .vaddr_d_i(vaddr_d),
    .vaddr_q_i(vaddr_q),
    .flush_addr_i(flush_addr),
    .icache_addr_o(cache_addr),
    .icache_valid_bit_o(valid_bit)
  );

  //----------------------\\
  // CONTROL ENABLE BLOCK \\
  //----------------------\\

  icache_ctrl_en i_icache_ctrl_en (
    .icache_cond_ctrl_i(conditional_ctrl),
    .comparing_i(comparing),
    .replaying_i(replaying),
    .waiting_tlb_i(waiting_tlb),
    .waiting_l2c_i(waiting_l2c),
    .cache_hit_i(cache_hit),
    .itlb_hit_i(tlb_aresp_i.hit),
    .itlb_exception_i(tlb_aresp_i.exception),
    .itlb_rdy_i(tlb_ready_i),
    .l2c_req_rdy_i(l2_ready),
    .l2c_ans_valid_i(l2_resp_i.valid),
    .fend_icache_valid_i(ireq_i.valid),
    .icache_cond_ctrl_en_o(mem_ctrl_en),
    .icache_fend_req_rdy_o(ready_o),
    .icache_fend_ans_valid_o(iresp_o.valid),
    .update_replacement_o(update_replacement),
    .vaddr_reg_en_o(vaddr_reg_en),
    .tag_reg_en_o(tag_reg_en)
  );

  //-------------------\\
  // REPLACEMENT BLOCK \\
  //-------------------\\

  icache_replacement_block i_icache_replacement_block (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .valid_vec_i(mem_out.valid_vec),
    .update_replacement_i(update_replacement),
    .replace_vec_o(replace_vec)
  );

  //--------------\\
  // TAG REGISTER \\
  //--------------\\

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tag_q <= '0;
    end else if (abort_i) begin
      tag_q <= '0;
    end else if (tag_reg_en) begin
      tag_q <= tlb_aresp_i.paddr.tag;
    end
  end

  //----------------------------\\
  // OTHER INTERFACE ASSIGNMENT \\
  //----------------------------\\

  assign iresp_o.exception  = tlb_aresp_i.exception;
  assign l2_req_o.line_addr = {vaddr_q.tag, vaddr_q.idx};

endmodule
