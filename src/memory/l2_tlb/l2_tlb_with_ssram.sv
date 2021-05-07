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
// File: l2_tlb_with_ssram.sv
// Author: Matteo Perotti
// Date: 30/11/2019
// Description: L2-TLB with the physical SSRAM

import memory_pkg::*;
import len5_pkg::*;
//import mmm_pkg::*;


module l2_tlb_with_ssram
(
  // Main
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             clr_mshr_i,
  input  logic             abort_i,
  // From CSR
  input  logic             sum_bit_i,      // For U bit access permissions check. Neglected for isntruction checks
  input  logic             mxr_bit_i,      // Executable pages can become Readable
  input  priv_e            priv_mode_i,    // The actual privilege mode (NOT filtered by the MPRV BIT!!)
  input  priv_e            priv_mode_ls_i, // The actual privilege mode (filtered by the MPRV BIT!!)
  input  asid_t            base_asid_i,    // Actual ASID from "satp" register
  // Flush control
  input  tlb_flush_e       flush_type_i,   // External flush request to the L2 TLB flush unit
  input  asid_t            flush_asid_i,
  input  var vpn_t             flush_page_i,
  // (L1 TLB Arbiter -> L2 TLB) request channel
  input  var l1tlb_l2tlb_req_t l1tlb_l2tlb_req_i,
  output logic             l2tlb_l1tlb_req_rdy_o,
  // (L2 TLB -> PTW) request channel
  output l2tlb_ptw_req_t   l2tlb_ptw_req_o,
  input  logic             ptw_l2tlb_req_rdy_i,
  // (PTW -> L2 TLB) answer channel
  input  var ptw_l2tlb_ans_t   ptw_l2tlb_ans_i,
  output logic             l2tlb_ptw_ans_rdy_o,
  // (L2 TLB -> L1 TLB Arbiter) answer channel
  output l2tlb_l1tlb_ans_t l2tlb_l1tlb_ans_o
);

  localparam N_SETS_TLB  = L2_TLB_ENTRIES / L2_TLB_ASSOCIATIVITY;
  localparam N_WAY       = L2_TLB_ASSOCIATIVITY;
  localparam TMEM_LEN    = L2_TLB_TAG_ENTRY_LEN;
  localparam IDX_LEN     = L2_TLB_IDX_LEN;

  // MEMORY interface
  l2tlb_dmem_ctrl_t   data_mem_ctrl [N_WAY];
  l2tlb_tmem_ctrl_t   tag_mem_ctrl [N_WAY];
  logic [IDX_LEN-1:0] tlb_addr;
  l2tlb_t_entry_t     tlb_input_entry_tag;
  logic [PPN_LEN-1:0] tlb_input_entry_data;
  l2tlb_t_entry_t     tlb_output_entry_vec_tag  [N_WAY];
  logic [PPN_LEN-1:0] tlb_output_entry_vec_data [N_WAY];

  // L2 TLB unit
  l2_tlb i_l2_tlb (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_mshr_i(clr_mshr_i),
    .abort_i(abort_i),
    .sum_bit_i(sum_bit_i),
    .mxr_bit_i(mxr_bit_i),
    .priv_mode_i(priv_mode_i),
    .priv_mode_ls_i(priv_mode_ls_i),
    .base_asid_i(base_asid_i),
    .flush_type_i(flush_type_i),
    .flush_asid_i(flush_asid_i),
    .flush_page_i(flush_page_i),
    .l1tlb_l2tlb_req_i(l1tlb_l2tlb_req_i),
    .l2tlb_l1tlb_req_rdy_o(l2tlb_l1tlb_req_rdy_o),
    .l2tlb_ptw_req_o(l2tlb_ptw_req_o),
    .ptw_l2tlb_req_rdy_i(ptw_l2tlb_req_rdy_i),
    .ptw_l2tlb_ans_i(ptw_l2tlb_ans_i),
    .l2tlb_ptw_ans_rdy_o(l2tlb_ptw_ans_rdy_o),
    .l2tlb_l1tlb_ans_o(l2tlb_l1tlb_ans_o),
    .tag_mem_ctrl_o(tag_mem_ctrl),
    .tlb_addr_o(tlb_addr),
    .data_mem_ctrl_o(data_mem_ctrl),
    .tlb_input_entry_tag_o(tlb_input_entry_tag),
    .tlb_input_entry_data_o(tlb_input_entry_data),
    .tlb_output_entry_vec_tag_i(tlb_output_entry_vec_tag),
    .tlb_output_entry_vec_data_i(tlb_output_entry_vec_data)
  );

  // TAG Memory
  for (genvar k = 0; k < N_WAY; k++) begin : l2_tlb_tag_part
    ssram #(
      .NUM_WORDS(N_SETS_TLB),
      .DATA_LEN(TMEM_LEN)
    ) i_l2_tlb_t_ssram (
      .clk_i(clk_i),
      .cs_i(tag_mem_ctrl[k].cs),
      .we_i(tag_mem_ctrl[k].we),
      .be_i(tag_mem_ctrl[k].be),
      .addr_i(tlb_addr),
      .wdata_i(tlb_input_entry_tag),
      .rdata_o(tlb_output_entry_vec_tag[k])
    );
  end

  // DATA Memory
  for (genvar k = 0; k < N_WAY; k++) begin : l2_tlb_data_part
    ssram #(
      .NUM_WORDS(N_SETS_TLB),
      .DATA_LEN(PPN_LEN)
    ) i_l2_tlb_d_ssram (
      .clk_i(clk_i),
      .cs_i(data_mem_ctrl[k].cs),
      .we_i(data_mem_ctrl[k].we),
      .be_i(data_mem_ctrl[k].be),
      .addr_i(tlb_addr),
      .wdata_i(tlb_input_entry_data),
      .rdata_o(tlb_output_entry_vec_data[k])
    );
  end

endmodule
