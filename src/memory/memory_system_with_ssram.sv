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
// File: memory_system_with_ssram.sv
// Author: Matteo Perotti
// Date: 02/12/2019

`include "memory_pkg.sv"
`include "len5_pkg.sv"
import len5_pkg::*;
import memory_pkg::*;

`include "dcache/dcache_rst_block.sv"
`include "dtlb_L1.sv"
`include "tlb_arbiter.sv"
`include "l2c_arbiter.sv"
`include "mmu_cache.sv"
`include "updateL2_block.sv"
`include "itlb_L1.sv"
`include "dcache_L1_system_with_ssram.sv"
`include "l2_tlb_with_ssram.sv"
`include "ptw.sv"
`include "icache_L1_with_ssram.sv"

module memory_system_with_ssram
(
  // Main
  input  logic                 clk_i,
  input  logic                 rst_ni,
  // Flush Unit -> Memory System
  input  logic                 flush_i,
  input  logic                 abort_i,
  input  logic                 clr_l1tlb_mshr_i,
  input  logic                 clr_l2tlb_mshr_i,
  input  logic                 clear_dmshr_dregs_i,
  // Update Block <-> d-Cache Updating Unit
  input  logic                 synch_l1dc_l2c_i,
  output logic                 l2c_update_done_o,
  // System -> TLBs/PTW
  input  logic                 vmem_on_i,
  input  logic                 sum_bit_i,
  input  logic                 mxr_bit_i,
  input  priv_e                priv_mode_i,
  input  priv_e                priv_mode_ls_i,
  input  asid_t                base_asid_i,
  input  logic [PPN_LEN-1:0]   csr_root_ppn_i,
  input  tlb_flush_e           L1TLB_flush_type_i,
  input  tlb_flush_e           L2TLB_flush_type_i,
  input  asid_t                flush_asid_i,
  input  vpn_t                 flush_page_i,
  // Front End <-> i-Cache
  input  frontend_icache_req_t frontend_icache_req_i,
  output logic                 icache_frontend_rdy_o,
  output icache_frontend_ans_t icache_frontend_ans_o,
  // LSQ <-> d-TLB
  input  lsq_dtlb_req_t        lsq_dtlb_req_i,
  output logic                 dtlb_lsq_req_rdy_o,
  output dtlb_lsq_ans_t        dtlb_lsq_ans_o,
  output dtlb_lsq_wup_t        dtlb_lsq_wup_o,
  // LSQ <-> d-Cache
  input  lsq_l1dc_req_t        lsq_l1dc_req_i,
  output logic                 l1dc_lsq_req_rdy_o,
  output l1dc_lsq_ans_t        l1dc_lsq_ans_o,
  output l1dc_lsq_wup_t        l1dc_lsq_wup_o,
  // L2 Cache Arbiter <-> L2 Cache Emulator
  output l2arb_l2c_req_t       l2arb_l2c_req_o,
  input  logic                 l2c_l2arb_req_rdy_i,
  input  l2c_l2arb_ans_t       l2c_l2arb_ans_i,
  output logic                 l2arb_l2c_ans_rdy_o
);

  // RST block <-> d-Cache
  rst_l1dc_req_t        rst_l1dc_req;
  // Update Block <-> d-Cache
  upd_l1dc_req_t        upd_l1dc_req;
  logic                 update_cnt_en;
  logic                 wbb_empty;
  // i-Cache <-> i-TLB
  icache_tlb_req_t      icache_itlb_req;
  logic                 itlb_icache_req_rdy;
  tlb_icache_ans_t      itlb_icache_ans;
  // i-TLB <-> L2 TLB
  itlb_l2tlb_req_t      itlb_l2tlb_req;
  logic                 itlb_l2_ans_ready;
  // PTW <-> MMUC
  logic                 ptw_mmuc_flush;
  mmuc_ptw_ans_t        mmuc_ptw_ans;
  ptw_mmuc_req_t        ptw_mmuc_req;
  ptw_mmuc_write_t      ptw_mmuc_write;
  // PTW <-> L2 TLB
  l2tlb_ptw_req_t       tlb_ptw_req;
  logic                 ptw_tlb_req_rdy;
  ptw_l2tlb_ans_t       ptw_tlb_ans;
  logic                 tlb_ptw_ans_rdy;
  // L2 TLB <-> TLB Arbiter
  l1tlb_l2tlb_req_t     l1tlb_l2tlb_req;
  logic                 l2tlb_l1tlb_req_rdy;
  l2tlb_l1tlb_ans_t     l2tlb_l1tlb_ans_o;
  // TLB Arbiter <-> L1 TLBs
  logic                 l2tlb_itlb_req_rdy;
  logic                 l2tlb_dtlb_req_rdy;
  l2tlb_itlb_ans_t      l2tlb_itlb_ans;
  l2tlb_dtlb_ans_t      l2tlb_dtlb_ans;
  dtlb_l2tlb_req_t      dtlb_l2tlb_req;
  logic                 l1tlb_l2tlb_ans_rdy;
  // d-Cache <-> L2 Arb
  l1dc_l2c_req_t        l1dc_l2arb_req;
  logic                 l2arb_l1dc_req_rdy;
  l2c_l1dc_ans_t        l2arb_l1dc_ans;
  logic                 l1dc_l2c_ans_rdy;
  // i-Cache <-> L2 Arb
  icache_l2_req_t       icache_l2arb_req;
  logic                 l2arb_icache_req_rdy;
  l2_icache_ans_t       l2arb_icache_ans;
  logic                 icache_l2c_ans_rdy;
  // PTW <-> L2 Arb
  ptw_l2c_req_t         ptw_l2arb_req;
  logic                 l2arb_ptw_req_rdy;
  l2c_ptw_ans_t         l2arb_ptw_ans;
  logic                 ptw_l2c_ans_rdy;

  l2c_arbiter i_l2c_arbiter (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .l1dc_l2arb_req_i(l1dc_l2arb_req),
    .icache_l2arb_req_i(icache_l2arb_req),
    .ptw_l2arb_req_i(ptw_l2arb_req),
    .l2arb_l2c_req_o(l2arb_l2c_req_o),
    .l2c_l2arb_req_rdy_i(l2c_l2arb_req_rdy_i),
    .l2arb_l1dc_req_rdy_o(l2arb_l1dc_req_rdy),
    .l2arb_icache_req_rdy_o(l2arb_icache_req_rdy),
    .l2arb_ptw_req_rdy_o(l2arb_ptw_req_rdy),
    .l2c_l2arb_ans_i(l2c_l2arb_ans_i),
    .l2arb_l1dc_ans_o(l2arb_l1dc_ans),
    .l2arb_icache_ans_o(l2arb_icache_ans),
    .l2arb_ptw_ans_o(l2arb_ptw_ans),
    .l1dc_l2c_ans_rdy_i(l1dc_l2c_ans_rdy),
    .icache_l2c_ans_rdy_i(1'b1),
    .ptw_l2c_ans_rdy_i(ptw_l2c_ans_rdy),
    .l2arb_l2c_ans_rdy_o(l2arb_l2c_ans_rdy_o)
  );

  dcache_L1_system_with_ssram i_dcache_L1_system (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_i(clear_dmshr_dregs_i),
    .rst_l1dc_req_i(rst_l1dc_req),
    .upd_l1dc_req_i(upd_l1dc_req),
    .en_cnt_o(update_cnt_en),
    .wbb_empty_o(wbb_empty),
    .lsq_l1dc_req_i(lsq_l1dc_req_i),
    .l1dc_lsq_req_rdy_o(l1dc_lsq_req_rdy_o),
    .l1dc_lsq_ans_o(l1dc_lsq_ans_o),
    .l1dc_lsq_wup_o(l1dc_lsq_wup_o),
    .l1dc_l2c_req_o(l1dc_l2arb_req),
    .l2c_l1dc_req_rdy_i(l2arb_l1dc_req_rdy),
    .l2c_l1dc_ans_i(l2arb_l1dc_ans),
    .l1dc_l2c_ans_rdy_o(l1dc_l2c_ans_rdy)
  );

  dcache_rst_block #(
    .IDX_LEN(DCACHE_L1_IDX_A_LEN)
  ) i_dcache_rst_block (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rst_l1dc_req_o(rst_l1dc_req)
  );

  updateL2_block #(
    .IDX_LEN(DCACHE_L1_IDX_A_LEN)
  ) i_updateL2_block (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .synch_l1dc_l2c_i(synch_l1dc_l2c_i),
    .en_cnt_i(update_cnt_en),
    .wbb_empty_i(wbb_empty),
    .upd_l1dc_req_o(upd_l1dc_req),
    .l2c_update_done_o(l2c_update_done_o)
  );

  icache_L1_with_ssram i_icache_L1 (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .flush_i(flush_i),
    .abort_i(abort_i),
    .ireq_i(frontend_icache_req_i),
    .ready_o(icache_frontend_rdy_o),
    .iresp_o(icache_frontend_ans_o),
    .tlb_areq_o(icache_itlb_req),
    .tlb_ready_i(itlb_icache_req_rdy),
    .tlb_aresp_i(itlb_icache_ans),
    .l2_req_o(icache_l2arb_req),
    .l2_ready(l2arb_icache_req_rdy),
    .l2_resp_i(l2arb_icache_ans)
  );

  mmu_cache i_mmu_cache (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .ptw_mmuc_req_i(ptw_mmuc_req),
    .ptw_mmuc_write_i(ptw_mmuc_write),
    .mmuc_flush_i(ptw_mmuc_flush),
    .mmuc_ptw_ans_o(mmuc_ptw_ans)
  );

  ptw i_ptw (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .flush_i(flush_i),
    .tlb_ptw_req_i(tlb_ptw_req),
    .ptw_tlb_req_rdy_o(ptw_tlb_req_rdy),
    .ptw_tlb_ans_o(ptw_tlb_ans),
    .tlb_ptw_ans_rdy_i(tlb_ptw_ans_rdy),
    .ptw_mmuc_req_o(ptw_mmuc_req),
    .ptw_mmuc_write_o(ptw_mmuc_write),
    .mmuc_flush_o(ptw_mmuc_flush),
    .mmuc_ptw_ans_i(mmuc_ptw_ans),
    .ptw_l2c_req_o(ptw_l2arb_req),
    .l2c_ptw_req_rdy_i(l2arb_ptw_req_rdy),
    .l2c_ptw_ans_i(l2arb_ptw_ans),
    .ptw_l2c_ans_rdy_o(ptw_l2c_ans_rdy),
    .csr_root_ppn_i(csr_root_ppn_i)
  );

  l2_tlb_with_ssram i_l2_tlb (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_mshr_i(clr_l2tlb_mshr_i),
    .abort_i(abort_i),
    .sum_bit_i(sum_bit_i),
    .mxr_bit_i(mxr_bit_i),
    .priv_mode_i(priv_mode_i),
    .priv_mode_ls_i(priv_mode_ls_i),
    .base_asid_i(base_asid_i),
    .flush_type_i(L2TLB_flush_type_i),
    .flush_asid_i(flush_asid_i),
    .flush_page_i(flush_page_i),
    .l1tlb_l2tlb_req_i(l1tlb_l2tlb_req),
    .l2tlb_l1tlb_req_rdy_o(l2tlb_l1tlb_req_rdy),
    .l2tlb_ptw_req_o(tlb_ptw_req),
    .ptw_l2tlb_req_rdy_i(ptw_tlb_req_rdy),
    .ptw_l2tlb_ans_i(ptw_tlb_ans),
    .l2tlb_ptw_ans_rdy_o(tlb_ptw_ans_rdy),
    .l2tlb_l1tlb_ans_o(l2tlb_l1tlb_ans_o)
  );

  tlb_arbiter i_tlb_arbiter (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .itlb_l2tlb_req_i(itlb_l2tlb_req),
    .dtlb_l2tlb_req_i(dtlb_l2tlb_req),
    .l1tlb_l2tlb_req_o(l1tlb_l2tlb_req),
    .l2tlb_l1tlb_req_rdy_i(l2tlb_l1tlb_req_rdy),
    .l2tlb_itlb_req_rdy_o(l2tlb_itlb_req_rdy),
    .l2tlb_dtlb_req_rdy_o(l2tlb_dtlb_req_rdy),
    .l2tlb_l1tlb_ans_i(l2tlb_l1tlb_ans_o),
    .l2tlb_itlb_ans_o(l2tlb_itlb_ans),
    .l2tlb_dtlb_ans_o(l2tlb_dtlb_ans),
    .itlb_l2tlb_ans_rdy_i(itlb_l2_ans_ready),
    .dtlb_l2tlb_ans_rdy_i(1'b1),
    .l1tlb_l2tlb_ans_rdy_o(l1tlb_l2tlb_ans_rdy)
  );

  dtlb_L1 i_dtlb_L1 (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_mshr_i(clr_l1tlb_mshr_i),
    .sum_bit_i(sum_bit_i),
    .mxr_bit_i(mxr_bit_i),
    .priv_mode_i(priv_mode_i),
    .base_asid_i(base_asid_i),
    .flush_type_i(L1TLB_flush_type_i),
    .flush_asid_i(flush_asid_i),
    .flush_page_i(flush_page_i),
    .lsq_dtlb_req_i(lsq_dtlb_req_i),
    .dtlb_lsq_req_rdy_o(dtlb_lsq_req_rdy_o),
    .dtlb_lsq_ans_o(dtlb_lsq_ans_o),
    .dtlb_lsq_wup_o(dtlb_lsq_wup_o),
    .dtlb_l2tlb_req_o(dtlb_l2tlb_req),
    .l2tlb_dtlb_req_rdy_i(l2tlb_dtlb_req_rdy),
    .l2tlb_dtlb_ans_i(l2tlb_dtlb_ans)
  );

  itlb_L1 i_itlb_L1 (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .priv_mode_i(priv_mode_i),
    .base_asid_i(base_asid_i),
    .flush_type_i(L1TLB_flush_type_i),
    .flush_asid_i(flush_asid_i),
    .flush_page_i(flush_page_i),
    .vmem_on_i(vmem_on_i),
    .abort_i(abort_i),
    .ic_areq_i(icache_itlb_req),
    .ic_areq_ready_o(itlb_icache_req_rdy),
    .ic_aresp_o(itlb_icache_ans),
    .l2_req_o(itlb_l2tlb_req),
    .l2_req_ready_i(l2tlb_itlb_req_rdy),
    .l2_resp_i(l2tlb_itlb_ans),
    .l2_resp_ready_o(itlb_l2_ans_ready)
  );

endmodule
