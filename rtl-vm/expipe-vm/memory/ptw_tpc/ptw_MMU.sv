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
// File: ptw.sv
// Author: Matteo Perotti
// Date: 15/10/2019
// Description: Page Table Walker

import memory_pkg::*;




module ptw_MMU (
    input  logic           clk_i,
    input  logic           rst_ni,             // async reset
    input  logic           flush_i,            // flush ptw and mmuc
    // L2_tlb -> ptw
    input  l2tlb_ptw_req_t tlb_ptw_req_i,      // 3*9 = 27 bits of virtual page numbers
    output logic           ptw_tlb_req_rdy_o,  // ptw ready for TLB request
    // ptw -> L2_tlb
    output ptw_l2tlb_ans_t ptw_tlb_ans_o,      // ppn, isSuperpage, exception, valid
    input  logic           tlb_ptw_ans_rdy_i,  // tlb ready

    // ptw -> L2_cache
    output ptw_l2c_req_t               ptw_l2c_req_o,      // PPN to address a PTE
    input  logic                       l2c_ptw_req_rdy_i,  // L2 cache ready for ptw
    // L2_cache -> ptw
    input  l2c_ptw_ans_t               l2c_ptw_ans_i,      // PTE from L2 cache
    output logic                       ptw_l2c_ans_rdy_o,  // ptw ready for L2 cache
    // csr -> ptw
    input  logic         [PPN_LEN-1:0] csr_root_ppn_i      // the root ppn
);

  // Signlas 
  ptw_mmuc_req_t   ptw_mmuc_req_o;  // first two VPNs
  ptw_mmuc_write_t ptw_mmuc_write_o;  // info for mmu_cache lines replacement
  logic            mmuc_flush_o;  // flush the mmuc
  mmuc_ptw_ans_t   mmuc_ptw_ans_i;  // low_vpn, hit, full_hit, isSuperpage

  ptw u_ptw (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .flush_i(flush_i),
      .tlb_ptw_req_i(tlb_ptw_req_i),
      .ptw_tlb_req_rdy_o(ptw_tlb_req_rdy_o),
      .ptw_tlb_ans_o(ptw_tlb_ans_o),
      .tlb_ptw_ans_rdy_i(tlb_ptw_ans_rdy_i),
      .ptw_mmuc_req_o(ptw_mmuc_req_o),
      .ptw_mmuc_write_o(ptw_mmuc_write_o),
      .mmuc_flush_o(mmuc_flush_o),
      .mmuc_ptw_ans_i(mmuc_ptw_ans_i),
      .ptw_l2c_req_o(ptw_l2c_req_o),
      .l2c_ptw_req_rdy_i(l2c_ptw_req_rdy_i),
      .l2c_ptw_ans_i(l2c_ptw_ans_i),
      .ptw_l2c_ans_rdy_o(ptw_l2c_ans_rdy_o),
      .csr_root_ppn_i(csr_root_ppn_i)
  );

  mmu_cache u_mmu_cache (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .ptw_mmuc_req_i(ptw_mmuc_req_o),
      .ptw_mmuc_write_i(ptw_mmuc_write_o),
      .mmuc_flush_i(mmuc_flush_o),
      .mmuc_ptw_ans_o(mmuc_ptw_ans_i)  // PPN, hit, full_hit, is_superpage
  );

endmodule
