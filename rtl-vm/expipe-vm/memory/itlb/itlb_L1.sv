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
// File: itlb_L1.sv
// Author: Matteo Perotti
// Date: 31/10/2019
// Description: L1 i-TLB with zero latency for an hit. The access time should be masked by the cache access time (cache "virtually" indexed, physically tagged)
// Details: if virtual memory is inactive, the i-TLB should remain inactive too. A valid request is shortened to the output, no exception can be raised and no valid request signal reach the control unit


import len5_pkg::*;
import memory_pkg::*;
import csr_pkg::csr_priv_t;
import csr_pkg::PRIV_MODE_U;
import csr_pkg::PRIV_MODE_S;

module itlb_L1 (
  // main
  input  logic             clk_i,           // main clock
  input  logic             rst_ni,          // main reset signal
  // from CSR
  input  csr_priv_t        priv_mode_i,     // The actual privilege mode (NOT filtered by the MPRV BIT!!)
  input  asid_t            base_asid_i,     // actual ASID from satp
  // ctrl
  input  tlb_flush_e       flush_type_i,    // flush the tlb
  input  asid_t            flush_asid_i,    // asid for selective flush (fence.vma)
  input vpn_t             flush_page_i,    // page address for selective flush (fence.vma)
  input  logic             vmem_on_i,       // is virtual memory active?
  input  logic             abort_i,         // abort current operation
  // i-cache
  input icache_tlb_req_t  ic_areq_i,       // address translation request from i-cache
  output logic             ic_areq_ready_o, // i-TLB is ready for a request
  output tlb_icache_ans_t  ic_aresp_o,      // response channel to i-cache
  // L2-arbiter
  output itlb_l2tlb_req_t  l2_req_o,        // request channel to L2-arbiter
  input  logic             l2_req_ready_i,  // l2 level can accept requests
  input l2tlb_itlb_ans_t  l2_resp_i,       // response channel from L2-arbiter
  output logic             l2_resp_ready_o  // response channel from L2-arbiter
);

  // i_TLB number of entries
  localparam N      = I_TLB_ENTRIES;
  localparam LOG2_N = $clog2(N);

  // i-Cache -> i-TLB request signal. If the virtual memory is inactive, no valid request can arrive and vaddr is masked
  logic                      icache_itlb_effective_req_valid; // The valid signal is masked by vmem_on_i
  virtual_addr_t             effective_vaddr;
  // The i-TLB entries
  itlb_entry_t               entry_vec_q [N];
  logic [N-1:0]              valid_vec;
  // L2C exception
  logic                      exception_reg_en;
  logic                      exception_reg_clr;
  exception_e                exception_q;
  logic [XLEN-VADDR_LEN-1:0] vaddr_msb_difference_vec;
  exception_e                vaddr_exception;
  exception_e                vmem_exception;
  exception_e                user_page_exception; // Access Exception in the comparison block
  exception_e                effective_exception;
  // From the CU
  logic                      flush;               // Global
  logic [N-1:0]              flush_vec;           // Flush mask on the single entries
  logic                      replace_entry;       // Global
  logic [N-1:0]              replacement_vec;     // Replace mask on the single entries
  logic                      waiting_l2c_ans;     // The CU is in the waiting L2C state
  // CU signal
  logic                      tlb_cond_rdy;        // TLB conditionally ready (wait for the hit/miss signal)
  // Comparison block
  logic                      hit;
  logic [N-1:0]              hit_vec;
  logic [LOG2_N-1:0]         hit_idx;             // To address the data
  // To the control
  vpn_t                      vpn_vec_q  [N];
  asid_t                     asid_vec_q [N];
  logic                      glob_vec_q [N];
  logic                      mebi_vec_q [N];
  logic                      gibi_vec_q [N];

  // If Virtual Memory is off, no request is valid and effective VADDR for the TLB is masked
  assign icache_itlb_effective_req_valid = (vmem_on_i) ? ic_areq_i.valid : 1'b0;
  assign effective_vaddr                 = (vmem_on_i) ? ic_areq_i.vaddr : '0;

  //------------------------------\\
  // EXCEPTION CHECK AND REGISTER \\
  //------------------------------\\

  // Exception register
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      exception_q <= NoException;
    end else if (exception_reg_clr) begin // Reg cleared after every valid access which hit
      exception_q <= NoException;
    end else if (exception_reg_en) begin
      exception_q <= l2_resp_i.exception;
    end
  end

  // Check if all the bits of the incoming vaddr from 63 to 39 are equal. If not -> PageFault if Virtual memory is on
  logic effective_vaddr_38;
  assign effective_vaddr_38 = effective_vaddr[38];
  always_comb begin
    for (int k = VADDR_LEN; k < XLEN; k++) begin
      vaddr_msb_difference_vec[k-VADDR_LEN] = (effective_vaddr[k] != effective_vaddr[38]) ? 1'b1 : 1'b0;
    end
  end
  assign vaddr_exception      = (|vaddr_msb_difference_vec) ? PageFault : NoException;
  // If the requesting vaddr is wrong it can't have raised a L2C request
  assign vmem_exception       = (vaddr_exception == PageFault) ? vaddr_exception : exception_q;
  // If no other exceptions are present, check the user page access permissions
  assign effective_exception  = (vmem_exception == NoException) ? user_page_exception : vmem_exception;
  // If the Virtual Memory is inactive, no exception can be raised
  assign ic_aresp_o.exception = (vmem_on_i) ? effective_exception : NoException;

  //-------------------\\
  // REPLACEMENT BLOCK \\
  //-------------------\\

  // Useful for the NRU replacement block
  always_comb begin
    for (int k = 0; k < N; k++) begin
      valid_vec[k] = entry_vec_q[k].valid;
    end
  end

  itlb_replacement_block #(
    .N(N)
  ) i_itlb_replacement_block (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .itlb_valid_vec_i(valid_vec),
    .itlb_req_valid_i(icache_itlb_effective_req_valid),
    .itlb_hit_vec_i(hit_vec),
    .itlb_hit_i(hit),
    .itlb_replacement_vec_o(replacement_vec)
  );

  //----------\\
  // MOORE CU \\
  //----------\\

  itlb_moore_cu i_itlb_moore_cu (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .abort_i(abort_i),
    .vmem_on_i(vmem_on_i),
    .cache_req_valid_i(icache_itlb_effective_req_valid),
    .internal_exception_i(vaddr_exception),
    .itlb_hit_i(hit),
    .l2c_req_rdy_i(l2_req_ready_i),
    .l2c_ans_valid_i(l2_resp_i.valid),
    .tlb_cond_ready_o(tlb_cond_rdy),
    .l2c_req_valid_o(l2_req_o.valid),
    .l2c_ans_rdy_o(l2_resp_ready_o),
    .waiting_l2c_ans_o(waiting_l2c_ans)
  );

  //--------------------\\
  // COMBINATORIAL CTRL \\
  //--------------------\\

  always_comb begin
    for (int k = 0; k < N; k++) begin
      vpn_vec_q[k]  = entry_vec_q[k].vpn ;
      asid_vec_q[k] = entry_vec_q[k].asid;
      glob_vec_q[k] = entry_vec_q[k].glob;
      mebi_vec_q[k] = entry_vec_q[k].mebi;
      gibi_vec_q[k] = entry_vec_q[k].gibi;
    end
  end

  itlb_ctrl #(
    .N(N)
  ) i_itlb_ctrl (
    .vmem_on_i(vmem_on_i),
    .tlb_cond_ready_i(tlb_cond_rdy),
    .waiting_l2c_ans_i(waiting_l2c_ans),
    .flush_type_i(flush_type_i),
    .flush_asid_i(flush_asid_i),
    .flush_page_i(flush_page_i),
    .vpn_vec_q(vpn_vec_q),
    .asid_vec_q(asid_vec_q),
    .glob_vec_q(glob_vec_q),
    .mebi_vec_q(mebi_vec_q),
    .gibi_vec_q(gibi_vec_q),
    .icache_tlb_req_valid_i(icache_itlb_effective_req_valid),
    .itlb_hit_i(hit),
    .itlb_exception_i(effective_exception),
    .l2c_ans_valid_i(l2_resp_i.valid),
    .l2c_ans_exception_i(l2_resp_i.exception),
    .flush_o(flush),
    .flush_vec_o(flush_vec),
    .icache_req_rdy_o(ic_areq_ready_o),
    .icache_ans_valid_o(ic_aresp_o.valid),
    .exception_reg_en_o(exception_reg_en),
    .exception_reg_clr_o(exception_reg_clr),
    .replace_o(replace_entry)
  );

  //-------------\\
  // TLB ENTRIES \\
  //-------------\\

  // Enable and flush signals masked by the flush vector and the replacement vector
  for (genvar k = 0; k < N; k++) begin : itlb_entries
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        entry_vec_q[k]        <= '0;
      end else if (flush && flush_vec[k]) begin
        entry_vec_q[k].valid  <= 1'b0;
      end else if (replace_entry && replacement_vec[k]) begin
        entry_vec_q[k].ppn    <= l2_resp_i.ppn;
        entry_vec_q[k].vpn    <= effective_vaddr.vpn;
        entry_vec_q[k].asid   <= base_asid_i;
        entry_vec_q[k].glob   <= l2_resp_i.g_bit;
        entry_vec_q[k].user   <= l2_resp_i.u_bit;
        entry_vec_q[k].gibi   <= (l2_resp_i.page_type == GibiPage) ? 1'b1 : 1'b0;
        entry_vec_q[k].mebi   <= (l2_resp_i.page_type == MebiPage) ? 1'b1 : 1'b0;;
        entry_vec_q[k].valid  <= 1'b1;
      end
    end
  end

  //-----------------------\\
  // COMPARE AND SELECTION \\
  //-----------------------\\

  // Hit vector creation and superpage checking
  always_comb begin
    hit_vec             = '0;
    hit_idx             = '0;
    user_page_exception = NoException;
    for (int k = 0; k < N; k++) begin
      if (valid_vec[k]) begin
        if ((entry_vec_q[k].asid == base_asid_i) || entry_vec_q[k].glob) begin
          // Gibipage
          if (entry_vec_q[k].gibi) begin
            if (effective_vaddr.vpn[2] == entry_vec_q[k].vpn[2]) begin
                // User Page. S mode access forbidden (the SUM bit is ignored for the instructions!)
                if          ( entry_vec_q[k].user && priv_mode_i == PRIV_MODE_S) user_page_exception = PageFault;
                // Not a User page. U mode access forbidden
                else if (!entry_vec_q[k].user && priv_mode_i == PRIV_MODE_U) user_page_exception = PageFault;
              hit_vec[k] = 1'b1;
              hit_idx    = k;
            end
          // Mebipage
          end else if (entry_vec_q[k].mebi) begin
            if (effective_vaddr.vpn[2] == entry_vec_q[k].vpn[2]) begin
              if (effective_vaddr.vpn[1] == entry_vec_q[k].vpn[1]) begin
                // User Page. S mode access forbidden (the SUM bit is ignored for the instructions!)
                if          ( entry_vec_q[k].user && priv_mode_i == PRIV_MODE_S) user_page_exception = PageFault;
                // Not a User page. U mode access forbidden
                else if (!entry_vec_q[k].user && priv_mode_i == PRIV_MODE_U) user_page_exception = PageFault;
                hit_vec[k] = 1'b1;
                hit_idx    = k;
              end
            end
          // Kibipage
          end else begin
            if (effective_vaddr.vpn == entry_vec_q[k].vpn) begin
                // User Page. S mode access forbidden (the SUM bit is ignored for the instructions!)
                if          ( entry_vec_q[k].user && priv_mode_i == PRIV_MODE_S) user_page_exception = PageFault;
                // Not a User page. U mode access forbidden
                else if (!entry_vec_q[k].user && priv_mode_i == PRIV_MODE_U) user_page_exception = PageFault;
              hit_vec[k] = 1'b1;
              hit_idx    = k;
            end
          end
        end
      end
    end
  end

  assign hit = |hit_vec;

  // If virtual memory is off, hit is always 1.
  assign ic_aresp_o.hit = (vmem_on_i) ? |hit_vec : 1'b1;

  //------------\\
  // L2 REQUEST \\
  //------------\\

  assign l2_req_o.vpn = ic_areq_i.vaddr.vpn;

  //-------------------\\
  // PADDR COMPOSITION \\
  //-------------------\\

  // Compose the physical address
  always_comb begin
    if (vmem_on_i) begin
      if      (entry_vec_q[hit_idx].gibi) ic_aresp_o.paddr = {entry_vec_q[hit_idx].ppn.p2, effective_vaddr.vpn[1:0], effective_vaddr.page_offset};
      else if (entry_vec_q[hit_idx].mebi) ic_aresp_o.paddr = {entry_vec_q[hit_idx].ppn.p2, entry_vec_q[hit_idx].ppn.p1, effective_vaddr.vpn[0], effective_vaddr.page_offset};
      else                                ic_aresp_o.paddr = {entry_vec_q[hit_idx].ppn, effective_vaddr.page_offset};
    // If virtual memory is inactive, PADDR = VADDR
    end else ic_aresp_o.paddr = ic_areq_i.vaddr;
  end

endmodule
