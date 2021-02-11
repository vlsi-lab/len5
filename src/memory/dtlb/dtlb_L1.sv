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
// File: dtlb_L1.sv
// Author: Matteo Perotti
// Date: 31/10/2019
// Description: d-TLB
// Details: fully associative to easily support multiple page sizes. It is small (clock cycle and power)

`include "memory_pkg.sv"
`include "len5_pkg.sv"
import memory_pkg::*;
import len5_pkg::*;
//import mmm_pkg::*;

`include "dtlb_replacement_block.sv"

module dtlb_L1
(
  // Main signals
  input  logic            clk_i,
  input  logic            rst_ni,
  input  logic            clr_mshr_i,           // Clear MSHR if branch mispredicted
  // From CSRs
  input  logic            sum_bit_i,            // For U bit access permissions check
  input  logic            mxr_bit_i,            // Executable pages can become Readable
  input  priv_e           priv_mode_i,          // The actual privilege mode (filtered by the MPRV BIT!!)
  input  asid_t           base_asid_i,          // Actual ASID from SATP
  // Flush control
  input  tlb_flush_e      flush_type_i,         // Flush selectively the TLB and the MSHR
  input  asid_t           flush_asid_i,         // ASID for selective flush (fence.vma)
  input  vpn_t            flush_page_i,         // Page address for selective flush (fence.vma)
  // LSQ -> D-TLB translation request
  input  lsq_dtlb_req_t   lsq_dtlb_req_i,
  output logic            dtlb_lsq_req_rdy_o,
  // D-TLB -> LSQ answer and wake-up
  output dtlb_lsq_ans_t   dtlb_lsq_ans_o,
  output dtlb_lsq_wup_t   dtlb_lsq_wup_o,
  // D-TLB -> L2-TLB miss request (via the MSHR)
  output dtlb_l2tlb_req_t dtlb_l2tlb_req_o,     // MSHR to L2-TLB request
  input  logic            l2tlb_dtlb_req_rdy_i, // L2-TLB ready for MSHR req?
  // L2-TLB -> D-TLB answer
  input  l2tlb_dtlb_ans_t l2tlb_dtlb_ans_i      // Always ready for the L2-TLB, because it has the highest req priority
);

  localparam N      = D_TLB_ENTRIES;
  localparam LOG2_N = $clog2(N);
  localparam M      = DTLB_MSHR_ENTRIES;
  localparam LOG2_M = $clog2(M);

  // D-TLB Entries
  dtlb_entry_t       dtlb_entry_q [N];
  // Replacement block
  logic              valid_tlb_read; // Update the replacement vector
  logic [N-1:0]      tlb_valid_vec;
  logic [N-1:0]      replace_vec;      // One hot replacement vector,
  // Comparison block
  logic              tlb_hit;
  logic [N-1:0]      hit_vec;          // D-TLB hit vector
  logic [LOG2_N-1:0] hit_idx;
  // Ctrl
  dtlb_ctrl_e        dtlb_ctrl;
  logic [N-1:0]      flush_vec;
  logic              add_mshr_entry;
  logic              put_mshr_entry_wait;
  logic              rm_mshr_entry;
  logic              replace_entry;
  // Exception can come from L2-TLB answer or from the d-TLB comparison
  exception_e        exception_dtlb, exception_l2tlb;
  // MSHR
  dtlb_mshr_entry_t  mshr_entry_q [M];
  vpn_t              mshr_vpn_to_be_compared;
  logic [M-1:0]      mshr_valid_vec;
  logic [M-1:0]      mshr_valid_not_waiting_vec;
  logic [M-1:0]      mshr_oh_valid_not_waiting_vec;
  logic [LOG2_M-1:0] mshr_valid_not_waiting_idx;
  logic [M-1:0]      mshr_oh_invalid_vec;
  logic [LOG2_M-1:0] mshr_invalid_idx;
  logic              mshr_hit;
  logic [M-1:0]      mshr_hit_vec;
  logic              mshr_full;


  //-----------------------\\
  // SCHEDULER AND ARBITER \\
  //-----------------------\\

  // Control definition
  always_comb begin
    dtlb_ctrl = dtlb_NoReq;
         if (flush_type_i != NoFlush)            dtlb_ctrl = dtlb_Flush;
    else if (l2tlb_dtlb_ans_i.valid)             dtlb_ctrl = dtlb_L2Ans;
    else if (lsq_dtlb_req_i.valid && !mshr_full) dtlb_ctrl = dtlb_LSQReq;
  end

  // Arbiter
  always_comb begin
    // Ready only if the d-TLB is not flushing, if L2-TLB is not returning a valid answer and if mshr not full
    dtlb_lsq_req_rdy_o   = (flush_type_i == NoFlush && !l2tlb_dtlb_ans_i.valid && !mshr_full) ? 1'b1 : 1'b0;
  end

  //-------------------\\
  // REPLACEMENT BLOCK \\
  //-------------------\\

  // Valid vector to the replacement block. If at least one entry is not valid, fill it first
  always_comb begin
    for (int k = 0; k < N; k++) begin
      tlb_valid_vec[k] = dtlb_entry_q[k].valid;
    end
  end

  // PLRU replacement block
  dtlb_replacement_block #(
    .N(N)
  ) i_dtlb_replacement_block (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .tlb_valid_vec_i(tlb_valid_vec),
    .valid_tlb_read_i(valid_tlb_read),
    .valid_tlb_replacement_i(replace_entry),
    .hit_vec_i(hit_vec),
    .replace_vec_o(replace_vec)
  );

  //----------------------------------\\
  // CONTROL AND DATA SELECTION LOGIC \\
  //----------------------------------\\

  // Mask the access if it is valid but an PageFault is raised
  assign valid_tlb_read = ((dtlb_ctrl == dtlb_LSQReq) && (exception_dtlb != PageFault)) ? 1'b1 : 1'b0;

  always_comb begin
      dtlb_lsq_ans_o = '0;
      dtlb_lsq_wup_o = '0;
      flush_vec      = '0;
      replace_entry  = 1'b0;
      add_mshr_entry = 1'b0;
      rm_mshr_entry  = 1'b0;
    case (dtlb_ctrl)
      // Flush control
      dtlb_Flush: begin
        case (flush_type_i)
          // Selective flush on the ASID. If the page is marked as global, don't flush it
          FlushASID: begin
            for (int k = 0; k < N; k++) begin
              flush_vec[k] = ((dtlb_entry_q[k].asid == flush_asid_i) && !dtlb_entry_q[k].glob) ? 1'b1 : 1'b0;
            end
          end
          // Selective flush on the page. The comparison depends on the page type
          FlushPage: begin
            for (int k = 0; k < N; k++) begin
              if (dtlb_entry_q[k].mebi) begin
                flush_vec[k] = (dtlb_entry_q[k].vpn[2:1] == flush_page_i[2:1]) ? 1'b1 : 1'b0;
              end else if (dtlb_entry_q[k].gibi) begin
                flush_vec[k] = (dtlb_entry_q[k].vpn[2] == flush_page_i[2]) ? 1'b1 : 1'b0;
              end else begin
                flush_vec[k] = (dtlb_entry_q[k].vpn == flush_page_i) ? 1'b1 : 1'b0;
              end
            end
          end
          FlushAll: flush_vec = '1;
        endcase
      end
      dtlb_L2Ans: begin
        // If the entry was removed from the MSHR
        if (mshr_hit) begin
          // Don't put the new entry in the d-TLB if there is an exception
          replace_entry            = (l2tlb_dtlb_ans_i.exception == NoException) ? 1'b1 : 1'b0;
          // Remove the returned MSHR entry
          rm_mshr_entry            = 1'b1;
          // Wake up the LSQ entries and forward ppn and exception
          dtlb_lsq_wup_o.vpn       = l2tlb_dtlb_ans_i.vpn;
          dtlb_lsq_wup_o.valid     = 1'b1;
          // PPN forwarded for the Load Queue only
          dtlb_lsq_ans_o.ppn       = l2tlb_dtlb_ans_i.ppn;
          // If present, the exception is forwarded to the LSQ. Otherwise, check on possible store exceptions
          dtlb_lsq_ans_o.exception = l2tlb_dtlb_ans_i.exception;
        end
      end
      dtlb_LSQReq: begin
        if (tlb_hit) begin
          // If there is an exception, the ppn shouldn't be saved into the load/store queue (control in the LSQ)
          dtlb_lsq_ans_o.ppn       = dtlb_entry_q[hit_idx].ppn;
          dtlb_lsq_ans_o.exception = exception_dtlb;
          dtlb_lsq_ans_o.was_store = lsq_dtlb_req_i.is_store;
          dtlb_lsq_ans_o.lsq_addr  = lsq_dtlb_req_i.lsq_addr;
          dtlb_lsq_ans_o.valid     = 1'b1;
        end else if (!mshr_hit) begin
          add_mshr_entry = 1'b1;
        end
      end
    endcase
  end

  //-------------\\
  // TLB ENTRIES \\
  //-------------\\

  for (genvar k = 0; k < N; k++) begin
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        dtlb_entry_q[k]         <= '0;
      end else if (dtlb_ctrl == dtlb_Flush && flush_vec[k]) begin
        dtlb_entry_q[k].valid   <= 1'b0;
      end else if (replace_entry && replace_vec[k]) begin
        dtlb_entry_q[k].vpn     <= l2tlb_dtlb_ans_i.vpn;
        dtlb_entry_q[k].ppn     <= l2tlb_dtlb_ans_i.ppn;
        dtlb_entry_q[k].asid    <= base_asid_i;
        dtlb_entry_q[k].glob    <= l2tlb_dtlb_ans_i.g_bit;
        dtlb_entry_q[k].user    <= l2tlb_dtlb_ans_i.u_bit;
        dtlb_entry_q[k].read    <= l2tlb_dtlb_ans_i.r_bit;
        dtlb_entry_q[k].write   <= l2tlb_dtlb_ans_i.w_bit;
        dtlb_entry_q[k].execute <= l2tlb_dtlb_ans_i.x_bit;
        dtlb_entry_q[k].dirty   <= l2tlb_dtlb_ans_i.d_bit;
        dtlb_entry_q[k].gibi    <= (l2tlb_dtlb_ans_i.page_type == GibiPage) ? 1'b1 : 1'b0;
        dtlb_entry_q[k].mebi    <= (l2tlb_dtlb_ans_i.page_type == MebiPage) ? 1'b1 : 1'b0;
        dtlb_entry_q[k].valid   <= 1'b1;
      end
    end
  end

  //------------------\\
  // COMPARISON BLOCK \\
  //------------------\\

  always_comb begin
    exception_dtlb = NoException;
    hit_vec        = '0;
    hit_idx        = '0;
    // Valid request by the LSQ with no other requests
    if (dtlb_ctrl == dtlb_LSQReq) begin
      for (int k = 0; k < N; k++) begin
        if (dtlb_entry_q[k].valid) begin
          if (dtlb_entry_q[k].glob || (dtlb_entry_q[k].asid == base_asid_i)) begin
            // GibiPage
            if (dtlb_entry_q[k].gibi) begin
              // GibiPage hit
              if (lsq_dtlb_req_i.vpn[2] == dtlb_entry_q[k].vpn[2]) begin
                // Executable only page without load/store permissions
                if (!dtlb_entry_q[k].read && !mxr_bit_i)                         exception_dtlb = PageFault;
                // Store on a read-only page
                else if (lsq_dtlb_req_i.is_store && !dtlb_entry_q[k].write)      exception_dtlb = PageFault;
                // Store on a clean page
                else if (lsq_dtlb_req_i.is_store && !dtlb_entry_q[k].dirty)      exception_dtlb = PageFault;
                // User page. Supervisor access allowed only if SUM bit is asserted
                else if (dtlb_entry_q[k].user && priv_mode_i == S && !sum_bit_i) exception_dtlb = PageFault;
                // Not a User page. U mode access forbidden
                else if (!dtlb_entry_q[k].user && priv_mode_i == U)          exception_dtlb = PageFault;
                hit_vec[k] = 1'b1;
                hit_idx = k;
              end
            // MebiPage
            end else if (dtlb_entry_q[k].mebi) begin
              if (lsq_dtlb_req_i.vpn[2] == dtlb_entry_q[k].vpn[2] && lsq_dtlb_req_i.vpn[1] == dtlb_entry_q[k].vpn[1]) begin
                // Executable only page without load/store permissions
                if (!dtlb_entry_q[k].read && !mxr_bit_i)                         exception_dtlb = PageFault;
                // Store on a read-only page
                else if (lsq_dtlb_req_i.is_store && !dtlb_entry_q[k].write)      exception_dtlb = PageFault;
                // Store on a clean page
                else if (lsq_dtlb_req_i.is_store && !dtlb_entry_q[k].dirty)      exception_dtlb = PageFault;
                // User page. Supervisor access allowed only if SUM bit is asserted
                else if (dtlb_entry_q[k].user && priv_mode_i == S && !sum_bit_i) exception_dtlb = PageFault;
                // Not a User page. U mode access forbidden
                else if (!dtlb_entry_q[k].user && priv_mode_i == U)          exception_dtlb = PageFault;
                hit_vec[k] = 1'b1;
                hit_idx = k;
              end
            // KibiPage
            end else begin
              if (lsq_dtlb_req_i.vpn == dtlb_entry_q[k].vpn) begin
                // Executable only page without load/store permissions
                if (!dtlb_entry_q[k].read && !mxr_bit_i)                         exception_dtlb = PageFault;
                // Store on a read-only page
                else if (lsq_dtlb_req_i.is_store && !dtlb_entry_q[k].write)      exception_dtlb = PageFault;
                // Store on a clean page
                else if (lsq_dtlb_req_i.is_store && !dtlb_entry_q[k].dirty)      exception_dtlb = PageFault;
                // User page. Supervisor access allowed only if SUM bit is asserted
                else if (dtlb_entry_q[k].user && priv_mode_i == S && !sum_bit_i) exception_dtlb = PageFault;
                // Not a User page. U mode access forbidden
                else if (!dtlb_entry_q[k].user && priv_mode_i == U)          exception_dtlb = PageFault;
                hit_vec[k] = 1'b1;
                hit_idx = k;
              end
            end
          end
        end
      end
    end
  end

  assign tlb_hit = |hit_vec;

  //------\\
  // MSHR \\
  //------\\

  // d-TLB MSHR entries
  for (genvar k = 0; k < M; k++) begin : dtlb_mshr_entries
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        mshr_entry_q[k]           <=   '0;
      end else if (clr_mshr_i) begin
        mshr_entry_q[k].valid     <= 1'b0;
        mshr_entry_q[k].waiting   <= 1'b0;
      end else if (rm_mshr_entry && mshr_hit_vec[k]) begin
        mshr_entry_q[k].valid     <= 1'b0;
        mshr_entry_q[k].waiting   <= 1'b0;
      end else if (put_mshr_entry_wait && mshr_oh_valid_not_waiting_vec[k]) begin
        mshr_entry_q[k].waiting   <= 1'b1;
      end else if (add_mshr_entry && mshr_oh_invalid_vec[k]) begin
        mshr_entry_q[k].vpn       <= lsq_dtlb_req_i.vpn;
        mshr_entry_q[k].valid     <= 1'b1;
        mshr_entry_q[k].waiting   <= 1'b0;
      end
    end
  end

  // Comparison block: the VPN to be compared can be the one returned from the L2-TLB or the LSQ one
  assign mshr_vpn_to_be_compared = (dtlb_ctrl == dtlb_L2Ans) ? l2tlb_dtlb_ans_i.vpn : lsq_dtlb_req_i.vpn;
  always_comb begin
    mshr_hit_vec = '0;
    for (int k = 0; k < M; k++) begin
      if (dtlb_ctrl == dtlb_L2Ans) begin
        case (l2tlb_dtlb_ans_i.page_type)
          GibiPage: mshr_hit_vec[k] = (mshr_entry_q[k].valid && mshr_entry_q[k].vpn[2]   == mshr_vpn_to_be_compared[2]  ) ? 1'b1 : 1'b0;
          MebiPage: mshr_hit_vec[k] = (mshr_entry_q[k].valid && mshr_entry_q[k].vpn[2:1] == mshr_vpn_to_be_compared[2:1]) ? 1'b1 : 1'b0;
          KibiPage: mshr_hit_vec[k] = (mshr_entry_q[k].valid && mshr_entry_q[k].vpn      == mshr_vpn_to_be_compared     ) ? 1'b1 : 1'b0;
        endcase
      end else if (dtlb_ctrl == dtlb_LSQReq) mshr_hit_vec[k] = (mshr_entry_q[k].valid && (mshr_entry_q[k].vpn == mshr_vpn_to_be_compared)) ? 1'b1 : 1'b0;
    end
  end

  assign mshr_hit = |mshr_hit_vec;

  always_comb begin
    mshr_valid_vec             = '0;
    mshr_valid_not_waiting_vec = '0;
    mshr_valid_not_waiting_idx = '0;
    mshr_invalid_idx           = '0;
    // Priority encoding and multi hot vector formation
    for (int k = M-1; k >= 0; k--) begin
      mshr_valid_vec[k] = mshr_entry_q[k].valid;
      if (mshr_entry_q[k].valid && !mshr_entry_q[k].waiting) begin
        mshr_valid_not_waiting_vec[k] = 1'b1;
        mshr_valid_not_waiting_idx = k;
      end else if (!mshr_entry_q[k].valid) mshr_invalid_idx = k;
    end
  end

  // MSHR full -> d-TLB not ready
  assign mshr_full = &mshr_valid_vec;

  // One hot vector formation to selectively enable add and remove of MSHR entries
  always_comb begin
    mshr_oh_valid_not_waiting_vec = '0;
    mshr_oh_invalid_vec           = '0;
    mshr_oh_valid_not_waiting_vec[mshr_valid_not_waiting_idx] = 1'b1;
    mshr_oh_invalid_vec[mshr_invalid_idx]                     = 1'b1;
  end

  // A valid and not waiting entry can become an L2-TLB request
  assign dtlb_l2tlb_req_o.vpn    = mshr_entry_q[mshr_valid_not_waiting_idx].vpn;
  // MSHR valid request if there is at least one valid and not waiting entry
  assign dtlb_l2tlb_req_o.valid  = |mshr_valid_not_waiting_vec;

  // If valid MSHR -> L2-TLB transaction, put the entry in a waiting state
  assign put_mshr_entry_wait     = (l2tlb_dtlb_req_rdy_i && dtlb_l2tlb_req_o.valid) ? 1'b1 : 1'b0;

endmodule
