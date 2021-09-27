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
// File: L2_tlb_t1.sv
// Author: Matteo Perotti
// Date: 04/11/2019
// Description: second part of the L2-TLB
// Details: check the output data of the memory, allocate MSHR entries, check for exceptions, answer to the lower levels

import memory_pkg::*;
import len5_pkg::*;
//import mmm_pkg::*;

module L2_tlb_t1
#(
  A     = L2_TLB_IDX_LEN,
  N_WAY = L2_TLB_ASSOCIATIVITY
)
(
  // From the system
  input  logic             abort_i,
  // From the CSRs
  input  logic             sum_bit_i,      // For U bit access permissions check. Neglected for isntruction ch
  input  logic             mxr_bit_i,      // Executable pages can become Readable
  input  priv_e            priv_mode_i,    // The actual privilege mode (NOT filtered by the MPRV BIT!!)
  input  priv_e            priv_mode_ls_i, // The actual privilege mode (filtered by the MPRV BIT!!)
  input  asid_t            base_asid_i,    // Actual ASID from "satp" register
  // Flush control
  input  asid_t            flush_asid_i,
  input  var vpn_t             flush_page_i,
  // (t1 -> MSHR) data
  output vpn_t             t1_mshr_vpn_o,
  output tlb_arb_tag_e     mshr_destination_o,
  // (t1 -> MSHR) control
  output logic             add_mshr_entry_o,
  // (L2 TLB -> L1 TLB Arbiter) answer channel
  output l2tlb_l1tlb_ans_t l2tlb_l1tlb_ans_o,
  // t0 -> registers
  input  var t0_t1_req_t       t0_t1_req_q_i,
  // Memory -> t1 data
  input  var l2tlb_entry_t     tlb_output_entry_vec_i [N_WAY],
  // (t1 -> t0) request channel
  output t1_t0_req_t       t1_t0_req_o,
  // (t1 -> Replacement block)
  output logic [N_WAY-1:0] valid_vec_o,
  output logic [N_WAY-1:0] hit_vec_o,
  output logic             valid_tlb_read_o,    // The output of the TLB is valid after an useful read
  output logic             valid_tlb_access_o,  // A valid TLB acces has occurred
  output logic             replacing_an_entry_o // An entry is being replaced
);

  localparam T  = (VPN_LEN                 ) - L2_TLB_IDX_LEN; // The length of the TAG of the L2 TLB entry
  localparam KT = (VPN_LEN                 ) - L2_TLB_IDX_LEN; // KibiTag LEN (20 bit if IDX = 7 bit)
  localparam MT = (VPN_LEN - VPN_PART_LEN  ) - L2_TLB_IDX_LEN; // MebiTag LEN (11 bit if IDX = 7 bit)
  localparam GT = (VPN_LEN - 2*VPN_PART_LEN) - L2_TLB_IDX_LEN; // GibiTag LEN ( 2 bit if IDX = 7 bit)

  localparam LOG2_N_WAY = $clog2(N_WAY);

  logic [N_WAY-1:0]      hit_vec;
  logic [LOG2_N_WAY-1:0] hit_idx;
  logic                  hit;
  logic [VPN_LEN-1:0]    vpn_q, page_to_be_flushed;     // The VPN coming from the (t0 -> t1) registers
  l2tlb_entry_t          tlb_vec_q [N_WAY];             // Shorten the name not to tire your poor eyes...
  exception_e            l2tlb_exception;

  // Easier name assignments
  assign tlb_vec_q          = tlb_output_entry_vec_i;
  assign vpn_q              = t0_t1_req_q_i.vpn;
  assign page_to_be_flushed = flush_page_i;

  // MSHR vpn and destination are the ones output by the (t0 -> t1) registers
  assign t1_mshr_vpn_o      = t0_t1_req_q_i.vpn;
  assign mshr_destination_o = t0_t1_req_q_i.destination;

  //--------------------------------\\
  // COMPARISON BLOCK AND EXCEPTION \\
  //--------------------------------\\

  // Hit vector, flush_vec composition and Access exception checking
  always_comb begin
    hit_vec               = '0;
    case (t0_t1_req_q_i.req_type)
      t0_t1_KibiRead: begin
        for (int k = 0; k < N_WAY; k++) begin
          if ((tlb_vec_q[k].asid == base_asid_i) || tlb_vec_q[k].glob) begin
            // Page hit! But it does not mean this is a KibiPage (we are not checking the size in this first probing!)
            hit_vec[k] = (vpn_q[VPN_LEN-1-:KT] == tlb_vec_q[k].tag) ? tlb_vec_q[k].valid : 1'b0;
          end
        end
      end
      t0_t1_MebiRead: begin
        for (int k = 0; k < N_WAY; k++) begin
          if ((tlb_vec_q[k].asid == base_asid_i) || tlb_vec_q[k].glob) begin
            if (tlb_vec_q[k].mebi) begin
              // MebiPage hit! This is a MebiPage
              hit_vec[k] = (vpn_q[VPN_LEN-1-:MT] == tlb_vec_q[k].tag[T-1-:MT]) ? tlb_vec_q[k].valid : 1'b0;
            end
          end
        end
      end
      t0_t1_GibiRead: begin
        for (int k = 0; k < N_WAY; k++) begin
          if ((tlb_vec_q[k].asid == base_asid_i) || tlb_vec_q[k].glob) begin
            if (tlb_vec_q[k].gibi) begin
              // GibiPage hit! This is a GibiPage
              hit_vec[k] = (vpn_q[VPN_LEN-1-:GT] == tlb_vec_q[k].tag[T-1-:GT]) ? tlb_vec_q[k].valid : 1'b0;
            end
          end
        end
      end
    endcase
  end
  // Hit Idx
  always_comb begin
    hit_idx = '0;
    for (int k = N_WAY-1; k >= 0; k--) begin
      if (hit_vec[k]) hit_idx = k;
    end
  end
  // Global hit signal
  assign hit = |hit_vec;

  //------------\\
  // EXCEPTIONS \\
  //------------\\

  // Exceptions
  always_comb begin
    l2tlb_exception = NoException;
    case (t0_t1_req_q_i.req_type)
      t0_t1_KibiRead: begin
        // Check for PageFault Exceptions
        case (t0_t1_req_q_i.destination)
          ITLB: begin
            if      (!tlb_vec_q[hit_idx].execute)                                           l2tlb_exception = PageFault;
            else if ( tlb_vec_q[hit_idx].user && priv_mode_i == S)                          l2tlb_exception = PageFault;
            else if (!tlb_vec_q[hit_idx].user && priv_mode_i == U)                          l2tlb_exception = PageFault;
          end
          DTLB: begin
            // It can't exist here a (R == 0 && X == 0) page, so don't check it
            if      (!tlb_vec_q[hit_idx].read &&  tlb_vec_q[hit_idx].execute && !mxr_bit_i) l2tlb_exception = PageFault;
            else if ( tlb_vec_q[hit_idx].user &&  priv_mode_ls_i == S        && !sum_bit_i) l2tlb_exception = PageFault;
            else if (!tlb_vec_q[hit_idx].user &&  priv_mode_ls_i == U                     ) l2tlb_exception = PageFault;
          end
        endcase
      end
      t0_t1_MebiRead: begin
        // Check for PageFault Exceptions
        case (t0_t1_req_q_i.destination)
          ITLB: begin
            if      (!tlb_vec_q[hit_idx].execute)                                           l2tlb_exception = PageFault;
            else if ( tlb_vec_q[hit_idx].user && priv_mode_i == S)                          l2tlb_exception = PageFault;
            else if (!tlb_vec_q[hit_idx].user && priv_mode_i == U)                          l2tlb_exception = PageFault;
          end
          DTLB: begin
            if      (!tlb_vec_q[hit_idx].read &&  tlb_vec_q[hit_idx].execute && !mxr_bit_i) l2tlb_exception = PageFault;
            else if ( tlb_vec_q[hit_idx].user &&  priv_mode_ls_i == S        && !sum_bit_i) l2tlb_exception = PageFault;
            else if (!tlb_vec_q[hit_idx].user &&  priv_mode_ls_i == U                     ) l2tlb_exception = PageFault;
          end
        endcase
      end
      t0_t1_GibiRead: begin
        // Check for PageFault Exceptions
        case (t0_t1_req_q_i.destination)
        ITLB: begin
          if      (!tlb_vec_q[hit_idx].execute)                                           l2tlb_exception = PageFault;
          else if ( tlb_vec_q[hit_idx].user && priv_mode_i == S)                          l2tlb_exception = PageFault;
          else if (!tlb_vec_q[hit_idx].user && priv_mode_i == U)                          l2tlb_exception = PageFault;
        end
        DTLB: begin
          if      (!tlb_vec_q[hit_idx].read &&  tlb_vec_q[hit_idx].execute && !mxr_bit_i) l2tlb_exception = PageFault;
          else if ( tlb_vec_q[hit_idx].user &&  priv_mode_ls_i == S        && !sum_bit_i) l2tlb_exception = PageFault;
          else if (!tlb_vec_q[hit_idx].user &&  priv_mode_ls_i == U                     ) l2tlb_exception = PageFault;
        end
        endcase
      end
      // Can raise access exceptions!
      t0_t1_PTWAns: begin
        if        (t0_t1_req_q_i.destination == ITLB) begin
          if      (!t0_t1_req_q_i.wrx_bits.x               )                             l2tlb_exception = PageFault;
          else if ( t0_t1_req_q_i.u_bit && priv_mode_i == S)                             l2tlb_exception = PageFault;
          else if (!t0_t1_req_q_i.u_bit && priv_mode_i == U)                             l2tlb_exception = PageFault;
        end else if (t0_t1_req_q_i.destination == DTLB) begin
          if      (!t0_t1_req_q_i.wrx_bits.r &&  t0_t1_req_q_i.wrx_bits.x && !mxr_bit_i) l2tlb_exception = PageFault;
          else if ( t0_t1_req_q_i.u_bit      &&  priv_mode_ls_i == S      && !sum_bit_i) l2tlb_exception = PageFault;
          else if (!t0_t1_req_q_i.u_bit      &&  priv_mode_ls_i == U                   ) l2tlb_exception = PageFault;
        end
      end
    endcase
  end

  //--------------\\
  // FLUSH VECTOR \\
  //--------------\\

  // Flush Vector
  always_comb begin
    t1_t0_req_o.flush_vec = '0;
    case (t0_t1_req_q_i.req_type)
      t0_t1_FlushASID: begin
        for (int k = 0; k < N_WAY; k++) begin
          t1_t0_req_o.flush_vec[k] = ((flush_asid_i == tlb_vec_q[k].asid) && !tlb_vec_q[k].glob) ? tlb_vec_q[k].valid : 1'b0;
        end
      end
      // Selective flush on the page: it depends on the page size
      t0_t1_FlushPage: begin
        for (int k = 0; k < N_WAY; k++) begin
          // MebiPage
          if (tlb_vec_q[k].mebi) begin
            t1_t0_req_o.flush_vec[k] = (page_to_be_flushed[T-1-:MT] == tlb_vec_q[k].tag[T-1-:MT]) ? tlb_vec_q[k].valid : 1'b0;
          // GibiPage
          end else if (tlb_vec_q[k].gibi) begin
            t1_t0_req_o.flush_vec[k] = (page_to_be_flushed[T-1-:GT] == tlb_vec_q[k].tag[T-1-:GT]) ? tlb_vec_q[k].valid : 1'b0;
          // KibiPage
          end else begin
            t1_t0_req_o.flush_vec[k] = (page_to_be_flushed == tlb_vec_q[k].tag) ? tlb_vec_q[k].valid : 1'b0;
          end
        end
      end
    endcase
  end

  //-------------------\\
  // REPLACEMENT BLOCK \\
  //-------------------\\

  assign hit_vec_o          = hit_vec;
  assign valid_tlb_access_o = (t0_t1_req_q_i.req_type == t0_t1_KibiRead ||
                               t0_t1_req_q_i.req_type == t0_t1_MebiRead ||
                               t0_t1_req_q_i.req_type == t0_t1_GibiRead    ) ? hit : 1'b0;
  assign valid_tlb_read_o   = (t0_t1_req_q_i.req_type == t0_t1_KibiRead ||
                               t0_t1_req_q_i.req_type == t0_t1_MebiRead ||
                               t0_t1_req_q_i.req_type == t0_t1_GibiRead ||
                               t0_t1_req_q_i.req_type == t0_t1_PTWAns      ) ? 1'b1 : 1'b0;

  //------------\\
  // t1 CONTROL \\
  //------------\\

  // Combinatorial control to control the MSHR add-entry, the back request type and valid, the L1 answer valid
  always_comb begin
    add_mshr_entry_o        = 1'b0;
    l2tlb_l1tlb_ans_o.valid = 1'b0;
    t1_t0_req_o.valid       = 1'b0;
    t1_t0_req_o.req_type    = t1_t0_MebiRead;
    if (!abort_i) begin
      case (t0_t1_req_q_i.req_type)
        t0_t1_KibiRead: begin
          t1_t0_req_o.req_type    = t1_t0_MebiRead;
          t1_t0_req_o.valid       = (!hit) ? 1'b1 : 1'b0;
          l2tlb_l1tlb_ans_o.valid = ( hit) ? 1'b1 : 1'b0;
        end
        t0_t1_MebiRead: begin
          t1_t0_req_o.req_type    = t1_t0_GibiRead;
          t1_t0_req_o.valid       = (!hit) ? 1'b1 : 1'b0;
          l2tlb_l1tlb_ans_o.valid = ( hit) ? 1'b1 : 1'b0;
        end
        // Update the MSHR only if a GibiPage read misses. No stalls can occurs, because if the request is performed, there is enaugh space.
        t0_t1_GibiRead: begin
          add_mshr_entry_o        = (!hit) ? 1'b1 : 1'b0;
          l2tlb_l1tlb_ans_o.valid = ( hit) ? 1'b1 : 1'b0;
        end
        t0_t1_FlushASID, t0_t1_FlushPage: begin
          t1_t0_req_o.valid       = 1'b1;
          t1_t0_req_o.req_type    = t1_t0_FlushMasked;
        end
        // Back write request only if no exceptions
        t0_t1_PTWAns: begin
          t1_t0_req_o.valid       = ((t0_t1_req_q_i.exception) == NoException && (l2tlb_exception == NoException)) ? 1'b1 : 1'b0;
          t1_t0_req_o.req_type    = t1_t0_ReplaceLine;
          l2tlb_l1tlb_ans_o.valid = 1'b1;
        end
      endcase
    end
  end

  //------------------------------\\
  // REPLACEMENT BLOCK CONTROLLER \\
  //------------------------------\\

  // Update replacement unit when a replace occurs
  assign replacing_an_entry_o = (t1_t0_req_o.req_type == t1_t0_ReplaceLine) ? 1'b1 : 1'b0;

  // Valid vector assignment
  for (genvar k = 0; k < N_WAY; k++) begin
    assign valid_vec_o[k] = tlb_vec_q[k].valid;
  end

  // The replacement index is created in t0 and is given to the replacement block

  //-----------------------\\
  // t1 -> t0 BACK REQUEST \\
  //-----------------------\\

  // The valid and the req_type are generated in the t1 control block, the flush_vec is defined in the comparison block

  // The right portion of the VPN is selected in t0
  assign t1_t0_req_o.vpn         = t0_t1_req_q_i.vpn;
  assign t1_t0_req_o.ppn         = t0_t1_req_q_i.ppn;
  assign t1_t0_req_o.page_type   = t0_t1_req_q_i.page_type;
  assign t1_t0_req_o.wrx_bits    = t0_t1_req_q_i.wrx_bits;
  assign t1_t0_req_o.d_bit       = t0_t1_req_q_i.d_bit;
  assign t1_t0_req_o.g_bit       = t0_t1_req_q_i.g_bit;
  assign t1_t0_req_o.u_bit       = t0_t1_req_q_i.u_bit;
  assign t1_t0_req_o.destination = t0_t1_req_q_i.destination;

  //---------------\\
  // L1 TLB ANSWER \\
  //---------------\\

  // The valid is generated in the t1 control block

  // If a PTW exception occurred, let it reaches the L1 TLB. Otherwise, update it with the internal L2 exception signal
  assign l2tlb_l1tlb_ans_o.exception   = (t0_t1_req_q_i.exception == NoException) ? l2tlb_exception : t0_t1_req_q_i.exception;
  // Page size
  always_comb begin
    // Default: KibiPage
    l2tlb_l1tlb_ans_o.page_type = KibiPage;
    if (hit) begin
      // TLB MebiPage
      if      (tlb_vec_q[hit_idx].mebi && !tlb_vec_q[hit_idx].gibi) l2tlb_l1tlb_ans_o.page_type = MebiPage;
      // TLB GibiPage
      else if (!tlb_vec_q[hit_idx].mebi && tlb_vec_q[hit_idx].gibi) l2tlb_l1tlb_ans_o.page_type = GibiPage;
    end else begin
      // Page Size set by the PTW answer
      l2tlb_l1tlb_ans_o.page_type = t0_t1_req_q_i.page_type;
    end
  end
  // Other
  assign l2tlb_l1tlb_ans_o.vpn         = t0_t1_req_q_i.vpn;
  assign l2tlb_l1tlb_ans_o.ppn         = (hit) ? tlb_vec_q[hit_idx].ppn     : t0_t1_req_q_i.ppn;
  assign l2tlb_l1tlb_ans_o.w_bit       = (hit) ? tlb_vec_q[hit_idx].write   : t0_t1_req_q_i.wrx_bits.w;
  assign l2tlb_l1tlb_ans_o.r_bit       = (hit) ? tlb_vec_q[hit_idx].read    : t0_t1_req_q_i.wrx_bits.r;
  assign l2tlb_l1tlb_ans_o.x_bit       = (hit) ? tlb_vec_q[hit_idx].execute : t0_t1_req_q_i.wrx_bits.x;
  assign l2tlb_l1tlb_ans_o.d_bit       = (hit) ? tlb_vec_q[hit_idx].dirty   : t0_t1_req_q_i.d_bit;
  assign l2tlb_l1tlb_ans_o.g_bit       = (hit) ? tlb_vec_q[hit_idx].glob    : t0_t1_req_q_i.g_bit;
  assign l2tlb_l1tlb_ans_o.u_bit       = (hit) ? tlb_vec_q[hit_idx].user    : t0_t1_req_q_i.u_bit;
  assign l2tlb_l1tlb_ans_o.destination = t0_t1_req_q_i.destination;

endmodule
