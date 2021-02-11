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
// File: L2_tlb_t0.sv
// Author: Matteo Perotti
// Date: 04/11/2019
// Description: first part of the L2-TLB
// Details: schedule the requests, control the memory, feed the t0 -> t1 registers

`include "memory_pkg.sv"
import memory_pkg::*;

module L2_tlb_t0
#(
  A     = L2_TLB_IDX_LEN,
  N_WAY = L2_TLB_ASSOCIATIVITY
)
(
  // Control from the system
  input  logic             abort_i,
  // Actual ASID from "satp" register
  input  asid_t            base_asid_i,
  // (Flush unit -> t0) request channel
  input  tlb_flush_e       flush_type_i,
  input  logic [A-1:0]     flush_idx_i,
  input  logic             flush_req_valid_i,
  // (t0 -> Flush unit) control
  output logic             flush_idx_cnt_en_o,
  // (L1 TLB Arbiter -> L2 TLB) request channel
  input  l1tlb_l2tlb_req_t l1tlb_l2tlb_req_i,
  output logic             l2tlb_l1tlb_req_rdy_o,
  // (PTW -> L2 TLB) answer channel
  input  ptw_l2tlb_ans_t   ptw_l2tlb_ans_i,
  output logic             l2tlb_ptw_ans_rdy_o,
  // t0 -> memory
  output l2tlb_dmem_ctrl_t data_mem_ctrl_o [N_WAY],
  output l2tlb_tmem_ctrl_t tag_mem_ctrl_o [N_WAY],
  output logic [A-1:0]     tlb_addr_o,
  output l2tlb_entry_t     tlb_input_entry_o,
  // t0 -> registers
  output t0_t1_req_t       t0_t1_req_d_o,
  output logic             t0_t1_reg_en_o,
  // (t1 -> t0) request channel
  input  t1_t0_req_t       t1_t0_req_i,
  // (MSHR -> t0) data
  input  vpn_t             mshr_vpn_i,
  input  tlb_arb_tag_e     mshr_destination_i,
  // (MSHR -> t0) status
  input  logic             mshr_full_i,
  // (t0 -> MSHR) control
  output logic             rm_mshr_entry_o,
  // (t0 -> Replacement block) index
  output logic [A-1:0]     replace_idx_o,
  // (Replacement block -> t0)
  input  logic [N_WAY-1:0] replace_vec_i
);

  localparam TAG_LEN        = L2_TLB_TAG_LEN;
  localparam TMEM_ENTRY_LEN = L2_TLB_TMEM_ENTRY_LEN;

  // The L2 TLB can receive requests from its t1 part, from the Flush unit, from the PTW, from an L1 TLB (descending priority)
  typedef enum logic [2:0] {
    Nobody,
    L1TLBReq,
    PTWAns,
    FlushReq,
    t1Req
  } t0_winner_e;

  t0_winner_e                t0_winner;
  logic [TMEM_ENTRY_LEN-2:0] be_one_hot_lsb_zero_filling;
  logic [TMEM_ENTRY_LEN-1:0] be_one_hot_lsb;
  // Vector to create the TAG
  logic [VPN_LEN-1:0]        vpn_to_tag_converter;

  //-------------------------------------\\
  // SCHEDULER, ARBITER, REGISTER ENABLE \\
  //-------------------------------------\\

  // Scheduler (schedule the block and catch the valid)
  always_comb begin
    t0_winner             = Nobody;
    if (t1_t0_req_i.valid) begin
      t0_winner           = t1Req;
    end else if (flush_req_valid_i) begin
      t0_winner           = FlushReq;
    end else if (ptw_l2tlb_ans_i.valid) begin
      t0_winner           = PTWAns;
    end else if (l1tlb_l2tlb_req_i.valid && !mshr_full_i) begin
      t0_winner           = L1TLBReq;
    end
  end

  // Enable for the (t0 -> t1) registers. A t0 action does not necessarily correspond to a linked t1 request
  always_comb begin
    t0_t1_reg_en_o         = 1'b0;
    case (t0_winner)
      L1TLBReq: begin
        t0_t1_reg_en_o     = 1'b1;
      end
      PTWAns: begin
        t0_t1_reg_en_o     = 1'b1;
      end
      FlushReq: begin
        case (flush_type_i)
          FlushASID, FlushPage: begin
            t0_t1_reg_en_o = 1'b1;
          end
        endcase
      end
      t1Req: begin
        case (t1_t0_req_i.req_type)
          t1_t0_MebiRead, t1_t0_GibiRead: begin
            t0_t1_reg_en_o = 1'b1;
          end
        endcase
      end
    endcase
  end

  // Acknowledgement unit
  assign l2tlb_l1tlb_req_rdy_o = (t0_winner == L1TLBReq) ? 1'b1 : 1'b0;
  assign l2tlb_ptw_ans_rdy_o   = (t0_winner == PTWAns  ) ? 1'b1 : 1'b0;

  //-------------------\\
  // MEMORY CONTROLLER \\
  //-------------------\\

  // One Hot Byte Enable with the 1 in the LSB. Used to flush the valid bit
  assign be_one_hot_lsb_zero_filling = '0;
  assign be_one_hot_lsb = {be_one_hot_lsb_zero_filling, 1'b1};

  // Memory controlled via CS, WE, BE
  always_comb begin
    for (int z = 0; z < N_WAY; z++) begin
      data_mem_ctrl_o[z] = '0;
      tag_mem_ctrl_o[z]  = '0;
    end
    case (t0_winner)
      L1TLBReq: begin
        for (int k = 0; k < N_WAY; k++) begin
          data_mem_ctrl_o[k].cs = 1'b1;
          data_mem_ctrl_o[k].be = '1;
          tag_mem_ctrl_o[k].cs  = 1'b1;
          tag_mem_ctrl_o[k].be  = '1;
        end
      end
      // Perform a full read only if there are not exceptions!
      PTWAns: begin
        if (ptw_l2tlb_ans_i.exception == NoException) begin
          for (int k = 0; k < N_WAY; k++) begin
            data_mem_ctrl_o[k].cs = 1'b1;
            data_mem_ctrl_o[k].be = '1;
            tag_mem_ctrl_o[k].cs  = 1'b1;
            tag_mem_ctrl_o[k].be  = '1;
          end
        end
      end
      FlushReq: begin
        case (flush_type_i)
          FlushAll: begin
            // Clear all immediately
            for (int k = 0; k < N_WAY; k++) begin
              tag_mem_ctrl_o[k].cs  = 1'b1;
              tag_mem_ctrl_o[k].we  = 1'b1;
              tag_mem_ctrl_o[k].be  = be_one_hot_lsb;
            end
          end
          FlushASID, FlushPage: begin
            // Read only and inject a back-write in t1
            for (int k = 0; k < N_WAY; k++) begin
              data_mem_ctrl_o[k].cs = 1'b1;
              data_mem_ctrl_o[k].be = '1;
              tag_mem_ctrl_o[k].cs  = 1'b1;
              tag_mem_ctrl_o[k].be  = '1;
            end
          end
        endcase
      end
      t1Req: begin
        case (t1_t0_req_i.req_type)
          t1_t0_MebiRead, t1_t0_GibiRead: begin
            for (int k = 0; k < N_WAY; k++) begin
              data_mem_ctrl_o[k].cs = 1'b1;
              data_mem_ctrl_o[k].be = '1;
              tag_mem_ctrl_o[k].cs  = 1'b1;
              tag_mem_ctrl_o[k].be  = '1;
            end
          end
          // Back-write for replacement only if no exceptions
          t1_t0_ReplaceLine: begin
            for (int k = 0; k < N_WAY; k++) begin
              data_mem_ctrl_o[k].cs = (replace_vec_i[k]) ? 1'b1 : 1'b0;
              data_mem_ctrl_o[k].we = (replace_vec_i[k]) ? 1'b1 : 1'b0;
              data_mem_ctrl_o[k].be = '1;
              tag_mem_ctrl_o[k].cs  = (replace_vec_i[k]) ? 1'b1 : 1'b0;
              tag_mem_ctrl_o[k].we  = (replace_vec_i[k]) ? 1'b1 : 1'b0;
              tag_mem_ctrl_o[k].be  = '1;
            end
          end
          t1_t0_FlushMasked: begin
            for (int k = 0; k < N_WAY; k++) begin
              tag_mem_ctrl_o[k].cs  = (t1_t0_req_i.flush_vec[k]) ? 1'b1 : 1'b0;
              tag_mem_ctrl_o[k].we  = (t1_t0_req_i.flush_vec[k]) ? 1'b1 : 1'b0;
              tag_mem_ctrl_o[k].be  = be_one_hot_lsb;
            end
          end
        endcase
      end
    endcase
  end

  //----------------\\
  // DATA SELECTION \\
  //----------------\\

  // To the registers
  always_comb begin
    t0_t1_req_d_o.vpn               = '0;
    t0_t1_req_d_o.destination       = ITLB;
    t0_t1_req_d_o.req_type          = t0_t1_Idle;
    case (t0_winner)
      L1TLBReq: begin
        t0_t1_req_d_o.vpn           = l1tlb_l2tlb_req_i.vpn;
        t0_t1_req_d_o.destination   = l1tlb_l2tlb_req_i.origin;
        t0_t1_req_d_o.req_type      = t0_t1_KibiRead;
      end
      PTWAns: begin
        t0_t1_req_d_o.vpn           = mshr_vpn_i;
        t0_t1_req_d_o.destination   = mshr_destination_i;
        t0_t1_req_d_o.req_type      = t0_t1_PTWAns;
      end
      FlushReq: begin
        t0_t1_req_d_o.vpn[0][A-1:0] = flush_idx_i; // *
        case (flush_type_i)
          FlushASID: begin
            t0_t1_req_d_o.req_type  = t0_t1_FlushASID;
          end
          FlushPage: begin
            t0_t1_req_d_o.req_type  = t0_t1_FlushASID;
          end
        endcase
      end
      t1Req: begin
        t0_t1_req_d_o.vpn           = t1_t0_req_i.vpn;
        t0_t1_req_d_o.destination   = t1_t0_req_i.destination;
        case (t1_t0_req_i.req_type)
          t1_t0_MebiRead: begin
            t0_t1_req_d_o.req_type  = t0_t1_MebiRead;
          end
          t1_t0_GibiRead: begin
            t0_t1_req_d_o.req_type  = t0_t1_GibiRead;
          end
        endcase
      end
    endcase
  end
  assign t0_t1_req_d_o.ppn       = ptw_l2tlb_ans_i.ppn;
  assign t0_t1_req_d_o.page_type = ptw_l2tlb_ans_i.page_type;
  assign t0_t1_req_d_o.exception = ptw_l2tlb_ans_i.exception;
  assign t0_t1_req_d_o.wrx_bits  = ptw_l2tlb_ans_i.wrx_bits;
  assign t0_t1_req_d_o.d_bit     = ptw_l2tlb_ans_i.d_bit;
  assign t0_t1_req_d_o.g_bit     = ptw_l2tlb_ans_i.g_bit;
  assign t0_t1_req_d_o.u_bit     = ptw_l2tlb_ans_i.u_bit;

  // To the memory
  always_comb begin
    tlb_addr_o              = '0;
    tlb_input_entry_o.valid = 1'b0; // Useful only for write requests (write or flush)
    case (t0_winner)
      // A KibiPage read only request
      L1TLBReq: begin
        tlb_addr_o = l1tlb_l2tlb_req_i.vpn[0][A-1:0]; // it was -> mshr_vpn_i[0][A-1:0]; ... maybe a bug?
      end
      // A read only request. The index is chosen depending on the page type
      PTWAns: begin
        // L2 TLB address
        case (ptw_l2tlb_ans_i.page_type)
          KibiPage: begin
            tlb_addr_o = mshr_vpn_i[0][A-1:0];
          end
          MebiPage: begin
            tlb_addr_o = mshr_vpn_i[1][A-1:0];
          end
          GibiPage: begin
            tlb_addr_o = mshr_vpn_i[2][A-1:0];
          end
        endcase
      end
      // It either flush immediately or read
      FlushReq: begin
        tlb_addr_o              = flush_idx_i;
        tlb_input_entry_o.valid = 1'b0;
      end
      // It can be a read request, a write or a flush
      t1Req: begin
        case (t1_t0_req_i.req_type)
          t1_t0_MebiRead: begin
            tlb_addr_o = t1_t0_req_i.vpn[1][A-1:0];
          end
          t1_t0_GibiRead: begin
            tlb_addr_o = t1_t0_req_i.vpn[2][A-1:0];
          end
          // Write in the right set (depending on the page type)
          t1_t0_ReplaceLine: begin
            case (t1_t0_req_i.page_type)
              KibiPage: begin
                tlb_addr_o = mshr_vpn_i[0][A-1:0];
              end
              MebiPage: begin
                tlb_addr_o = mshr_vpn_i[1][A-1:0];
              end
              GibiPage: begin
                tlb_addr_o = mshr_vpn_i[2][A-1:0];
              end
            endcase
            tlb_input_entry_o.valid = 1'b1;
          end
          t1_t0_FlushMasked: begin
            tlb_addr_o              = t1_t0_req_i.vpn[0][A-1:0];
            tlb_input_entry_o.valid = 1'b0;
          end
        endcase
      end
    endcase
  end
  // TAG creation
  assign vpn_to_tag_converter      = t1_t0_req_i.vpn;
  assign tlb_input_entry_o.tag     = vpn_to_tag_converter[VPN_LEN-1:A]; // The TAG is always complete and will be treaten differently only in t1
  // Other TLB input assignments
  assign tlb_input_entry_o.ppn     = t1_t0_req_i.ppn;
  assign tlb_input_entry_o.asid    = base_asid_i;
  assign tlb_input_entry_o.glob    = t1_t0_req_i.g_bit;
  assign tlb_input_entry_o.user    = t1_t0_req_i.u_bit;
  assign tlb_input_entry_o.dirty   = t1_t0_req_i.d_bit;
  assign tlb_input_entry_o.gibi    = (t1_t0_req_i.page_type == GibiPage) ? 1'b1 : 1'b0;
  assign tlb_input_entry_o.mebi    = (t1_t0_req_i.page_type == MebiPage) ? 1'b1 : 1'b0;
  assign tlb_input_entry_o.read    = t1_t0_req_i.wrx_bits.r;
  assign tlb_input_entry_o.write   = t1_t0_req_i.wrx_bits.w;
  assign tlb_input_entry_o.execute = t1_t0_req_i.wrx_bits.x;

  // To the replacement block (the index is the same of the accessed set in the memory)
  assign replace_idx_o = tlb_addr_o;

  //-----------------\\
  // MSHR CONTROLLER \\
  //-----------------\\

  // Remove the waiting entry when the PTW request is accepted and the replace occurs
  assign rm_mshr_entry_o = (t0_winner == PTWAns) ? 1'b1 : 1'b0;

  //-----------------------\\
  // FLUSH UNIT CONTROLLER \\
  //-----------------------\\

  // Update the flush address only if we are flushing and (we are flushing all (update every cycle) or when t1 does the back write (update once in two cycles))
  assign flush_idx_cnt_en_o = ((t0_winner == FlushReq) && (flush_type_i == FlushAll || t1_t0_req_i.req_type == t1_t0_FlushMasked)) ? 1'b1 : 1'b0;

endmodule

// * "mshr_vpn_i[0][A-1:0]" works only because A < VPN_PART_LEN
