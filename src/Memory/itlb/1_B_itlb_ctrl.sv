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
// File: itlb_ctrl.sv
// Author: Matteo Perotti
// Date: 31/10/2019
// Description: combinatorial control for the i-TLB

`include "len5_pkg.sv"
`include "memory_pkg.sv"
//import mmm_pkg::*;
import len5_pkg::*;
import memory_pkg::*;

module itlb_ctrl
#(
  N = I_TLB_ENTRIES
)
(
  // From the system
  input logic          vmem_on_i,
  // From CU
  input logic          tlb_cond_ready_i,
  input logic          waiting_l2c_ans_i,
  // Flush type
  input  tlb_flush_e   flush_type_i,
  input  asid_t        flush_asid_i,
  input  vpn_t         flush_page_i,
  // From the TLB entries
  input  vpn_t         vpn_vec_q [N],
  input  asid_t        asid_vec_q [N],
  input  logic         glob_vec_q [N],
  input  logic         mebi_vec_q [N],
  input  logic         gibi_vec_q [N],
  // From comparison block
  input  logic         icache_tlb_req_valid_i,
  input  logic         itlb_hit_i,
  // Any exception
  input exception_e    itlb_exception_i,
  // From L2C
  input  logic         l2c_ans_valid_i,
  input  exception_e   l2c_ans_exception_i,
  // Flush control
  output logic         flush_o,
  output logic [N-1:0] flush_vec_o,
  // Flow control
  output logic         icache_req_rdy_o,
  output logic         icache_ans_valid_o,
  // Data flow control
  output logic         exception_reg_en_o,
  output logic         exception_reg_clr_o,
  output logic         replace_o
);

  //------------\\
  // FLUSH CTRL \\
  //------------\\

  // The flush can be generic or selective on the ASID (only for non-global pages) or on the leaf page
  always_comb begin
    flush_vec_o = '0;
    flush_o     = 1'b0;
    case (flush_type_i)
      FlushASID: begin
        flush_o     = 1'b1;
        for (int k = 0; k < N; k++) begin
          flush_vec_o[k] = ((asid_vec_q[k] == flush_asid_i) && !glob_vec_q[k]) ? 1'b1 : 1'b0;
        end
      end
      // The selective page flush depends on the page size
      FlushPage: begin
        flush_o     = 1'b1;
        for (int k = 0; k < N; k++) begin
          if (mebi_vec_q[k]) begin
            flush_vec_o[k] = (vpn_vec_q[k][2:1] == flush_page_i[2:1]) ? 1'b1 : 1'b0;
          end else if (gibi_vec_q[k]) begin
            flush_vec_o[k] = (vpn_vec_q[k][2] == flush_page_i[2]) ? 1'b1 : 1'b0;
          end else begin
            flush_vec_o[k] = (vpn_vec_q[k] == flush_page_i) ? 1'b1 : 1'b0;
          end
        end
      end
      // Flush all
      FlushAll: begin
        flush_o     = 1'b1;
        flush_vec_o = '1;
      end
    endcase
  end

  //-----------\\
  // FLOW CTRL \\
  //-----------\\

  always_comb begin
    icache_req_rdy_o       = 1'b0;
    icache_ans_valid_o     = 1'b0;
    exception_reg_en_o     = 1'b0;
    exception_reg_clr_o    = 1'b0;
    // Ready only if no valid request or valid request and (hit or pending exception)
    if (tlb_cond_ready_i && !icache_tlb_req_valid_i) begin
      icache_req_rdy_o     = 1'b1;
    end else if (tlb_cond_ready_i && icache_tlb_req_valid_i) begin
      // If valid request and hit or exception -> clear the exception register (it is used only after a replace)
      if (itlb_hit_i || (itlb_exception_i != NoException)) begin
        exception_reg_clr_o = 1'b1;
        icache_req_rdy_o    = 1'b1;
        icache_ans_valid_o  = 1'b1;
      end
    // Save exception and replace when l2c answers
    end else if (waiting_l2c_ans_i && l2c_ans_valid_i) begin
      exception_reg_en_o   = 1'b1;
    end
  end

  //--------------\\
  // REPLACE CTRL \\
  //--------------\\

  // If in the answer there is an exception, don't replace any page
  assign replace_o = (waiting_l2c_ans_i && l2c_ans_valid_i && (l2c_ans_exception_i == NoException)) ? 1'b1 : 1'b0;

endmodule
