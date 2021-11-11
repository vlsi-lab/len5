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
// File: L2_tlb_mshr.sv
// Author: Matteo Perotti
// Date: 04/11/2019
// Description: L2-TLB MSHR
// Details: FIFO MSHR with no holes. Requests are served in-order.

import memory_pkg::*;

module L2_tlb_mshr
#(
  N = L2_TLB_MSHR_ENTRIES
)
(
  // Main
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         clr_mshr_i,
  // Control
  input  logic         add_entry_i,
  input  logic         rm_entry_i,
  input  logic         let_entry_waiting_i,
  // Status
  output logic         req_available_o,
  output logic         mshr_full_o,
  // Data
  input vpn_t         vpn_i,
  input  tlb_arb_tag_e destination_i,
  output vpn_t         ptw_ans_vpn_o,
  output vpn_t         ptw_req_vpn_o,
  output tlb_arb_tag_e destination_o
);

  localparam LOG2_N = $clog2(N);

  // The MSHR remembers also the request type (either I or D)
  typedef struct packed {
    vpn_t         vpn;
    tlb_arb_tag_e destination;
    logic         valid;
  } l2tlb_mshr_entry_t;

  logic [LOG2_N-1:0] free_ptr, older_ptr;
  l2tlb_mshr_entry_t mshr_entry_q [N];
  l2tlb_mshr_entry_t waiting_entry_q;
  logic [N-1:0]      valid_vec;

  // FIFO pointers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      free_ptr    <= '0;
      older_ptr   <= '0;
    end else if (clr_mshr_i) begin
      free_ptr    <= '0;
      older_ptr   <= '0;
    end else if (add_entry_i) begin
      if (free_ptr == N) begin
        free_ptr  <= '0;
      end else begin
        free_ptr  <= free_ptr + 1;
      end
    end else if (let_entry_waiting_i) begin
      if (older_ptr == N) begin
        older_ptr <= '0;
      end else begin
        older_ptr <= older_ptr + 1;
      end
    end
  end

  // MSHR entries
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int k = 0; k < N; k++) begin
        mshr_entry_q[k].vpn              <= '0;
        mshr_entry_q[k].valid            <= 1'b0;
        mshr_entry_q[k].destination      <= ITLB;
      end
    end else if (clr_mshr_i) begin
      for (int k = 0; k < N; k++) begin
        mshr_entry_q[k].vpn              <= '0;
        mshr_entry_q[k].valid            <= 1'b0;
        mshr_entry_q[k].destination      <= ITLB;
      end
   end else if (add_entry_i) begin
      mshr_entry_q[free_ptr].vpn         <= vpn_i;
      mshr_entry_q[free_ptr].destination <= destination_i;
      mshr_entry_q[free_ptr].valid       <= 1'b1;
    end else if (let_entry_waiting_i) begin
      mshr_entry_q[older_ptr].valid      <= 1'b0;
    end
  end

  // MSHR separated waiting entry *
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      waiting_entry_q.vpn         <= '0;
      waiting_entry_q.valid       <= 1'b0;
      waiting_entry_q.destination <= ITLB;
    end else if (clr_mshr_i) begin
      waiting_entry_q.vpn         <= '0;
      waiting_entry_q.valid       <= 1'b0;
      waiting_entry_q.destination <= ITLB;
    end else if (rm_entry_i) begin
      waiting_entry_q.valid       <= 1'b0;
    end else if (let_entry_waiting_i) begin
      waiting_entry_q             <= mshr_entry_q[older_ptr];
    end
  end

  // MSHR-full output status
  always_comb begin
    for (int k = 0; k < N; k++) begin
      valid_vec[k]   = mshr_entry_q[k].valid;
    end
  end
  assign mshr_full_o = &valid_vec;

  // MSHR-request available status
  assign req_available_o = |valid_vec;

  // Output data
  assign ptw_req_vpn_o   = mshr_entry_q[older_ptr].vpn;
  assign ptw_ans_vpn_o   = waiting_entry_q.vpn;
  assign destination_o   = waiting_entry_q.destination;

endmodule

// * The valid signal in the waiting entry is not necessary because the main hypothesis is that each
//   PTW answer is linked to a waiting request, and the PTW cannot answer is no valid request was
//   done and is pending in that moment.
