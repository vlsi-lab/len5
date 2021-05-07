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
// File: tlb_arbiter.sv
// Author: Matteo Perotti
// Date: 30/10/2019
// Description: schedule the next L2 TLB request and the next L2 TLB answer and drive the data
// Details: Fair Round Robin priority imposed with a T-FF in case of ties for the requests

import memory_pkg::*;

module tlb_arbiter
(
  // Main
  input  logic             clk_i,
  input  logic             rst_ni,
  // Request channel
  input  var itlb_l2tlb_req_t  itlb_l2tlb_req_i,
  input  var dtlb_l2tlb_req_t  dtlb_l2tlb_req_i,
  output l1tlb_l2tlb_req_t l1tlb_l2tlb_req_o,
  // Request channel ready
  input  logic             l2tlb_l1tlb_req_rdy_i,
  output logic             l2tlb_itlb_req_rdy_o,
  output logic             l2tlb_dtlb_req_rdy_o,
  // Answer channel
  input  var l2tlb_l1tlb_ans_t l2tlb_l1tlb_ans_i,
  output l2tlb_itlb_ans_t  l2tlb_itlb_ans_o,
  output l2tlb_dtlb_ans_t  l2tlb_dtlb_ans_o,
  // Answer channel ready
  input  logic             itlb_l2tlb_ans_rdy_i,
  input  logic             dtlb_l2tlb_ans_rdy_i,
  output logic             l1tlb_l2tlb_ans_rdy_o
);

  typedef enum logic [1:0] {
    Nobody,
    ITLB_win,
    DTLB_win
  } tlb_arb_winner_e;

  tlb_arb_winner_e req_winner;
  tlb_arb_winner_e tie_winner;
  logic            is_tie;
  logic            valid_transaction;
  logic            resolved_tie;

  //----------\\
  // REQUESTS \\
  //----------\\

  // If no ties: pass who needs. If ties: one tie for the i-TLB, then one tie for the d-TLB

  // Scheduler
  always_comb begin
    // If no requests, nobody is requesting
    req_winner                = Nobody;
    l1tlb_l2tlb_req_o.valid   = 1'b0;
    if          ( itlb_l2tlb_req_i.valid && !dtlb_l2tlb_req_i.valid) begin
      req_winner = ITLB_win;
      l1tlb_l2tlb_req_o.valid = 1'b1;
    end else if (!itlb_l2tlb_req_i.valid &&  dtlb_l2tlb_req_i.valid) begin
      req_winner = DTLB_win;
      l1tlb_l2tlb_req_o.valid = 1'b1;
    end else if ( itlb_l2tlb_req_i.valid &&  dtlb_l2tlb_req_i.valid) begin
      req_winner = tie_winner;
      l1tlb_l2tlb_req_o.valid = 1'b1;
    end
  end

  // Arbiter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tie_winner <= ITLB_win;
    end else if (resolved_tie) begin
      tie_winner <= (req_winner == ITLB_win) ? DTLB_win : ITLB_win;
    end
  end

  // Tie policy updating
  assign is_tie            = (itlb_l2tlb_req_i.valid &&  dtlb_l2tlb_req_i.valid) ? 1'b1 : 1'b0;
  assign valid_transaction = ((itlb_l2tlb_req_i.valid || dtlb_l2tlb_req_i.valid) && l2tlb_l1tlb_req_rdy_i) ? 1'b1 : 1'b0;
  assign resolved_tie      = (is_tie && valid_transaction) ? 1'b1 : 1'b0;

  // Data and ready selection
  assign l1tlb_l2tlb_req_o.vpn    = (req_winner == ITLB_win) ? itlb_l2tlb_req_i.vpn  : dtlb_l2tlb_req_i.vpn;
  assign l1tlb_l2tlb_req_o.origin = (req_winner == ITLB_win) ? ITLB : DTLB;
  assign l2tlb_itlb_req_rdy_o     = (req_winner == ITLB_win) ? l2tlb_l1tlb_req_rdy_i : 1'b0;
  assign l2tlb_dtlb_req_rdy_o     = (req_winner == DTLB_win) ? l2tlb_l1tlb_req_rdy_i : 1'b0;

  //---------\\
  // ANSWERS \\
  //---------\\

  // The answer is always addressed to a particular block

  // Answer valid dispatching
  assign l2tlb_itlb_ans_o.valid     = (l2tlb_l1tlb_ans_i.destination == ITLB) ? l2tlb_l1tlb_ans_i.valid : 1'b0;
  assign l2tlb_dtlb_ans_o.valid     = (l2tlb_l1tlb_ans_i.destination == DTLB) ? l2tlb_l1tlb_ans_i.valid : 1'b0;

  // Ready selector
  assign l1tlb_l2tlb_ans_rdy_o      = (l2tlb_l1tlb_ans_i.destination == ITLB) ? itlb_l2tlb_ans_rdy_i : dtlb_l2tlb_ans_rdy_i;

  // Data connections
  // I-TLB
  assign l2tlb_itlb_ans_o.ppn       = l2tlb_l1tlb_ans_i.ppn;
  assign l2tlb_itlb_ans_o.page_type = l2tlb_l1tlb_ans_i.page_type;
  assign l2tlb_itlb_ans_o.exception = l2tlb_l1tlb_ans_i.exception;
  assign l2tlb_itlb_ans_o.g_bit     = l2tlb_l1tlb_ans_i.g_bit;
  assign l2tlb_itlb_ans_o.u_bit     = l2tlb_l1tlb_ans_i.u_bit;
  // D-TLB
  assign l2tlb_dtlb_ans_o.vpn       = l2tlb_l1tlb_ans_i.vpn;
  assign l2tlb_dtlb_ans_o.ppn       = l2tlb_l1tlb_ans_i.ppn;
  assign l2tlb_dtlb_ans_o.page_type = l2tlb_l1tlb_ans_i.page_type;
  assign l2tlb_dtlb_ans_o.w_bit     = l2tlb_l1tlb_ans_i.w_bit;
  assign l2tlb_dtlb_ans_o.r_bit     = l2tlb_l1tlb_ans_i.r_bit;
  assign l2tlb_dtlb_ans_o.x_bit     = l2tlb_l1tlb_ans_i.x_bit;
  assign l2tlb_dtlb_ans_o.d_bit     = l2tlb_l1tlb_ans_i.d_bit;
  assign l2tlb_dtlb_ans_o.g_bit     = l2tlb_l1tlb_ans_i.g_bit;
  assign l2tlb_dtlb_ans_o.u_bit     = l2tlb_l1tlb_ans_i.u_bit;
  assign l2tlb_dtlb_ans_o.exception = l2tlb_l1tlb_ans_i.exception;

endmodule
