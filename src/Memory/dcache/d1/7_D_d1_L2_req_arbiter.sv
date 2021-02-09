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
// File: d1_L2_req_arbiter.sv
// Author: Matteo Perotti
// Date: 27/10/2019
// Description: select the correct speaker (MSHR or WB Buffer) following a precise policy
// Details: to speed up the execution and avoid deadlocks, in case of ties the default
//          priority goes to MSHR only if its pending requests are less then the number of
//          buffer free entries

`include "memory_pkg.sv"
import memory_pkg::*;

module d1_L2_req_arbiter
(
  // Valid requests from MSHR and WBB
  input logic              mshr_l2c_req_valid_i,
  input logic              wbb_l2c_req_valid_i,
  // L2C req ready
  input logic              l2c_l1dc_req_rdy_i,
  // Information to handle the ties
  input mshr_pending_req_t mshr_pending_req_i,
  input wbb_free_entries_t wbb_free_entries_i,
  // WBB -> D-Cache fwd info
  input  logic             wbb_d0_fwd_i,
  // Scheduled block
  output mshr_wbb_winner_e winner_o,
  // MSHR and WBB req ready
  output logic             mshr_l2c_transaction_ok_o,
  output logic             wbb_l2c_transaction_ok_o,
  // Any request valid
  output logic             d1_l2c_valid_o
);

  always_comb begin
    // Default: no valid request
    winner_o       = MSHR;
    d1_l2c_valid_o = 1'b0;
    // WBB -> let it pass
    if (!mshr_l2c_req_valid_i && wbb_l2c_req_valid_i) begin
      winner_o    = WBB;
      // Valid request only if the buffer is not forwarding that cycle
      if (!wbb_d0_fwd_i) d1_l2c_valid_o = 1'b1;
    // Buffer can tolerate an eviction of dirty line
    end else if (mshr_pending_req_i < wbb_free_entries_i) begin
      // MSHR -> let it pass
      if (mshr_l2c_req_valid_i && !wbb_l2c_req_valid_i) begin
        winner_o       = MSHR;
        d1_l2c_valid_o = 1'b1;
      // Tie -> MSHR priority
      end else if (mshr_l2c_req_valid_i && wbb_l2c_req_valid_i) begin
        winner_o       = MSHR;
        d1_l2c_valid_o = 1'b1;
      end
    // Buffer can't tolerate an eviction of dirty line
    end else begin
      // MSHR -> mask its request
      if (mshr_l2c_req_valid_i && !wbb_l2c_req_valid_i) begin
        d1_l2c_valid_o = 1'b0;
      // Tie -> WBB priority
      end else if (mshr_l2c_req_valid_i && wbb_l2c_req_valid_i) begin
        winner_o = WBB;
        // Valid request only if the buffer is not forwarding that cycle
        if (!wbb_d0_fwd_i) d1_l2c_valid_o = 1'b1;
      end
    end
  end

  assign mshr_l2c_transaction_ok_o = (l2c_l1dc_req_rdy_i && d1_l2c_valid_o && winner_o == MSHR) ? 1'b1 : 1'b0;
  assign wbb_l2c_transaction_ok_o  = (l2c_l1dc_req_rdy_i && d1_l2c_valid_o && winner_o == WBB)  ? 1'b1 : 1'b0;

endmodule
