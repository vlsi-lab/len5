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
// File: l2c_arbiter.sv
// Author: Matteo Perotti
// Date: 30/10/2019
// Description: schedule the next l2c request and the next l2c response

import memory_pkg::*;
import len5_pkg::*;
//import mmm_pkg::*;

module l2c_arbiter
(
  // Main
  input  logic            clk_i,
  input  logic            rst_ni,
  // Request channel
  input  var l1dc_l2c_req_t   l1dc_l2arb_req_i,       // D-Cache request to L2-Cache
  input  var icache_l2_req_t  icache_l2arb_req_i,     // I-Cache request to L2-Cache
  input  var ptw_l2c_req_t    ptw_l2arb_req_i,        // PTW request to L2-Cache
  output l2arb_l2c_req_t  l2arb_l2c_req_o,        // Final L2-Cache request
  // Request channel ready
  input  logic            l2c_l2arb_req_rdy_i,    // L2-Cache ready for a request
  output logic            l2arb_l1dc_req_rdy_o,   // L2-Cache ready for the D-Cache
  output logic            l2arb_icache_req_rdy_o, // L2-Cache ready for the I-Cache
  output logic            l2arb_ptw_req_rdy_o,    // L2-Cache ready for the PTW
  // Answer channel
  input  var l2c_l2arb_ans_t  l2c_l2arb_ans_i,        // L2-Cache answer to someone
  output l2c_l1dc_ans_t   l2arb_l1dc_ans_o,       // L2-Cache answer to D-Cache
  output l2_icache_ans_t  l2arb_icache_ans_o,     // L2-Cache answer to I-Cache
  output l2c_ptw_ans_t    l2arb_ptw_ans_o,        // L2-Cache answer to PTW
  // Answer channel ready
  input  logic            l1dc_l2c_ans_rdy_i,     // D-Cache ready for L2-Cache answer
  input  logic            icache_l2c_ans_rdy_i,   // I-Cache ready for L2-Cache answer (fixed 1'b1)
  input  logic            ptw_l2c_ans_rdy_i,      // PTW ready for L2-Cache answer
  output logic            l2arb_l2c_ans_rdy_o     // Someone is ready for the answer
);

  l2arb_ans_destination_e    ans_destination;           // Destination of the L2C answer
  l2arb_req_sender_e         req_sender;                // Sender of the request to L2C
  l2arb_i_d_priority_e       i_d_priority;              // Actual priority to I-Cache or D-Cache
  l2arb_i_d_winner_e         i_d_winner;                // Scheduled speaker between I-Cache and D-Cache
  logic                      i_d_winner_valid;          // Is there at least one speaker between I-Cache and D-Cache?
  l2arb_cache_ptw_priority_e cache_ptw_priority;        // Actual priority to Cache or PTW
  l2arb_cache_ptw_winner_e   cache_ptw_winner;          // Scheduled speaker between Cache and PTW
  logic                      i_d_tie;                   // Both I-Cache and D-Cache want to speak
  logic                      cache_ptw_tie;             // Both a Cache and the PTW want to speak
  logic                      i_d_priority_update;       // Update the tie priority relative to I-Cache and D-Cache
  logic                      cache_ptw_priority_update; // Update the tie priority relative to Cache and PTW
  // Auxiliary
  logic [(XLEN-PADDR_LEN)-1:0] paddr_zero_filling;

  //-------------------\\
  // REQUEST SCHEDULER \\
  //-------------------\\

  // Priority T-FF: I-Cache - D-Cache
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      i_d_priority <= l2arb_id_prio_ICache;
    end else if (i_d_priority_update) begin
      i_d_priority <= (i_d_priority == l2arb_id_prio_ICache) ? l2arb_id_prio_DCache : l2arb_id_prio_ICache;
    end
  end

  // Update the priority when I-Cache or D-Cache complete a valid transaction and there was a tie between them
  assign i_d_priority_update = (i_d_tie && (cache_ptw_winner == l2arb_cptw_win_Cache) && l2c_l2arb_req_rdy_i) ? 1'b1 : 1'b0;

  // First couple of priorities: I-Cache - D-Cache
  always_comb begin
    i_d_winner_valid   = 1'b0;
    i_d_winner         = l2arb_id_win_DCache;
    i_d_tie            = 1'b0;
    if (!l1dc_l2arb_req_i.valid && icache_l2arb_req_i.valid) begin
      i_d_winner_valid = 1'b1;
      i_d_winner       = l2arb_id_win_ICache;
    end else if (l1dc_l2arb_req_i.valid && !icache_l2arb_req_i.valid) begin
      i_d_winner_valid = 1'b1;
      i_d_winner       = l2arb_id_win_DCache;
    end else if (l1dc_l2arb_req_i.valid && icache_l2arb_req_i.valid) begin
      i_d_tie          = 1'b1;
      i_d_winner_valid = 1'b1;
      i_d_winner = (i_d_priority == l2arb_id_prio_ICache) ? l2arb_id_win_ICache : l2arb_id_win_DCache;
    end
  end

  // Priority T-FF: Cache - PTW
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cache_ptw_priority <= l2arb_cptw_prio_Cache;
    end else if (cache_ptw_priority_update) begin
      cache_ptw_priority <= (cache_ptw_priority == l2arb_cptw_prio_Cache) ? l2arb_cptw_prio_PTW : l2arb_cptw_prio_Cache;
    end
  end

  // Update the priority when Cache or PTW complete a valid transaction and there was a tie between them
  assign cache_ptw_priority_update = (cache_ptw_tie && l2c_l2arb_req_rdy_i) ? 1'b1 : 1'b0;

  // Second couple of priorities: Cache - PTW
  always_comb begin
    l2arb_l2c_req_o.valid   = 1'b0;
    cache_ptw_winner        = l2arb_cptw_win_Cache;
    cache_ptw_tie           = 1'b0;
    if (!i_d_winner_valid && ptw_l2arb_req_i.valid) begin
      l2arb_l2c_req_o.valid = 1'b1;
      cache_ptw_winner      = l2arb_cptw_win_PTW;
    end else if (i_d_winner_valid && !ptw_l2arb_req_i.valid) begin
      l2arb_l2c_req_o.valid = 1'b1;
      cache_ptw_winner      = l2arb_cptw_win_Cache;
    end else if (i_d_winner_valid && ptw_l2arb_req_i.valid) begin
      cache_ptw_tie         = 1'b1;
      l2arb_l2c_req_o.valid = 1'b1;
      cache_ptw_winner      = (cache_ptw_priority == l2arb_cptw_prio_Cache) ? l2arb_cptw_win_Cache : l2arb_cptw_win_PTW;
    end
  end

  //-----------------\\
  // REQUEST ARBITER \\
  //-----------------\\

  // Dispatch the L2C ready to the correct block
  always_comb begin
    l2arb_l1dc_req_rdy_o   = 1'b0;
    l2arb_icache_req_rdy_o = 1'b0;
    l2arb_ptw_req_rdy_o    = 1'b0;
    // There is a valid request to L2C
    if (l2arb_l2c_req_o.valid) begin
      if (cache_ptw_winner ==  l2arb_cptw_win_PTW) begin
        l2arb_ptw_req_rdy_o    = l2c_l2arb_req_rdy_i;
      end else if (i_d_winner == l2arb_id_win_ICache) begin
        l2arb_icache_req_rdy_o = l2c_l2arb_req_rdy_i;
      end else if (i_d_winner == l2arb_id_win_DCache) begin
        l2arb_l1dc_req_rdy_o   = l2c_l2arb_req_rdy_i;
      end
    end
  end

  //------------------\\
  // REQUEST DATA SEL \\
  //------------------\\

  assign paddr_zero_filling       = '0;

  always_comb begin
    l2arb_l2c_req_o.paddr         = '0;
    l2arb_l2c_req_o.req_type      = IReadLine;
    if (l2arb_l2c_req_o.valid) begin
      if (cache_ptw_winner == l2arb_cptw_win_PTW) begin
        // 56 bit PTE address to 64 bit full address filling
        l2arb_l2c_req_o.paddr     = {paddr_zero_filling, ptw_l2arb_req_i.pte_paddr};
        l2arb_l2c_req_o.req_type  = PTWLoad;
      end else if (i_d_winner == l2arb_id_win_ICache) begin
        {l2arb_l2c_req_o.paddr.tag, l2arb_l2c_req_o.paddr.idx} = {icache_l2arb_req_i.line_addr.tag, icache_l2arb_req_i.line_addr.idx};
        l2arb_l2c_req_o.req_type  = IReadLine;
      end else if (i_d_winner == l2arb_id_win_DCache) begin
        {l2arb_l2c_req_o.paddr.tag, l2arb_l2c_req_o.paddr.idx} = {l1dc_l2arb_req_i.line_addr.tag, l1dc_l2arb_req_i.line_addr.idx};
        l2arb_l2c_req_o.req_type  = (l1dc_l2arb_req_i.is_store) ? DWriteLine : DReadLine;
      end
    end
  end

  assign l2arb_l2c_req_o.line     = l1dc_l2arb_req_i.line;
  assign l2arb_l2c_req_o.wbb_tag  = l1dc_l2arb_req_i.wbb_tag;

  //--------------------\\
  // ANSWER REDIRECTION \\
  //--------------------\\

  // Who is the answer recipient
  always_comb begin
    ans_destination = l2arb_ans_NoWhere;
    case (l2c_l2arb_ans_i.ans_type)
      l2arb_s0_ILineRead:                                             ans_destination = l2arb_ans_ICache;
      l2arb_s0_DLineRead, l2arb_s0_DWbbWakeUp, l2arb_s0_DLineWritten: ans_destination = l2arb_ans_DCache;
      l2arb_s0_PTWLoad:                                               ans_destination = l2arb_ans_PTW;
    endcase
  end

  // Route the answer data
  // To D-Cache
  assign l2arb_l1dc_ans_o.line_addr = {l2c_l2arb_ans_i.paddr.tag, l2c_l2arb_ans_i.paddr.idx};
  assign l2arb_l1dc_ans_o.line      = l2c_l2arb_ans_i.line;
  assign l2arb_l1dc_ans_o.wbb_tag   = l2c_l2arb_ans_i.wbb_tag;
  always_comb begin
    l2arb_l1dc_ans_o.ans_type = ReplaceLine;
    case (l2c_l2arb_ans_i.ans_type)
      l2arb_s0_DLineRead:    l2arb_l1dc_ans_o.ans_type = ReplaceLine;
      l2arb_s0_DWbbWakeUp:   l2arb_l1dc_ans_o.ans_type = WWBWakeUp;
      l2arb_s0_DLineWritten: l2arb_l1dc_ans_o.ans_type = StoreHit;
    endcase
  end
  // To I-Cache
  assign l2arb_icache_ans_o.line = l2c_l2arb_ans_i.line;
  // To PTW
  assign l2arb_ptw_ans_o.pte     = l2c_l2arb_ans_i.data;

  // Route the answer valid signal
  assign l2arb_l1dc_ans_o.valid   = (ans_destination == l2arb_ans_DCache) ? l2c_l2arb_ans_i.valid : 1'b0;
  assign l2arb_icache_ans_o.valid = (ans_destination == l2arb_ans_ICache) ? l2c_l2arb_ans_i.valid : 1'b0;
  assign l2arb_ptw_ans_o.valid    = (ans_destination == l2arb_ans_PTW)    ? l2c_l2arb_ans_i.valid : 1'b0;

  //----------------------\\
  // ANSWER READY ARBITER \\
  //----------------------\\

  // The routing depends on the L2C answer
  always_comb begin
    l2arb_l2c_ans_rdy_o = 1'b0;
    case (ans_destination)
      l2arb_ans_DCache: l2arb_l2c_ans_rdy_o = l1dc_l2c_ans_rdy_i;
      l2arb_ans_ICache: l2arb_l2c_ans_rdy_o = icache_l2c_ans_rdy_i;
      l2arb_ans_PTW:    l2arb_l2c_ans_rdy_o = ptw_l2c_ans_rdy_i;
    endcase
  end

endmodule
