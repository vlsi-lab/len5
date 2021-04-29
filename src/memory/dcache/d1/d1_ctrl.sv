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
// File: d1_ctrl.sv
// Author: Matteo Perotti
// Date: 27/10/2019
// Description: set control for the d1 stage
// Details: set control starting from the req type, the hit/miss infromation and condition of
//          the MSHR

import memory_pkg::*;

module d1_ctrl
(
  // Main
  input  logic            clr_mshr_i,
  // D1 encoded request
  input  d0_d1_req_type_e d1_req_type_i,
  input  logic            d1_req_valid_i,
  // Hit information
  input  logic            cache_hit_i,
  input  logic            mshr_hit_i,
  input  logic            wbb_line_addr_hit_i,
  input  logic            wbb_tag_hit_i,
  // Line dirty from replace vector
  input  logic            line_dirty_i,
  // At least one dirty line in the set
  input  logic            at_least_one_dirty_i, // Used during an L2 updating process
  // MSHR and WBB full
  input  logic            mshr_full_i,
  input  logic            wbb_full_i,
  // From CU
  input  logic            d1_stalled_i,
  input  logic            replaying_i,
  // Information to drive the data flow and control d0
  output d1_d0_req_type_e d1_d0_req_type_o,
  output logic            d1_d0_req_valid_o,
  // MSHR and WBB control from d1
  output logic            mshr_add_data_o,
  output logic            mshr_clr_hit_line_o,
  output logic            mshr_clr_all_o,
  output logic            wbb_add_data_o,
  output logic            wbb_clr_hit_line_o,
  output logic            wbb_switch_hit_line_o,
  output logic            wbb_wup_hit_line_o,
  // To CU
  output logic            lets_stall_o,             // ask for a stall in the next cycle
  output logic            lets_replay_o,            // ask for a replay in the next cycle
  output logic            lets_wait_wbb_o,          // ask for a stall in the next cycle
  output logic            wbb_will_free_o,          // unstall the CU and keep updating L2
  // Replay registers control
  output logic            replay_reg_en_o,
  // Replay registers instruction data
  output d1_d0_req_type_e d1_d0_req_type_repl_d_o,
  // LSQ Output Validation
  output logic            d1_lsq_ans_valid_o,
  output logic            d1_lsq_ans_was_store_o,
  // Auxiliary signal for the dirty vec one hotter block (to control the L2 update counter)
  output logic            l2_update_is_writing_wbb_o,
  // WBB is forwarding a line to the cache in this cycle
  output logic            wbb_d0_fwd_o,
  // d1 ready for d0 requests?
  output logic            d1_d0_req_rdy_o
);

  assign mshr_clr_all_o = clr_mshr_i; // Clear all the MSHR (e.g. after a mispredicted branch)

  always_comb begin
    // Default assignment, no default needed in the case
    d1_d0_req_type_o            = LoadReplay; // Valid only if d1_d0_req_valid_o is asserted
    d1_d0_req_valid_o           = 1'b0;       // Validate the d1_d0_req_type_o signal
    mshr_add_data_o             = 1'b0;       // Primary miss: add the addr line to an MSHR entry
    mshr_clr_hit_line_o         = 1'b0;       // L2 returned a line: clear the corresponding MSRH entry
    wbb_add_data_o              = 1'b0;       // Write Back the line (write it into the buffer)
    wbb_clr_hit_line_o          = 1'b0;       // Line correctly written back
    wbb_switch_hit_line_o       = 1'b0;       // Switch the current cache line with the WBB read one
    wbb_wup_hit_line_o          = 1'b0;       // Wake-up the hit line to let it perform the req another time
    lets_stall_o                = 1'b0;       // Ask the CU to stall
    lets_replay_o               = 1'b0;       // Ask the CU to use the replay registers as source
    lets_wait_wbb_o             = 1'b0;       // Ask the CU to stall (WBB request when it's full during a L2 updating)
    wbb_will_free_o             = 1'b0;       // Inform the CU that the next cycle there will be a free WBB entry
    replay_reg_en_o             = 1'b0;       // Let the replay regs sample
    d1_d0_req_type_repl_d_o     = LoadReplay; // Instruction type to the replay regs
    d1_lsq_ans_valid_o          = 1'b0;       // Valid result to the LSQ
    d1_lsq_ans_was_store_o      = 1'b0;       // The instruction was a store
    l2_update_is_writing_wbb_o  = 1'b0;       // WBB is being written during an L2 updating (to the d1 L2-updating block)
    wbb_d0_fwd_o                = 1'b0;       // If it is asserted, write back to l2c is blocked in this cycle
    d1_d0_req_rdy_o             = 1'b1;       // d1 ready for new d0 req? Default: ready
    if (d1_req_valid_i) begin
      case (d1_req_type_i)
        d0_d1_Load: begin
          // The best thing after pizza: a cache hit
          if (cache_hit_i) begin
            d1_lsq_ans_valid_o = 1'b1;
          // Line in the WBB. Request a forward, check dirty and conditionally switch the lines, enable the replay registers and inform the CU
          end else if (wbb_line_addr_hit_i) begin
            d1_d0_req_type_o                        = WriteDirtyLine;
            d1_d0_req_valid_o                       = 1'b1;
            replay_reg_en_o                         = 1'b1;
            d1_d0_req_type_repl_d_o                 = LoadReplay;
            lets_replay_o                           = 1'b1;
            wbb_d0_fwd_o                            = 1'b1;
            if (line_dirty_i) wbb_switch_hit_line_o = 1'b1;
            else              wbb_clr_hit_line_o    = 1'b1;
          // Miss -> We write the MSHR and query L2 for primary misses only. Secondary misses are filtered
          end else if (!mshr_hit_i) begin
            if (!mshr_full_i) begin
              mshr_add_data_o = 1'b1;
            // Stall and wait for an MSHR free entry (d1 NOT ready for d0 req)
            end else begin
              replay_reg_en_o         = 1'b1;
              d1_d0_req_type_repl_d_o = LoadReplay;
              lets_stall_o            = 1'b1;
              d1_d0_req_rdy_o         = 1'b0;
            end
          end
        end
        d0_d1_Store: begin
          if (cache_hit_i) begin
            d1_lsq_ans_valid_o     = 1'b1;
            d1_d0_req_type_o       = WriteStore;
            d1_d0_req_valid_o      = 1'b1;
            d1_lsq_ans_was_store_o = 1'b1;
          end else if (wbb_line_addr_hit_i) begin
            d1_d0_req_type_o                        = WriteDirtyLine;
            d1_d0_req_valid_o                       = 1'b1;
            replay_reg_en_o                         = 1'b1;
            d1_d0_req_type_repl_d_o                 = StoreReplay;
            lets_replay_o                           = 1'b1;
            wbb_d0_fwd_o                            = 1'b1;
            if (line_dirty_i) wbb_switch_hit_line_o = 1'b1;
            else              wbb_clr_hit_line_o    = 1'b1;
          end else if (!mshr_hit_i) begin
            if (!mshr_full_i) mshr_add_data_o = 1'b1;
            // Stall and wait for an MSHR free entry (d1 not ready for d0 req)
            else begin
              replay_reg_en_o         = 1'b1;
              d1_d0_req_type_repl_d_o = StoreReplay;
              lets_stall_o            = 1'b1;
              d1_d0_req_rdy_o         = 1'b0;
            end
          end
        end
        d0_d1_L2WBBWakeUp: begin
          // No tag comparison requested to speed up execution in the worst case
          if (wbb_line_addr_hit_i) begin
            wbb_wup_hit_line_o = 1'b1;            // Wake-Up the WBB entry
          end
        end
        d0_d1_L2StHit: begin
          // Clear an entry only if is the SAME entry which requested a data (TAG comparison requested)
          if (wbb_tag_hit_i) begin
            wbb_clr_hit_line_o = 1'b1;            // Free a WBB entry
            wbb_will_free_o    = 1'b1;            // Inform the CU
          end
        end
        // L2 has returned the requested line after a miss
        d0_d1_ReplaceReq: begin
          // If the line is still needed
          if (mshr_hit_i) begin
            mshr_clr_hit_line_o = 1'b1;           // clear the line from the MSHR
            if (line_dirty_i) begin               // line to be replaced dirty?
              wbb_add_data_o    = 1'b1;           // write the dirty line into the buffer
            end
            d1_d0_req_type_o    = WriteCleanLine; // d0 immediate write line request
            d1_d0_req_valid_o   = 1'b1;           // valid d0 request
            if (d1_stalled_i) begin
             lets_replay_o      = 1'b1;           // replay, there will be space into the MSHR now
            end
          end
        end
        d0_d1_UpdateL2: begin
          if (at_least_one_dirty_i && wbb_full_i) begin
            lets_wait_wbb_o            = 1'b1;
          end else if (at_least_one_dirty_i && !wbb_full_i) begin
            d1_d0_req_type_o           = CleanDirty;
            d1_d0_req_valid_o          = 1'b1;
            wbb_add_data_o             = 1'b1;
            l2_update_is_writing_wbb_o = 1'b1;
          // If the set is clean, don't let d0 inject any instruction while the L2 Updating counter is incrementing
          end else if (!at_least_one_dirty_i) begin
            d1_d0_req_type_o           = WaitL2UpdatingCnt;
            d1_d0_req_valid_o          = 1'b1;
          end
        end
      endcase
    end
  end

endmodule
