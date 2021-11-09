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
// File: updateL2_block.sv
// Author: Matteo Perotti
// Date: 23/10/2019
// Description: block to handle an L2 update request

import memory_pkg::*;

module updateL2_block
#(
  IDX_LEN = DCACHE_L1_IDX_A_LEN
)
(
  // Main
  input  logic          clk_i,
  input  logic          rst_ni,
  // From the main system
  input  logic          synch_l1dc_l2c_i,  // Synchronize the L2-Cache with the D-Cache
  // From d1
  input  logic          en_cnt_i,          // Address the next set
  input  logic          wbb_empty_i,       // the wbb is empty
  // To d0
  output upd_l1dc_req_t upd_l1dc_req_o,    // Synch request to the L1 D-Cache
  // To the system
  output logic          l2c_update_done_o  // L2-Cache synch done
);

  typedef enum logic [1:0] {
    StIdle, StUpdating, StWaitingBuf, StDone
  } updL2_state_e;

  updL2_state_e state_d, state_q;

  logic [IDX_LEN-1:0] cnt;
  logic               synch;
  logic               valid;
  logic               done;
  logic               tc;    // terminal count

  assign synch                = synch_l1dc_l2c_i;
  assign upd_l1dc_req_o.idx   = cnt;
  assign upd_l1dc_req_o.valid = valid;
  assign l2c_update_done_o    = done;

  //---------\\
  // COUNTER \\
  //---------\\

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      cnt <= '0;
    end else if (en_cnt_i && state_q == StUpdating) begin
      cnt <= cnt + 1;
    end
  end

  assign tc = &cnt; // tc asserted if (cnt == MAX)

  //--------------\\
  // CONTROL UNIT \\
  //--------------\\

  always_comb begin
    // Default assignment
    state_d = StIdle;
    valid   = 1'b0;
    done    = 1'b0;
    // Next state and output definition
    case (state_q)
      StIdle: begin
        if (synch) state_d = StUpdating;
        else       state_d = StIdle;
      end
      StUpdating: begin
        if (tc && en_cnt_i) state_d = StWaitingBuf;
        else                state_d = StUpdating;
        valid = 1'b1;
      end
      StWaitingBuf: begin
        state_d = (wbb_empty_i) ? StDone : StWaitingBuf;
      end      
      StDone: begin
        state_d = StIdle;
        done    = 1'b1;
      end
      default: sate_d = StIdle;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      state_q <= StIdle;
    end else begin
      state_q <= state_d;
    end
  end

endmodule
