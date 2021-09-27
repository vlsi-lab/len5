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
// File: d1_stall_replay_cu.sv
// Author: Matteo Perotti
// Date: 27/10/2019
// Description: simple CU to handle the stalls and the replay of the instructions from the
//              replay registers
// Details: the enabling of the replay regs is not controlled by this CU, but by the d1_ctrl
//          combinatorial network

import memory_pkg::*;

module d1_stall_replay_cu
(
  // Main
  input  logic clk_i,
  input  logic rst_ni,
  // From d1_ctrl -> they will act in the next cycle
  input  logic lets_stall_i,    // new primary miss when MSHR is full
  input  logic lets_replay_i,   // above situation resolved or (buffer -> cache) fwd
  input  logic lets_wait_wbb_i, // new line to be evicted when WBB is full
  input  logic wbb_will_free_i, // the buffer will be free in the next cycle
  // Source from replay registers
  output logic replaying_o,
  // d1 is stalled
  output logic d1_stalled_o
);

  typedef enum logic [1:0] {
    StDecode, StStall, StReplay, StFullBuffer
  } state_t;

  state_t state_d, state_q;

  always_comb begin
    state_d      = StDecode;
    replaying_o  = 1'b0;
    d1_stalled_o = 1'b0;
    case (state_q)
      // Normal operations: replay regs are empty
      StDecode: begin
        if      (lets_stall_i)    state_d = StStall;      // Stall
        else if (lets_replay_i)   state_d = StReplay;     // Replay after a Buffer -> Cache forwarding
        else if (lets_wait_wbb_i) state_d = StFullBuffer; // Stall
        else                      state_d = StDecode;     // Normal operations
      end
      // d1 stalled: replay regs full but they output is not used
      StStall: begin
        d1_stalled_o = 1'b1;
        if (lets_replay_i) state_d = StReplay;                 // Replay after a stall
        else          state_d = StStall;                  // Keep stalled
      end
      // Replay regs full and their output is being used
      StReplay: begin
        replaying_o = 1'b1;
      end
      // Wait for the buffer to free an entry
      StFullBuffer: begin
        d1_stalled_o = 1'b1;
        if (wbb_will_free_i) state_d = StDecode;          // Repeat the L2 updating
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StDecode;
    end else begin
      state_q <= state_d;
    end
  end

endmodule
