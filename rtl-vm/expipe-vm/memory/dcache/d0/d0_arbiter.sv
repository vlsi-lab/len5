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
// File: d0_arbiter.sv
// Author: Matteo Perotti
// Date: 24/10/2019
// Description: acknowledge the block to be served and say if d0 is currently enabled

import memory_pkg::*;

module d0_arbiter (
    // The scheduled block
    input  d0_winner_e winner_i,
    // Next state ready? Stalled?
    input  logic       d1_rdy_i,
    input  logic       d1_stalled_i,
    // Ack signals*
    output logic       l2c_rdy_o,
    output logic       lsq_rdy_o,
    // Is there any request which is being served in this cycle?
    output logic       d0_enable
);

  always_comb begin
    // Default assignments
    l2c_rdy_o = 1'b0;
    lsq_rdy_o = 1'b0;
    d0_enable = 1'b0;
    // Behavioural logic
    case (winner_i)
      RstBlock: begin
        d0_enable = 1'b1;
      end
      D1: begin
        d0_enable = 1'b1;
      end
      L2Cache: begin
        if (d1_rdy_i || d1_stalled_i) begin
          l2c_rdy_o = 1'b1;
          d0_enable = 1'b1;
        end
      end
      UpdateL2: begin
        if (d1_rdy_i) begin
          d0_enable = 1'b1;
        end
      end
      LSQ: begin
        if (d1_rdy_i) begin
          lsq_rdy_o = 1'b1;
          d0_enable = 1'b1;
        end
      end
    endcase
  end

endmodule

// * "d1" and "L2-update block" do not need any acknowledge signal.
//   "d1" has the highest priority and every request is always executed.
//   "L2-update block" is not controlled by the execution of its request, it is directly controlled by d1
//   "Reset block" is the first to act, no ack is necessary.
