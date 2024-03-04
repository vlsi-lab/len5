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
// File: d0_scheduler.sv
// Author: Matteo Perotti
// Date: 23/10/2019
// Description: schedule the next block to be served (the winner block)
// Details: fixed priority from higher (left) to lower (right): D1, L2-C, UpdateL2, LSQ

import memory_pkg::*;

module d0_scheduler (
    // Valid signals from the competing blocks
    input  logic       rst_val_i,
    input  logic       d1_val_i,
    input  logic       l2c_val_i,
    input  logic       upd_val_i,
    input  logic       lsq_val_i,
    // The winner block
    output d0_winner_e winner_o
);

  always_comb begin
    // Default assignment
    winner_o = Nobody;
    // Behavioural priority logic
    if (rst_val_i) begin
      winner_o = RstBlock;
    end else if (d1_val_i) begin
      winner_o = D1;
    end else if (l2c_val_i) begin
      winner_o = L2Cache;
    end else if (upd_val_i) begin
      winner_o = UpdateL2;
    end else if (lsq_val_i) begin
      winner_o = LSQ;
    end
  end

endmodule

