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
// File: fair_2way_arbiter.sv
// Author: Michele Caon
// Date: 29/10/2019

module fair_2way_arbiter #(
  parameter type DATA_T = logic
) (
  input logic clk_i,
  input logic rst_ni,

  // Handshaking
  input  logic valid_a_i,
  input  logic valid_b_i,
  input  logic ready_i,
  output logic valid_o,
  output logic ready_a_o,
  output logic ready_b_o,

  // Data
  input  DATA_T data_a_i,
  input  DATA_T data_b_i,
  output DATA_T data_o
);
  // DEFINITIONS
  logic last_served_a;
  logic sel_a;

  // Ready generation
  // ----------------
  always_comb begin : ready_gen
    // Default (downstram not ready)
    ready_a_o = 1'b0;
    ready_b_o = 1'b0;
    sel_a     = 1'b1;

    // Downstream ready
    if (ready_i) begin
      if (valid_a_i && !valid_b_i) begin
        ready_a_o = 1'b1;
        ready_b_o = 1'b0;
        sel_a     = 1'b1;
      end else if (valid_b_i && !valid_a_i) begin
        ready_a_o = 1'b0;
        ready_b_o = 1'b1;
        sel_a     = 1'b0;
      end else if (valid_a_i && valid_b_i) begin
        ready_a_o = ~last_served_a;
        ready_b_o = last_served_a;
        sel_a     = ~last_served_a;
      end
    end
  end

  // Output multiplexer
  // ------------------
  assign data_o = (sel_a) ? data_a_i : data_b_i;

  // -----------------------
  // LAST SERVED ON CONFLICT
  // -----------------------
  // This flip-flop stores the last input that was accepted during a conflict (both valid asserted). When a new conflict takes place, the other input is served instead.
  always @(posedge clk_i or negedge rst_ni) begin : last_served_ff
    if (!rst_ni) begin
      last_served_a <= 1'b0;
    end else if (valid_a_i && valid_b_i && ready_i) last_served_a <= ~last_served_a;
  end

endmodule
