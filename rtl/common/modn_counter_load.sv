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
// File: modn_counter.sv
// Author: Michele Caon
// Date: 17/10/2019

module modn_counter_load #(
  parameter int unsigned N = 16,
  parameter logic [$clog2(N)-1:0] INIT = '0  // initial value at reset and clear
) (
  // Input signals
  input logic                 clk_i,
  input logic                 rst_ni,        // Asynchronous reset
  input logic                 en_i,          // enable count
  input logic                 en_l,          // enable load, synchronous load
  input logic [$clog2(N)-1:0] load_value_i,  // value to load
  input logic                 clr_i,         // Synchronous clear

  // Output signals
  output logic [$clog2(N)-1:0] count_o,  // Counter value
  output logic                 tc_o      // Terminal count: '1' when count_o = N-1
);

  // Terminal count
  assign tc_o = int'(count_o) == N - 1;

  // Main counting process. The counter clears when reaching the threshold
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      count_o <= INIT;  // Asynchronous reset
    end else if (clr_i) begin
      count_o <= INIT;  // Synchronous clear when requested or when reaching the threshold
    end else if (en_l) begin
      count_o <= load_value_i;
    end else if (en_i && tc_o) begin
      count_o <= '0;
    end else if (en_i) begin
      count_o <= count_o + 1;
    end
  end
endmodule
