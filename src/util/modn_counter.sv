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

module modn_counter
#(
    N = 16
)
(
    // Input signals 
    input logic clk_i,
    input logic rst_n_i, // Asynchronous reset
    input logic en_i,
    input logic clr_i, // Synchronous clear

    // Output signals 
   // output logic [$clog2(N)-1:0] count_o, // Counter value 
   output logic [3-1:0] count_o, // Counter value 
    output logic tc_o // Terminal count: '1' when count_o = N-1
);

// Terminal count
assign tc_o = count_o == N-1;

// Main counting process. The counter clears when reaching the threshold
always_ff @ (posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        count_o <= 0; // Asynchronous reset
    end
    else if (clr_i || tc_o) begin
        count_o <= 0; // Synchronous clear when requested or when reaching the threshold
    end
    else if (en_i) begin
        count_o <= count_o + 1;
    end
end

endmodule