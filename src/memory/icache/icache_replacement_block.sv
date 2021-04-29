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
// File: icache_replacement_block.sv
// Author: Matteo Perotti
// Date: 29/10/2019
// Description: indicate the correct line to be replaced when a replace occurs
// Details: random replacement if all the lines of the sets are valid, otherwise invalid first

//import mmm_pkg::*;
import len5_pkg::*;
import memory_pkg::*;

`include "one_hot_shift_reg.sv"

module icache_replacement_block
(
  // Main
  input  logic                clk_i,
  input  logic                rst_ni,
  // Cache valid vector
  input  icache_valid_vec_t   valid_vec_i,
  // Replace request
  input  logic                update_replacement_i, // used to update the shift register and sample the valid addr
  // Replace vector
  output icache_replace_vec_t replace_vec_o
);

  localparam N_WAY      = ICACHE_L1_ASSOCIATIVITY;
  localparam LOG2_N_WAY = $clog2(N_WAY);

  icache_replace_vec_t   invalid_vec_q;
  logic [LOG2_N_WAY-1:0] invalid_vec_q_encoded;
  icache_replace_vec_t   shift_q;
  icache_replace_vec_t   first_invalid;
  logic                  any_invalid;

  // One hot shift register
  one_hot_shift_reg #(
    .REG_LEN(ICACHE_L1_ASSOCIATIVITY)
  ) i_one_hot_shift_reg (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .update_i(update_replacement_i),
    .output_o(shift_q)
  );

  // Invalid vector register
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      invalid_vec_q <= '0;
    end else if (update_replacement_i) begin
      invalid_vec_q <= ~valid_vec_i;
    end
  end

  // If at least one line in the set is not valid -> invalid first replace
  assign any_invalid = |invalid_vec_q;

  // first_invalid signal creation (to be optimized) - No need for an
  always_comb begin
    invalid_vec_q_encoded = '0;
    for (int k = N_WAY; k >= 0; k--) begin
      if (invalid_vec_q[k]) invalid_vec_q_encoded = k;
    end
  end
  always_comb begin
    first_invalid = '0;
    first_invalid[invalid_vec_q_encoded] = 1'b1;
  end

  // If not all the lines in the set are valid -> fill the not valid first
  assign replace_vec_o = (any_invalid) ? first_invalid : shift_q;


endmodule
