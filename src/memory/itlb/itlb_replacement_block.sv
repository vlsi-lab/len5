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
// File: itlb_replacement_block.sv
// Author: Matteo Perotti
// Date: 30/10/2019
// Description: i-TLB replacement block - NRU policy

`include "len5_pkg.sv"
`include "memory_pkg.sv"
//import mmm_pkg::*;
import len5_pkg::*;
import memory_pkg::*;

module itlb_replacement_block
#(
  N = I_TLB_ENTRIES
)
(
  // Main
  input  logic         clk_i,
  input  logic         rst_ni,
  // Valid vector (for not-valid entries filling). If invalid entries are present, fill them first on a replace
  input  logic [N-1:0] itlb_valid_vec_i,
  // Hit vector (for NRU filling)
  input  logic         itlb_req_valid_i,
  input  logic [N-1:0] itlb_hit_vec_i,
  input  logic         itlb_hit_i,
  // Replacement vector
  output logic [N-1:0] itlb_replacement_vec_o
);

  localparam LOG2_N = $clog2(N);

  logic              update_safe_reg;
  logic [N-1:0]      safe_vec, unsafe_vec;
  logic [LOG2_N-1:0] unsafe_vec_enc;
  logic [N-1:0]      one_hot_unsafe_vec;
  logic              all_entries_valid;
  logic [N-1:0]      one_hot_invalid_vec;
  logic [N-1:0]      safe_reg_en;
  logic [N-1:0]      safe_reg_cond_en;
  logic              accessing_the_last_unsafe;
  logic [LOG2_N-1:0] invalid_vec_enc;
  logic [N-1:0]      itlb_invalid_vec;
  logic              only_one_unsafe;

  // Update safe reg in this cycle (an access is being performed)
  assign update_safe_reg           = (itlb_req_valid_i && itlb_hit_i) ? 1'b1 : 1'b0;
  // There is only one unsafe
  assign only_one_unsafe           = (one_hot_unsafe_vec == unsafe_vec) ? 1'b1 : 1'b0;
  // There is only one entry which is unsafe and this access is on that one
  assign accessing_the_last_unsafe = (only_one_unsafe && (one_hot_unsafe_vec == itlb_hit_vec_i)) ? 1'b1 : 1'b0;
  // Enable vector for the safe register. It will be effective only if a tlb access is performed (update_safe_reg)
  assign safe_reg_cond_en          = (accessing_the_last_unsafe) ? '1 : itlb_hit_vec_i;
  // The effective enable for the safe register
  assign safe_reg_en               = (update_safe_reg) ? safe_reg_cond_en : '0;

  // Safe register: the enable is different for each flip flop
  for (genvar k = 0; k < N; k++) begin : safe_reg
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        safe_vec[k] <= 1'b0;
      end else if (safe_reg_en[k]) begin
        safe_vec[k] <= itlb_hit_vec_i[k];
      end
    end
  end

  // Encode the bits that are not safe
  assign unsafe_vec = ~safe_vec;
  always_comb begin
    unsafe_vec_enc = '0;
    for (int k = N-1; k >= 0; k--) begin
      if (unsafe_vec[k]) unsafe_vec_enc = k;
    end
  end

  // One-hotted unsafe_vec
  always_comb begin
    one_hot_unsafe_vec = '0;
    for (int k = N-1; k >= 0; k--) begin
      if (unsafe_vec_enc == k) one_hot_unsafe_vec[k] = 1'b1;
    end
  end

  // Encode the bits which are invalid
  assign itlb_invalid_vec = ~itlb_valid_vec_i;
  always_comb begin
    invalid_vec_enc = '0;
    for (int k = N-1; k >= 0; k--) begin
      if (itlb_invalid_vec[k]) invalid_vec_enc = k;
    end
  end

  // One-hotted valid vector
  always_comb begin
    one_hot_invalid_vec = '0;
    for (int k = N-1; k >= 0; k--) begin
      if (invalid_vec_enc == k) one_hot_invalid_vec[k] = 1'b1;
    end
  end

  // Mux selector: if all entries are valid, use NRU policy. Otherwise, fill invalid entries first
  assign all_entries_valid = &itlb_valid_vec_i;
  // Replacement vector effective selection
  assign itlb_replacement_vec_o = (all_entries_valid) ? one_hot_unsafe_vec : one_hot_invalid_vec;

endmodule
