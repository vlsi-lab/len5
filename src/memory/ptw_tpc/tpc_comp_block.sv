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
// File: tpc_comp_block.sv
// Author: Matteo Perotti
// Date: 14/10/2019
// Description: mmu_cache comparison block

`include "memory_pkg.sv"
import memory_pkg::*;

module tpc_comp_block
#(
  REG_ENTRIES  = MMUC_ENTRIES, // vector length
  HALF_TAG_LEN = VPN_PART_LEN  // 9 bit
)
(
  input  logic [1:0][HALF_TAG_LEN-1:0]                  tag_i,         // 9 bits VPN + 9 bits VPN = 18 bits
  input  logic [REG_ENTRIES-1:0][1:0][HALF_TAG_LEN-1:0] tag_vec_i,     // all the tags
  input  logic [REG_ENTRIES-1:0]                        partial_vec_i, // all the partial bits
  input  logic [REG_ENTRIES-1:0]                        valid_vec_i,   // all the valid bits
  output logic                                          full_hit_o,    // full or partial hit of the VPN trace
  output logic [REG_ENTRIES-1:0]                        hit_vec_o,     // vector of the hit lines
  output logic                                          hit_o          // global hit signal
);

  localparam LOG2_REG_ENTRIES = $clog2(REG_ENTRIES);

  logic [LOG2_REG_ENTRIES-1:0] hit_idx;

  always_comb begin
    hit_idx = '0;
    for (int k = 0; k < REG_ENTRIES; k++) begin
      if (tag_vec_i[k][1] == tag_i[1]) hit_idx = k;
    end
  end

  // comparison block for hit generation
  for (genvar k = 0; k < REG_ENTRIES; k++) begin : comparison_block
    // corresponding hit asserted if valid and match the input tag
    assign hit_vec_o[k]  = (tag_vec_i[k][1] == tag_i[1]) ? valid_vec_i[k] : 1'b0;
  end

  // full hit only if both the stored VPN are valid and match the input tag
  assign full_hit_o = (tag_vec_i[hit_idx][1:0] == tag_i[1:0] && !partial_vec_i[hit_idx]) ? hit_vec_o[hit_idx] : 1'b0;

  // OR reduction
  assign hit_o = |hit_vec_o;

endmodule
