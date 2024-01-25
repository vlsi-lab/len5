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
// File: icache_comparison_block.sv
// Author: Matteo Perotti
// Date: 29/10/2019
// Description: compare the tag to the output of the cache and generate the valid bits


//import len5_pkg::*;
import memory_pkg::*;

module icache_comparison_block (
    // The output of the cache
    input  icache_mem_out_t mem_out_i,
    // Incoming tag to be compared
    input  icache_L1_tag_t  tag_i,
    // Cache hit
    output logic            hit_o,
    // Output selected line
    output icache_line_t    line_o
);

  localparam N_WAY = ICACHE_L1_ASSOCIATIVITY;
  localparam LOG2_N_WAY = $clog2(N_WAY);

  icache_hit_vec_t                  hit_vec;
  logic            [LOG2_N_WAY-1:0] encoded_hit_vec;

  // Hit vector creation
  always_comb begin
    hit_vec = '0;
    for (int k = 0; k < ICACHE_L1_ASSOCIATIVITY; k++) begin
      hit_vec[k] = (mem_out_i.tag_vec[k] == tag_i) ? mem_out_i.valid_vec[k] : 1'b0;
    end
  end
  assign hit_o = |hit_vec;

  // Line selection multiplexer
  always_comb begin
    encoded_hit_vec = '0;
    for (int k = 0; k < ICACHE_L1_ASSOCIATIVITY; k++) begin
      if (hit_vec[k]) encoded_hit_vec = k;
    end
  end
  assign line_o = mem_out_i.data_vec[encoded_hit_vec];

endmodule
