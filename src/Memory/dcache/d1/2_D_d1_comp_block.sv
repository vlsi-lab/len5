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
// File: d1_comp_block.sv
// Author: Matteo Perotti
// Date: 14/10/2019
// Description: dcache comparison block

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/memory_pkg.sv"
import memory_pkg::*;

module d1_comp_block
#(
  N_WAY = DCACHE_L1_ASSOCIATIVITY
)
(
  // From d0 output registers
  input  dcache_tag_t            tag_i,       // input tag for comparison
  // From the cache memory
  input dcache_tag_t [N_WAY-1:0] tag_vec_i,   // tag vector
  input valid_vec_t              valid_vec_i, // valid vector
  input dirty_vec_t              dirty_vec_i, // dirty vector
  // From the replace block
  input  repl_vec_t              replace_vec, // one-hot '1' on the line to be replaced
  // Hit vec to drive the doubleword selection
  output hit_vec_t               hit_vec_o,   // vector of the hit lines
  // Hit and Dirty signals
  output logic                   hit_o,       // global hit signal
  output logic                   dirty_o      // is line to be replaced dirty?
);

  // Each dirty bit masked with the corresponding bit in replace_vec
  logic [N_WAY-1:0] masked_dirty_vec;

  // Comparison block for hit generation
  for (genvar k = 0; k < N_WAY; k++) begin : comparison_block
    assign hit_vec_o[k] = (tag_vec_i[k] == tag_i) ? valid_vec_i[k] : 1'b0;
  end

  // Dirty bit selection
  for (genvar k = 0; k < N_WAY; k++) begin : dirty_sel_block
    assign masked_dirty_vec[k] = dirty_vec_i[k] & replace_vec[k];
  end
  // OR reduction to determine if the line to be replaced is dirty
  assign dirty_o =| masked_dirty_vec;

  // OR reduction for global HIT
  assign hit_o =| hit_vec_o;

endmodule
