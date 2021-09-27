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
// File: d1_dirty_vec_one_hotter.sv
// Author: Matteo Perotti
// Date: 28/10/2019
// Description: auxiliary d1 block to manipulate the dirty vector and control the L2 update counter

import memory_pkg::*;

module d1_dirty_vec_one_hotter
(
  // WBB is being written in this cycle
  input  logic       l2_update_is_writing_wbb_i,
  // Input multi hot dirty vector
  input  dirty_vec_t mh_dirty_vec_i,
  // Output one hotted dirty vector
  output dirty_vec_t oh_dirty_vec_o,
  // At least one dirty?
  output logic       at_least_one_dirty_o,
  // Enable the counter of the L2 Updating block (i.e. proceed with the next set)
  output logic       l2_update_cnt_en_o
);

  // support variable
  int one_found;

  dirty_vec_t oh_dirty_vec, mh_oh_dirty_vec_xnored;
  logic       mh_oh_equal;
  logic       is_clean;

  assign mh_oh_dirty_vec_xnored = mh_dirty_vec_i ^~ oh_dirty_vec;
  assign mh_oh_equal            = &mh_oh_dirty_vec_xnored;
  assign is_clean               = &(~mh_dirty_vec_i);

  // to be optimized
  always_comb begin
    oh_dirty_vec = '0;
    one_found = 0;
    for (int k = 0; k < DCACHE_L1_ASSOCIATIVITY; k++) begin
      if (mh_dirty_vec_i[k] && !one_found) begin
        oh_dirty_vec[k] = 1'b1;
        one_found       = 1;
      end
    end
  end

  // If the set is not clean there is at least one dirty
  assign at_least_one_dirty_o = ~is_clean;

  // Update if the vector is clean or if the last dirty is being written to the WBB
  assign l2_update_cnt_en_o   = ((mh_oh_equal && l2_update_is_writing_wbb_i) || is_clean ) ? 1'b1 : 1'b0;

  // Interface assignment
  assign oh_dirty_vec_o       = oh_dirty_vec;

endmodule
