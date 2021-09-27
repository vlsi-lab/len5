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
// File: mmuc_update_ctrl.sv
// Author: Matteo Perotti
// Date: 14/10/2019
// Description: controller to update the translation path cache

import memory_pkg::*;

module mmuc_update_ctrl
(
  input  pte_level_e pte_level_i,           // PT level at which the checked PTE exists (ROOT is not a PTE)
  input  logic       mmuc_update_cond_en_i, // an MMUC write is allowed to happen
  input  logic       ptw_done_i,            // PTW stopped for leaf page or exception
  output logic       wr_en_o,               // MMUC write enable
  output logic       which_side_o,          // first or second part of the trace
  output logic       wr_partial_o,          // write "partial_o" into its field in the MMUC
  output logic       partial_o              // only the first part of the trace in the MMUC is valid
);

  // Combinatorial process
  always_comb begin
    // default assignment
    wr_en_o      = 1'b0;
    which_side_o = 1'b0;
    wr_partial_o = 1'b0;
    partial_o    = 1'b0;
    // if it is possible to update the MMUC
    if (mmuc_update_cond_en_i) begin
      if (pte_level_i == L3) begin
        // not a Gibipage
        if (!ptw_done_i) begin
          wr_en_o      = 1'b1;
          which_side_o = 1'b1;
        end
      end else if (pte_level_i == L2) begin
        // not a Mebipage
        if (!ptw_done_i) begin
          wr_en_o = 1'b1;
        // Mebipage
        end else if (ptw_done_i) begin
          wr_partial_o = 1'b1;
          partial_o    = 1'b1;
        end
      end
    end
  end

endmodule
