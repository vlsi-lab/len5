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
// File: pte_checker.sv
// Author: Matteo Perotti
// Date: 14/10/2019
// Description: Page Table Entry checker for exception_os or leaf page

import memory_pkg::*;

module pte_checker
(
  input  pte_level_e pte_level_i,  // page table level at which the checked PTE exists. "ROOT" means that this is not a PTE, but the root address of the page table
  input ppn_t       ppn_i,        // the ppn. If it is not a leaf page, it should be alignet to its natural boundary
  input pte_ctrl_t  pte_ctrl_i,   // control bits to detect exception_os and understand the meaning of the PPN of the PTE
  input  logic       chk_en_i,     // there is something to check
  output exception_e exception_o,  // the actual exception_o. A value of 0 means "no exception_os".
  output logic       done_o        // asserted if the PTW should be stopped, either for an exception_o or for the correct PPN
);

  always_comb begin
    // default values
    exception_o = NoException;
    done_o      = 1'b1;           // default action: stop PTW and give the result to the L2-TLB
    // if there is something to check
    if (chk_en_i) begin
      // if data stored in the register is a PTE
      if (pte_level_i != Root) begin
        if (!pte_ctrl_i.v || (!pte_ctrl_i.r && pte_ctrl_i.w)) exception_o = PageFault;
        else begin
          // if leaf PTE
          if (pte_ctrl_i.r || pte_ctrl_i.x) begin
            // page fault exception due to the access bit cleared
            if (!pte_ctrl_i.a) exception_o = PageFault;
            // misaligned page exception check for GibiPage
            else if (pte_level_i == L3) begin
              if ({ppn_i.p1, ppn_i.p0} != '0) exception_o = PageFault;
            // misaligned page exception check for MebiPage
            end else if (pte_level_i == L2) begin
              if (ppn_i.p0 != '0) exception_o = PageFault;
            end
          // if non-leaf PTE, it should point to the next level of the Page Table
          end else if (!pte_ctrl_i.r && !pte_ctrl_i.x) begin
            // can't be a pointer
            if (pte_level_i == L1) exception_o = PageFault;
            // it is actually a pointer
            else done_o = 1'b0;
          end
        end
      // data in register is the Page Table root address (not a PTE)
      end else done_o = 1'b0;
    // nothing to check
    end else done_o = 1'b0;
  end

endmodule
