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
// File: d1_wbb_mshr_ctrl_L2_side.sv
// Author: Matteo Perotti
// Date: 28/10/2019
// Description: control the MSHR and the WBB for what concerns the L2 side
// Details: it can put in a waiting state the entries and write the tag into the WBB.
//          This block, in this configuration, should be implemented with wires

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/memory_pkg.sv"
import memory_pkg::*;

module d1_wbb_mshr_ctrl_L2_side
(
  // Any transaction ok with L2?
  input  logic mshr_transaction_ok_i,
  input  logic wbb_transaction_ok_i,
  // MSHR and buffer control
  output logic mshr_put_wait_read_line_o,
  output logic wbb_put_wait_tag_read_line_o
);

  assign mshr_put_wait_read_line_o    = (mshr_transaction_ok_i) ? 1'b1 : 1'b0;
  assign wbb_put_wait_tag_read_line_o = (wbb_transaction_ok_i)  ? 1'b1 : 1'b0;

endmodule
