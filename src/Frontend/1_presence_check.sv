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
// File: presence_check.sv
// Author: Marco Andorno
// Date: 03/10/2019

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/len5_pkg.sv"
import len5_pkg::*;

module presence_check
(
  input   logic [XLEN-1:0]  pc_i,
  input   logic [XLEN-1:0]  prev_pc_i,
  input   logic [XLEN-1:0]  line_pc_i,
  input   logic             line_valid_i,

  output  logic             here_o,
  output  logic             will_be_here_o
);

  assign here_o = (pc_i[XLEN-1:ICACHE_OFFSET+OFFSET] ==
                    line_pc_i[XLEN-1:ICACHE_OFFSET+OFFSET]) & line_valid_i;
  assign will_be_here_o = (pc_i[XLEN-1:ICACHE_OFFSET+OFFSET] ==
                    prev_pc_i[XLEN-1:ICACHE_OFFSET+OFFSET]) & (!here_o);

endmodule
