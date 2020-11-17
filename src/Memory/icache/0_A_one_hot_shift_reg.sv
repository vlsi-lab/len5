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
// File: one_hot_shift_reg.sv
// Author: Matteo Perotti
// Date: 22/10/2019
// Description: one hot shift register reset to "10...0". One bit among the others is always '1'.

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/memory_pkg.sv"
import memory_pkg::*;

module one_hot_shift_reg
#(
  REG_LEN = 2
)
(
  input logic                clk_i,
  input logic                rst_ni,
  input logic                update_i,
  output logic [REG_LEN-1:0] output_o
);

  logic [REG_LEN-1:0] reg_d, reg_q;

  always_comb begin
    for (int k = 1; k < REG_LEN; k++) begin : shift_register
      reg_d[k-1] = reg_q[k];
    end
      reg_d[REG_LEN-1] = reg_q[0];
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      reg_q[REG_LEN-1]   <= 1'b1;
      reg_q[REG_LEN-2:0] <= '0;
    end else if (update_i) begin
      reg_q              <= reg_d;
    end
  end

  assign output_o = reg_q;

endmodule
