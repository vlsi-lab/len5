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
// File: d1_wbb_tag_gen.sv
// Author: Matteo Perotti
// Date: 28/10/2019
// Description: generate the tag for the WB Victim Buffer
// Details: automatic wrapping of the cnt

import memory_pkg::*;

module d1_wbb_tag_gen (
    // Main
    input  logic     clk_i,
    input  logic     rst_ni,
    // A valid transaction between WBB and L2 is happening right now
    input  logic     wbb_valid_transaction_i,
    // The tag to be written into the entry of the transaction
    output wbb_tag_t wbb_tag_o
);

  wbb_tag_t cnt;
  logic     cnt_en;

  assign wbb_tag_o = cnt;
  assign cnt_en    = wbb_valid_transaction_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
    end else if (cnt_en) begin
      cnt <= cnt + 1;
    end
  end

endmodule
