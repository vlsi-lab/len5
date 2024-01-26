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
// File: tpc_regfile.sv
// Author: Matteo Perotti
// Date: 14/10/2019
// Description: possible implementation of the MMU cache with registers

import memory_pkg::*;

module tpc_regfile #(
    ADDR_LEN = MMUC_ENTRIES
) (
    // main
    input logic clk_i,
    input logic rst_ni,
    // replacement
    input logic wr_en_i,  // write enable
    input logic wr_part_en_i,  // write partial bit enable
    input logic [VPN_PART_LEN-1:0] tag_i,  // 9 bit PTE encoded offset
    input logic [PPN_LEN-1:0] data_i,  // 44 bit ppn
    input logic partial_i,  // if asserted -> only the first VPN is valid (this is a Mebipage)
    input logic flush_i,  // all the valid bits are zeroed
    input logic [ADDR_LEN-1:0] decoded_waddr_i,  // one-hot decoded address for write control
    input logic which_side_i,  // write either the first or the second part of both the tag and data addressed
    output logic [ADDR_LEN-1:0][1:0][VPN_PART_LEN-1:0] tag_vec_o,  // all the tags
    output logic [ADDR_LEN-1:0][1:0][PPN_LEN-1:0] data_vec_o,  // all the data
    output logic [ADDR_LEN-1:0] partial_vec_o,  // all the partial bits
    output logic [ADDR_LEN-1:0] valid_vec_o  // all the valid bits
);

  localparam LOG2_ADDR_LEN = $clog2(ADDR_LEN);

  // Write address from the decoded_waddr
  logic [LOG2_ADDR_LEN-1:0] write_idx;
  logic                     address_valid;

  always_comb begin
    write_idx = '0;
    for (int k = ADDR_LEN - 1; k >= 0; k--) begin
      if (decoded_waddr_i[k]) write_idx = k;
    end
  end
  // Priority encoder enable
  assign address_valid = |decoded_waddr_i;

  // Register file
  always_ff @(posedge clk_i or negedge rst_ni) begin : tpc_regfile
    if (!rst_ni) begin
      tag_vec_o     <= '0;
      data_vec_o    <= '0;
      partial_vec_o <= '0;
      valid_vec_o   <= '0;
    end else if (flush_i) begin
      valid_vec_o <= '0;  // flush all the entries
    end else if (wr_en_i && address_valid) begin
      tag_vec_o[write_idx][which_side_i]  <= tag_i;
      data_vec_o[write_idx][which_side_i] <= data_i;
      valid_vec_o[write_idx]              <= 1'b1;
    end else if (wr_part_en_i && address_valid) begin
      partial_vec_o[write_idx] <= partial_i;
    end
  end

endmodule
