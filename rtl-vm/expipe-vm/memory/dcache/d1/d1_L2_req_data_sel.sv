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
// File: d1_L2_req_data_sel.sv
// Author: Matteo Perotti
// Date: 28/10/2019
// Description: block to route the correct lines MSHR/WBB to L2

import memory_pkg::*;

module d1_L2_req_data_sel (
    // The winner block
    input mshr_wbb_winner_e winner_i,
    // From WBB
    input dcache_line_t wbb_l2c_line_i,
    input line_addr_t wbb_l2c_line_addr_i,
    // From the tag counter
    input wbb_tag_t wbb_tag_i,  // the tag is valid when the transaction is done
    // From MSHR
    input line_addr_t mshr_l2c_line_addr_i,
    // To L2C
    output line_addr_t l1dc_l2c_req_line_addr_o,
    output dcache_line_t l1dc_l2c_req_line_o,
    output wbb_tag_t l1dc_l2c_req_wbb_tag_o,
    output logic l1dc_l2c_req_is_store_o
);

  assign l1dc_l2c_req_line_addr_o = (winner_i == MSHR) ? mshr_l2c_line_addr_i : wbb_l2c_line_addr_i;
  assign l1dc_l2c_req_line_o = wbb_l2c_line_i;
  assign l1dc_l2c_req_wbb_tag_o = wbb_tag_i;
  assign l1dc_l2c_req_is_store_o = (winner_i == MSHR) ? 1'b0 : 1'b1;

endmodule
