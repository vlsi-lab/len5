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
// File: d1_d0_data_sel.sv
// Author: Matteo Perotti
// Date: 28/10/2019
// Description: block to route the correct lines from d1 to d0

import memory_pkg::*;
import len5_pkg::*;
import expipe_pkg::BUFF_IDX_LEN;

module d1_d0_data_sel (
    // Actual d1 request (to decide if WBB or Out Regs line forwarding)
    input d0_d1_req_type_e d1_req_type_i,
    // The request type and the information from the CU route the data
    input d1_d0_req_type_e d1_d0_req_type_i,  // d1 -> d0 request type
    input logic d1_d0_req_valid_i,  // valid for the d1 -> d0 request type
    input logic replaying_i,  // is d1 performing an instruction replay now?
    // Data from d0 output registers
    input dcache_L1_addr_t d0_reg_out_paddr_i,  // the physical cache address
    input logic [len5_pkg::XLEN-1:0] d0_reg_out_data_i,  // data to be stored
    input dcache_line_t d0_reg_out_line_i,  // forwarded line
    input logic [BUFF_IDX_LEN-1:0] d0_reg_out_lsq_addr_i,  // to address the answer to LSQ
    input store_width_e d0_reg_out_store_width_i,  // DW, W, HW, B
    // Dirty data from the memory (useful during an L2 Updating)
    input line_addr_t dirty_line_addr_i,  // paddr for d0 line cleaning during an L2 updating
    // Data from the comparison block
    input hit_vec_t hit_vec_i,  // hit lines from the comparison block in d1
    input dirty_vec_t dirty_vec_i,  // one hotted dirty vector from d1
    // Data from the Replace Block
    input repl_vec_t replace_vec_i,  // updateL2 replace idx
    // Data from the WBB
    input dcache_line_t wbb_d1_line_i,  // line from the WBB
    // Data from the replay registers
    input d1_d0_req_type_e replay_reg_type_i,  // d1 -> d0 request type
    input dcache_L1_addr_t replay_reg_paddr_i,  // the physical cache address
    input logic [len5_pkg::XLEN-1:0] replay_reg_doubleword_i,  // data to be stored
    input logic [BUFF_IDX_LEN-1:0] replay_reg_lsq_addr_i,  // to address the answer to LSQ
    input store_width_e replay_reg_store_width_i,  // DW, W, HW, B
    // d1 -> d0 data
    output d1_d0_req_t d1_d0_req_o  // d1 -> d0 data
);

  // Address length for the byte offset of a line
  localparam LINE_BYTE_OFF_A_LEN = DCACHE_L1_LINE_OFF_A_LEN + DCACHE_L1_WORD_A_LEN;
  // Filler for the dirty line address, to create a full paddr
  logic [LINE_BYTE_OFF_A_LEN-1:0] zero_line_off_filler;

  assign zero_line_off_filler = '0;

  assign d1_d0_req_o.req_type = (replaying_i) ? replay_reg_type_i : d1_d0_req_type_i;
  always_comb begin
    if (d1_req_type_i == d0_d1_UpdateL2) d1_d0_req_o.paddr = {dirty_line_addr_i, zero_line_off_filler};
    else if (replaying_i) d1_d0_req_o.paddr = replay_reg_paddr_i;
    else d1_d0_req_o.paddr = d0_reg_out_paddr_i;
  end
  assign d1_d0_req_o.line = (d1_req_type_i == d0_d1_ReplaceReq) ? d0_reg_out_line_i : wbb_d1_line_i;
  assign d1_d0_req_o.data = (replaying_i) ? replay_reg_doubleword_i : d0_reg_out_data_i;
  assign d1_d0_req_o.lsq_addr = (replaying_i) ? replay_reg_lsq_addr_i : d0_reg_out_lsq_addr_i;
  assign d1_d0_req_o.store_width = (replaying_i) ? replay_reg_store_width_i : d0_reg_out_store_width_i;
  ;
  assign d1_d0_req_o.hit_vec     = hit_vec_i;
  assign d1_d0_req_o.dirty_vec   = dirty_vec_i;
  assign d1_d0_req_o.replace_vec = replace_vec_i;
  assign d1_d0_req_o.valid       = d1_d0_req_valid_i;

endmodule
