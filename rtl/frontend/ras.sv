// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: ras.sv
// Author: Michele Caon
// Date: 11/10/2022

/**
 * @brief	Return address stack
 *
 * @details	This module stores the return address (PC+4) of the last jump-and-
 *          link instructions. When a 'ret' instruction is detected, the latest
 *          return address is fetched and used as the next value for the PC.
 */

import len5_pkg::*;

module ras #(
    parameter RAS_DEPTH = 4  // number of recent return addresses to buffer
) (
    input logic clk_i,
    input logic rst_n_i,

    // From the branch unit
    input  logic            push_i,
    input  logic            pop_i,
    input  logic [XLEN-1:0] ret_addr_i,
    output logic [XLEN-1:0] ret_addr_o
);
  localparam IDX_W = $clog2(RAS_DEPTH);

  // INTERNAL SIGNALS
  // ----------------

  // Return addresses
  logic            ras_push;
  logic [XLEN-1:0] ras      [RAS_DEPTH];

  // New and last entry indexes
  logic new_cnt_en, new_cnt_up;
  logic [IDX_W-1:0] new_idx, last_idx;

  // --------------------------
  // RETURN ADDRESS LIFO BUFFER
  // --------------------------
  assign ras_push = push_i;
  always_ff @(posedge clk_i or negedge rst_n_i) begin : lifo_upd
    if (rst_n_i) foreach (ras[i]) ras[i] <= '0;
    else if (ras_push) ras[new_idx] <= ret_addr_i;
  end

  // New index counter
  // -----------------
  assign new_cnt_en = push_i ^ pop_i;
  assign new_cnt_up = push_i;
  updown_counter #(
      .W(IDX_W)
  ) u_new_cnt (
      .clk_i  (clk_i),
      .rst_n_i(rst_n_i),
      .en_i   (new_cnt_en),
      .clr_i  (1'b0),
      .up_dn_i(new_cnt_up),
      .count_o(new_idx),
      .tc_o   ()             // unused
  );
  assign last_idx   = new_idx - 1;

  // -----------------
  // OUTPUT GENERATION
  // -----------------
  assign ret_addr_o = ras[last_idx];

endmodule
