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
 * @brief Return address stack
 *
 * @details This module stores the return address (PC+4) of the last jump-and-
 *          link instructions. When a 'ret' instruction is detected, the latest
 *          return address is fetched and used as the next value for the PC.
 */
module ras #(
  parameter int unsigned DEPTH = 4  // number of recent return addresses to buffer
) (
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i,

  // LIFO control
  input  logic                      push_i,      // push a new return address
  input  logic                      pop_i,       // pop the last return address
  input  logic                      confirm_i,   // confirm a resolved call
  input  logic [len5_pkg::ALEN-1:0] ret_addr_i,  // new return address
  output logic                      valid_o,     // return address valid
  output logic [len5_pkg::ALEN-1:0] ret_addr_o   // last return address
);

  import len5_pkg::*;
  localparam int unsigned IdxW = $clog2(DEPTH);

  // INTERNAL SIGNALS
  // ----------------
  // Return addresses
  logic [DEPTH-1:0][ ALEN-1:0] ras_addr;
  logic [DEPTH-1:0]            ras_valid;
  logic [DEPTH-1:0]            ras_confirmed;

  // RAS pointers
  logic [IdxW-1:0] last_idx, new_idx, confirmed_idx, spec_idx;
  logic last_valid;
  logic ras_full;
  logic all_confirmed;

  // --------------------------
  // RETURN ADDRESS LIFO BUFFER
  // --------------------------
  // LIFO address update
  always_ff @(posedge clk_i or negedge rst_ni) begin : lifo_upd
    if (!rst_ni) begin
      ras_valid <= '0;
    end else if (flush_i) begin
      ras_valid <= ras_confirmed;
    end else begin
      if (push_i && pop_i) begin
        ras_addr[last_idx] <= ret_addr_i;
      end else if (push_i && !ras_full) begin
        ras_addr[new_idx]  <= ret_addr_i;
        ras_valid[new_idx] <= 1'b1;
      end else if (pop_i) begin
        ras_valid[last_idx] <= 1'b0;
      end
    end
  end

  // LIFO speculation update
  assign all_confirmed = ras_valid == ras_confirmed;
  always_ff @(posedge clk_i or negedge rst_ni) begin : lifo_spec
    if (!rst_ni) begin
      ras_confirmed <= '0;
    end else begin
      if (all_confirmed && pop_i) begin
        ras_confirmed[confirmed_idx] <= 1'b0;
      end else if (confirm_i) begin
        ras_confirmed[spec_idx] <= 1'b1;
      end
    end
  end

  // Full
  assign ras_full = &ras_valid;

  // RAS indexes
  // -----------
  // Last valid entry
  prio_enc #(
    .N(DEPTH)
  ) prio_enc_last (
    .lines_i(ras_valid),
    .enc_o  (last_idx),
    .valid_o(last_valid)
  );

  // First free entry
  prio_enc #(
    .N  (DEPTH),
    .INV(1'b1)
  ) prio_enc_new (
    .lines_i(~ras_valid),
    .enc_o  (new_idx),
    .valid_o()             // not used
  );

  // Latest confirmed entry
  prio_enc #(
    .N(DEPTH)
  ) prio_enc_confirmed (
    .lines_i(ras_confirmed),
    .enc_o  (confirmed_idx),
    .valid_o()                // not used
  );

  // Latest confirmed entry
  prio_enc #(
    .N  (DEPTH),
    .INV(1'b1)
  ) prio_enc_spec (
    .lines_i(~ras_confirmed),
    .enc_o  (spec_idx),
    .valid_o()                 // not used
  );

  // -----------------
  // OUTPUT GENERATION
  // -----------------
  assign valid_o    = last_valid;
  assign ret_addr_o = ras_addr[last_idx];
endmodule
