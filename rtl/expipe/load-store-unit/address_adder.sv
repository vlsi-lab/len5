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
// File: address_adder.sv
// Author: Michele Caon
// Date: 15/07/2022

import len5_config_pkg::*;
import len5_pkg::*;
import expipe_pkg::*;

/**
 * @brief Address adder.
 *
 * @details Adder to compute the target memory address starting from a base
 *          address (rs1) and an offset (immediate value). Not suitable for
 *          virtual memory.
 */
module address_adder (
  input logic clk_i,
  input logic rst_n_i,
  input logic flush_i,

  /* Load/store buffer */
  input  logic valid_i,
  input  logic ready_i,
  output logic valid_o,
  output logic ready_o,

  input  adder_req_t req_i,
  output adder_ans_t ans_o
);
  // INTERNAL SIGNALS
  // ----------------
  logic       [XLEN-1:0] res;
  logic                  align_except;
  adder_ans_t            ans;

  // Exception handler
  // -----------------
  always_comb begin : vaddr_exception
    // Check if the address is naturally aligned according to the type of load/store. If not, an ADDRESS MISALIGNED exception must be raised.
    case (req_i.ls_type)
      LS_HALFWORD, LS_HALFWORD_U: align_except = (ans.result[0]) ? (1'b1) : (1'b0);
      LS_WORD, LS_WORD_U:         align_except = (ans.result[1:0] != 2'b00) ? (1'b1) : (1'b0);
      LS_DOUBLEWORD:              align_except = (ans.result[2:0] != 3'b000) ? (1'b1) : (1'b0);
      default:                    align_except = 1'b0;
    endcase
  end

  // Address adder
  // -------------
  assign ans.tag           = req_i.tag;
  assign ans.is_store      = req_i.is_store;
  assign ans.result        = req_i.base + req_i.offs;
  assign ans.except_raised = align_except;
  assign ans.except_code   = (req_i.is_store) ? E_ST_ADDR_MISALIGNED : E_LD_ADDR_MISALIGNED;

  // Output spill cell
  // -----------------
  spill_cell #(
    .DATA_T(adder_ans_t),
    .SKIP  (LSU_SPILL_SKIP)
  ) u_out_reg (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .valid_i(valid_i),
    .ready_i(ready_i),
    .valid_o(valid_o),
    .ready_o(ready_o),
    .data_i (ans),
    .data_o (ans_o)
  );

endmodule
