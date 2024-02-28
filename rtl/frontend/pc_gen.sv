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
// File: pc_gen.sv
// Author: Marco Andorno
// Date: 03/10/2019


module pc_gen #(
  parameter logic [len5_pkg::XLEN-1:0] BOOT_PC = 64'h0
) (
  input  logic                                        clk_i,
  input  logic                                        rst_ni,
  input  logic                                        comm_except_raised_i,
  input  logic                   [len5_pkg::XLEN-1:0] comm_except_pc_i,
  input  logic                                        bu_res_valid_i,
  input  fetch_pkg::resolution_t                      bu_res_i,
  input  logic                   [len5_pkg::XLEN-1:0] pred_target_i,
  input  logic                   [len5_pkg::XLEN-1:0] early_jump_target_i,
  input  logic                                        early_jump_valid_i,
  input  logic                                        pred_taken_i,
  input  logic                                        mem_ready_i,
  output logic                                        valid_o,
  output logic                                        bu_ready_o,
  output logic                   [len5_pkg::XLEN-1:0] pc_o,
  output logic                   [len5_pkg::XLEN-1:0] early_jump_target_prediction_o
);

  import len5_pkg::*;
  import fetch_pkg::*;
  // INTERNAL SIGNALS
  // ----------------
  logic [len5_pkg::XLEN-1:0] next_pc, add_pc, adder_out, pc_offset;

  // -------------------
  // PC GENERATION LOGIC
  // -------------------

  // Mux + adder
  assign pc_offset = (early_jump_valid_i && !(bu_res_valid_i && bu_res_i.mispredict)) ? early_jump_target_i : {32'b0, (ILEN >> 3)}; 
  assign add_pc    = (bu_res_valid_i && bu_res_i.mispredict) ? bu_res_i.pc : pc_o;
  assign adder_out = add_pc + pc_offset;

  // Priority list for choosing the next PC value:
  // 1) Exception
  // 2) Misprediction
  // 3) Branch prediction
  // 4) Default PC+jump immediate
  // 5) Default PC+4
  always_comb begin : pc_priority_enc
    if (comm_except_raised_i) begin
      next_pc = comm_except_pc_i;
    end else if (bu_res_valid_i && bu_res_i.mispredict) begin
      if (bu_res_i.taken) begin
        next_pc = bu_res_i.target;
      end else begin
        next_pc = adder_out;
      end
    end else if (pred_taken_i) begin
      next_pc = pred_target_i;
    end else begin
      next_pc = adder_out;
    end
  end : pc_priority_enc

  // PC register
  always_ff @(posedge clk_i or negedge rst_ni) begin : pc_reg
    if (!rst_ni) begin
      pc_o <= BOOT_PC;
    end else if (mem_ready_i) begin
      pc_o <= next_pc;
    end
  end : pc_reg

  // Output valid and ready
  assign valid_o    = rst_ni & !(bu_res_valid_i & bu_res_i.mispredict) & !comm_except_raised_i;
  assign bu_ready_o = mem_ready_i;
  assign early_jump_target_prediction_o = next_pc;
endmodule
