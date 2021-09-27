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
// File: branch_unit.sv
// Author: Marco Andorno
// Date: 05/10/2019

import len5_pkg::*;

module branch_unit
(
  input   logic             clk_i,
  input   logic             rst_n_i,
  input   logic [XLEN-1:0]  rs1_i,
  input   logic [XLEN-1:0]  rs2_i,
  input   logic [B_IMM-1:0] imm_i,
  input   logic             ops_valid_i,
  input   logic [XLEN-1:0]  pred_pc_i,
  input   logic [XLEN-1:0]  pred_target_i,
  input   logic             pred_taken_i,
  input   branch_type_t     type_i,

  output  logic             ops_ready_o,
  output  logic             res_valid_o,
  output  logic [XLEN-1:0]  res_pc_o,
  output  logic [XLEN-1:0]  res_target_o,
  output  logic             res_taken_o,
  output  logic             res_mispredict_o
);

  // Signal declarations
  logic taken, wrong_taken, wrong_target;
  logic [XLEN-1:0] target;

  // Logic unit
  always_comb begin
    case (type_i)
      BEQ:      taken = (rs1_i == rs2_i);
      BNE:      taken = (rs1_i != rs2_i);
      BLT:      taken = ($signed(rs1_i) < $signed(rs2_i));
      BGE:      taken = ($signed(rs1_i) >= $signed(rs2_i));
      BLTU:     taken = (rs1_i < rs2_i);
      BGEU:     taken = (rs1_i >= rs2_i);
      default:  taken = 0;    
    endcase
  end

  // Control unit
  branch_unit_cu u_branch_unit_cu
  (
    .clk_i            (clk_i),
    .rst_n_i          (rst_n_i),
    .ops_valid_i      (ops_valid_i),
    .taken_i          (taken),
    .wrong_taken_i    (wrong_taken),
    .wrong_target_i   (wrong_target),

    .ops_ready_o      (ops_ready_o),
    .res_valid_o      (res_valid_o),
    .res_taken_o      (res_taken_o),
    .res_mispredict_o (res_mispredict_o)
  );

  // Assignments
  assign wrong_taken = pred_taken_i != taken;
  assign target = { {XLEN-B_IMM{1'b0}}, (imm_i << 1)} + pred_pc_i; // add JAL and JALR; add a mux with jump
  assign wrong_target = pred_target_i != target;
	// Add a check for missaligned address
  // Output register
  always_ff @ (posedge clk_i or negedge rst_n_i) begin: out_reg
    if (!rst_n_i) begin
      res_pc_o <= '0;
      res_target_o <= '0;
    end else if (ops_valid_i) begin
      res_pc_o <= pred_pc_i;
      res_target_o <= target;
    end
  end: out_reg
  
endmodule
