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
// File: generic_rs.sv
// Author: Michele Caon
// Date: 21/10/2019

`ifndef SYNTHESIS
`include "len5_pkg.sv"
`include "expipe_pkg.sv"
`endif

`include "branch_unit.sv"
`include "branch_unit_rs.sv"

//import len5_pkg::XLEN;
//import len5_pkg::ILEN;
import len5_pkg::*;

import expipe_pkg::*;

module branch_rs 
#(
    RS_DEPTH = 16
)
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,
	//input   logic				stall,

    // Handshake from/to issue logic
    input   logic                   arbiter_valid_i,
    output  logic                   arbiter_ready_o,

    // Data from the decode stage
    input   branch_type_t                   branch_type_i,
    input   logic                           rs1_ready_i,
    input   logic [ROB_IDX_LEN-1:0]         rs1_idx_i,
    input   logic [XLEN-1:0]                rs1_value_i,
    input   logic                           rs2_ready_i,
    input   logic [ROB_IDX_LEN-1:0]         rs2_idx_i,
    input   logic [XLEN-1:0]                rs2_value_i,
    input   logic [B_IMM-1:0]               imm_value_i,
    input   logic [ROB_IDX_LEN-1:0]         dest_idx_i,
    input   logic [XLEN-1:0]                pred_pc_i,
    input   logic [XLEN-1:0]                pred_target_i,
    input   logic                           pred_taken_i,

	// Data to the FE 
	output  logic [XLEN-1:0]  res_pc_o,
  	output  logic [XLEN-1:0]  res_target_o,
  	output  logic             res_taken_o,
	output  logic             res_mispredict_o,

    // Hanshake from/to the CDB 
    input   logic                           cdb_ready_i,
    input   logic                           cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic                           cdb_valid_o,

    // Data from/to the CDB
    input   cdb_data_t                      cdb_data_i,
    output  cdb_data_t                      cdb_data_o
);

    // Data from/to the execution unit
    logic [XLEN-1:0]                mispredict_i; // mispredcition result
    logic [XLEN-1:0]                bu_rs1_o;
    logic [XLEN-1:0]                bu_rs2_o;
    logic [B_IMM-1:0]               bu_imm_o;
    logic [XLEN-1:0]                bu_pred_pc_o;
    logic [XLEN-1:0]                bu_pred_target_o;
    logic                           bu_pred_taken_o;
    logic [BU_CTL_LEN-1:0]          bu_branch_type_o;

    // Handshake from/to the execution unit
    logic                           bu_ready_i;
    logic                           bu_valid_i;
    logic                           bu_valid_o;
    logic                           bu_ready_o;

branch_unit_rs  #(.RS_DEPTH (RS_DEPTH)) u_branch_generic_rs
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall (stall),
    .arbiter_valid_i (arbiter_valid_i),
    .arbiter_ready_o (arbiter_ready_o),

    .branch_type_i(branch_type_i),
    .rs1_ready_i(rs1_ready_i),
    .rs1_idx_i(rs1_idx_i),
    .rs1_value_i(rs1_value_i),
    .rs2_ready_i(rs2_ready_i),
    .rs2_idx_i(rs2_idx_i),
    .rs2_value_i(rs2_value_i),
    .imm_value_i(imm_value_i),
    .dest_idx_i(dest_idx_i),
    .pred_pc_i(pred_pc_i),
    .pred_target_i(pred_target_i),
    .pred_taken_i(pred_taken_i),

    .bu_ready_i (bu_ready_i),
    .bu_valid_i (bu_valid_i),
    .bu_valid_o (bu_valid_o),
    .bu_ready_o (bu_ready_o),

    .mispredict_i(mispredict_i), 
    .bu_rs1_o(bu_rs1_o),
    .bu_rs2_o(bu_rs2_o),
    .bu_imm_o(bu_imm_o),
    .bu_pred_pc_o(bu_pred_pc_o),
    .bu_pred_target_o(bu_pred_target_o),
    .bu_pred_taken_o(bu_pred_taken_o),
    .bu_branch_type_o(bu_branch_type_o),
 
    .cdb_ready_i (cdb_ready_i),
    .cdb_valid_i (cdb_valid_i),
    .cdb_valid_o (cdb_valid_o),

    .cdb_data_i(cdb_data_i),
    .cdb_data_o(cdb_data_o)
);

branch_unit u_branch_unit
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
	.rs1_i(bu_rs1_o),
    .rs2_i(bu_rs2_o),
  	.imm_i(bu_imm_o),

  	.ops_valid_i(bu_valid_o),

  	.pred_pc_i(bu_pred_pc_o),
  	.pred_target_i(bu_pred_target_o),
  	.pred_taken_i(bu_pred_taken_o),
  	.type_i(branch_type_i),

  	.ops_ready_o(bu_ready_i),
  	.res_valid_o(bu_valid_i),
  	.res_pc_o(res_pc_o),
  	.res_target_o(res_target_o),
  	.res_taken_o(res_taken_o),
  	.res_mispredict_o(res_mispredict_o)

);

endmodule
