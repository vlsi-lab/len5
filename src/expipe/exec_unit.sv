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
// File: issue_IQL.sv
// Author: WALID WALID
// Date: 17/10/2020


import len5_pkg::*;
import expipe_pkg::*;
import csr_pkg::*;
import memory_pkg::*;

module exec_unit (
    input   logic               clk_i,
    input   logic               rst_n_i,
    input   logic               flush_i,
	//input logic stall,
	input   satp_mode_t         vm_mode_i,

    // Handshake from/to Back end
    input   logic [0:EU_N-1]    ex_ready_i,             // valid signal from each reservation station
    output  logic [0:EU_N-1]    ex_valid_o,             // ready signal to each reservation station

    // Data oto the Back end
    input   logic [8-1:0]  ex_eu_ctl_i,    // controls for the associated EU
    input   logic                       ex_rs1_ready_i, // first operand is ready at issue time (from the RF or the ROB)
    input   logic [ROB_IDX_LEN-1:0]     ex_rs1_idx_i,   // the index of the ROB where the first operand can be found (if not ready
    input   logic [XLEN-1:0]            ex_rs1_value_i, // the value of the first operand (if ready)
    input   logic                       ex_rs2_ready_i, // second operand is ready at issue time (from the RF or the ROB)
    input   logic [ROB_IDX_LEN-1:0]     ex_rs2_idx_i,   // the index of the ROB where the first operand can be found (if not ready)
    input   logic [XLEN-1:0]            ex_rs2_value_i, // the value of the first operand (if ready)
   
 	input   logic [I_IMM-1:0]           ex_imm_value_i, // the value of the immediate field (for st and branches)                   

    input   logic [ROB_IDX_LEN-1:0]     ex_rob_idx_i,   // the location of the ROB assigned to the instruction
    input   logic [XLEN-1:0]            ex_pred_pc_i,   // the PC of the current issuing instr (branches only)
    input   logic [XLEN-1:0]            ex_pred_target_i,// the predicted target of the current issuing instr (branches only)
    input   logic                       ex_pred_taken_i,// the predicted taken bit of the current issuing instr (branches only)
	input   branch_type_t               branch_type_i,
	input   ldst_type_t             	ldst_type_i,

	// Data to the FE 
	output  logic [XLEN-1:0]  res_pc_o,
  	output  logic [XLEN-1:0]  res_target_o,
  	output  logic             res_taken_o,
	output 	logic 			  res_mispredict_o,

	// Handshake and data from/to the TLB
    input   var dtlb_lsq_ans_t          dtlb_ans_i,
    input   var dtlb_lsq_wup_t          dtlb_wup_i,
    input   logic                       dtlb_ready_i,
    output  lsq_dtlb_req_t          dtlb_req_o,

    // Handshake and data from/to the D$
    input   var l1dc_lsq_ans_t          dcache_ans_i,
    input   var l1dc_lsq_wup_t          dcache_wup_i,
    input   logic                       dcache_ready_i,
    output  lsq_l1dc_req_t          dcache_req_o,

    // Hanshake from/to the CDB 
    input   logic  [0:EU_N-1]                 cdb_ready_i,
    input   logic                   cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic  [0:EU_N-1]                 cdb_valid_o,

    // Data from/to the CDB
  //typedef struct packed {
    //    logic [ROB_IDX_LEN-1:0]     rob_idx;
    //    logic [XLEN-1:0]            value;
    //    logic                       except_raised;
    //    logic [ROB_EXCEPT_LEN-1:0]  except_code;
    //} cdb_data_t;
    input 	var cdb_data_t   cdb_data_i [0:EU_N-1],
	output 	cdb_data_t   cdb_data_o [0:EU_N-1],
    //input   logic [ROB_IDX_LEN-1:0] cdb_idx_i,
    //input   logic [XLEN-1:0]        cdb_data_i,
    //input   logic                   cdb_except_raised_i,
    //output  logic [ROB_IDX_LEN-1:0] cdb_idx_o,
    //output  logic [XLEN-1:0]        cdb_data_o,
    //output  logic                   cdb_except_raised_o,
    //output  logic [ROB_EXCEPT_LEN-1:0] cdb_except_o,

	// Control from/to the ROB
    input   logic [ROB_IDX_LEN-1:0] rob_head_idx_i,
    output  logic                   rob_store_committing_o

    // Hanshake from/to the CDB 
    //input   logic                   cdb_lb_valid_i,
    //input   logic                   cdb_sb_valid_i,
    //input   logic                   cdb_lb_ready_i,
    //input   logic                   cdb_sb_ready_i,
    //output  logic                   lb_cdb_valid_o,
    //output  logic                   sb_cdb_valid_o,

    // Data from/to the CDB
    //input   cdb_data_t              cdb_lsb_data_i,
    //output  cdb_data_t              lb_cdb_data_o,
    //output  cdb_data_t              sb_cdb_data_o
);

    // DEFINITIONS
localparam EU_CTL_LEN = 8;//4;//8;
localparam RS_DEPTH = 8;
localparam EXCEPT_LEN = 2;

 //---------------\\
//----- DUT -----\\
//---------------\\

alu_rs #(.EU_CTL_LEN (8/*4//8*/), .RS_DEPTH (8), .EXCEPT_LEN(2)) u_alu_rs
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),
    .arbiter_valid_i (ex_ready_i[EU_INT_ALU]),
    .arbiter_ready_o (ex_valid_o[EU_INT_ALU]),
	.eu_ctl_i (ex_eu_ctl_i),
    .rs1_ready_i (ex_rs1_ready_i),
    .rs1_idx_i (ex_rs1_idx_i),
    .rs1_value_i (ex_rs1_value_i),
    .rs2_ready_i (ex_rs2_ready_i),
    .rs2_idx_i (ex_rs2_idx_i),
    .rs2_value_i (ex_rs2_value_i),
    .dest_idx_i (ex_rob_idx_i),
	.cdb_ready_i (cdb_ready_i[EU_INT_ALU]),
    .cdb_valid_i (cdb_valid_i),
    .cdb_valid_o (cdb_valid_o[EU_INT_ALU]),
    .cdb_idx_i (cdb_data_i[EU_INT_ALU].rob_idx),//(cdb_idx_i),
    .cdb_data_i (cdb_data_i[EU_INT_ALU].value),//(cdb_data_i),
    .cdb_except_raised_i (cdb_data_i[EU_INT_ALU].except_raised),//(cdb_except_raised_i),
    .cdb_idx_o (cdb_data_o[EU_INT_ALU].rob_idx),//(cdb_idx_o),
    .cdb_data_o (cdb_data_o[EU_INT_ALU].value),//(cdb_data_o),
    .cdb_except_raised_o (cdb_data_o[EU_INT_ALU].except_raised),//(cdb_except_raised_o),
    .cdb_except_o (cdb_data_o[EU_INT_ALU].except_code)//(cdb_except_o)
);

mult_rs #(.EU_CTL_LEN (EU_CTL_LEN), .RS_DEPTH (RS_DEPTH), .EXCEPT_LEN(2)) u_mult_rs
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),
    .arbiter_valid_i (ex_ready_i[EU_INT_MULT]),
    .arbiter_ready_o (ex_valid_o[EU_INT_MULT]),
	.eu_ctl_i (ex_eu_ctl_i),
    .rs1_ready_i (ex_rs1_ready_i),
    .rs1_idx_i (ex_rs1_idx_i),
    .rs1_value_i (ex_rs1_value_i),
    .rs2_ready_i (ex_rs2_ready_i),
    .rs2_idx_i (ex_rs2_idx_i),
    .rs2_value_i (ex_rs2_value_i),
    .dest_idx_i (ex_rob_idx_i),
	.cdb_ready_i (cdb_ready_i[EU_INT_MULT]),
    .cdb_valid_i (cdb_valid_i),
    .cdb_valid_o (cdb_valid_o[EU_INT_MULT]),
	.cdb_idx_i (cdb_data_i[EU_INT_MULT].rob_idx),//(cdb_idx_i),
    .cdb_data_i (cdb_data_i[EU_INT_MULT].value),//(cdb_data_i),
    .cdb_except_raised_i (cdb_data_i[EU_INT_MULT].except_raised),//(cdb_except_raised_i),
    .cdb_idx_o (cdb_data_o[EU_INT_MULT].rob_idx),//(cdb_idx_o),
    .cdb_data_o (cdb_data_o[EU_INT_MULT].value),//(cdb_data_o),
    .cdb_except_raised_o (cdb_data_o[EU_INT_MULT].except_raised),//(cdb_except_raised_o),
    .cdb_except_o (cdb_data_o[EU_INT_MULT].except_code)//(cdb_except_o)
);

div_rs #(.EU_CTL_LEN (EU_CTL_LEN), .RS_DEPTH (RS_DEPTH), .EXCEPT_LEN(2)) u_div_rs
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),
    .arbiter_valid_i (ex_ready_i[EU_INT_DIV]),
    .arbiter_ready_o (ex_valid_o[EU_INT_DIV]),
	.eu_ctl_i (ex_eu_ctl_i),
    .rs1_ready_i (ex_rs1_ready_i),
    .rs1_idx_i (ex_rs1_idx_i),
    .rs1_value_i (ex_rs1_value_i),
    .rs2_ready_i (ex_rs2_ready_i),
    .rs2_idx_i (ex_rs2_idx_i),
    .rs2_value_i (ex_rs2_value_i),
    .dest_idx_i (ex_rob_idx_i),
	.cdb_ready_i (cdb_ready_i[EU_INT_DIV]),
    .cdb_valid_i (cdb_valid_i),
    .cdb_valid_o (cdb_valid_o[EU_INT_DIV]),
    .cdb_idx_i (cdb_data_i[EU_INT_DIV].rob_idx),//(cdb_idx_i),
    .cdb_data_i (cdb_data_i[EU_INT_DIV].value),//(cdb_data_i),
    .cdb_except_raised_i (cdb_data_i[EU_INT_DIV].except_raised),//(cdb_except_raised_i),
    .cdb_idx_o (cdb_data_o[EU_INT_DIV].rob_idx),//(cdb_idx_o),
    .cdb_data_o (cdb_data_o[EU_INT_DIV].value),//(cdb_data_o),
    .cdb_except_raised_o (cdb_data_o[EU_INT_DIV].except_raised),//(cdb_except_raised_o),
    .cdb_except_o (cdb_data_o[EU_INT_DIV].except_code)//(cdb_except_o)
);

fpu_rs #(.EU_CTL_LEN (EU_CTL_LEN), .RS_DEPTH (RS_DEPTH), .EXCEPT_LEN(2)) u_fpu_rs
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),
    .arbiter_valid_i (ex_ready_i[EU_FPU]),
    .arbiter_ready_o (ex_valid_o[EU_FPU]),
	.eu_ctl_i (ex_eu_ctl_i),
    .rs1_ready_i (ex_rs1_ready_i),
    .rs1_idx_i (ex_rs1_idx_i),
    .rs1_value_i (ex_rs1_value_i),
    .rs2_ready_i (ex_rs2_ready_i),
    .rs2_idx_i (ex_rs2_idx_i),
    .rs2_value_i (ex_rs2_value_i),
    .dest_idx_i (ex_rob_idx_i),
	.cdb_ready_i (cdb_ready_i[EU_FPU]),
    .cdb_valid_i (cdb_valid_i),
    .cdb_valid_o (cdb_valid_o[EU_FPU]),
    .cdb_idx_i (cdb_data_i[EU_FPU].rob_idx),//(cdb_idx_i),
    .cdb_data_i (cdb_data_i[EU_FPU].value),//(cdb_data_i),
    .cdb_except_raised_i (cdb_data_i[EU_FPU].except_raised),//(cdb_except_raised_i),
    .cdb_idx_o (cdb_data_o[EU_FPU].rob_idx),//(cdb_idx_o),
    .cdb_data_o (cdb_data_o[EU_FPU].value),//(cdb_data_o),
    .cdb_except_raised_o (cdb_data_o[EU_FPU].except_raised),//(cdb_except_raised_o),
    .cdb_except_o (cdb_data_o[EU_FPU].except_code)//(cdb_except_o)
);

simd_rs #(.EU_CTL_LEN (EU_CTL_LEN), .RS_DEPTH (RS_DEPTH), .EXCEPT_LEN(2)) u_simd_rs
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),
    .arbiter_valid_i (ex_ready_i[EU_SIMD]),
    .arbiter_ready_o (ex_valid_o[EU_SIMD]),
	.eu_ctl_i (ex_eu_ctl_i),
    .rs1_ready_i (ex_rs1_ready_i),
    .rs1_idx_i (ex_rs1_idx_i),
    .rs1_value_i (ex_rs1_value_i),
    .rs2_ready_i (ex_rs2_ready_i),
    .rs2_idx_i (ex_rs2_idx_i),
    .rs2_value_i (ex_rs2_value_i),
    .dest_idx_i (ex_rob_idx_i),
	.cdb_ready_i (cdb_ready_i[EU_SIMD]),
    .cdb_valid_i (cdb_valid_i),
    .cdb_valid_o (cdb_valid_o[EU_SIMD]),
    .cdb_idx_i (cdb_data_i[EU_SIMD].rob_idx),//(cdb_idx_i),
    .cdb_data_i (cdb_data_i[EU_SIMD].value),//(cdb_data_i),
    .cdb_except_raised_i (cdb_data_i[EU_SIMD].except_raised),//(cdb_except_raised_i),
    .cdb_idx_o (cdb_data_o[EU_SIMD].rob_idx),//(cdb_idx_o),
    .cdb_data_o (cdb_data_o[EU_SIMD].value),//(cdb_data_o),
    .cdb_except_raised_o (cdb_data_o[EU_SIMD].except_raised),//(cdb_except_raised_o),
    .cdb_except_o (cdb_data_o[EU_SIMD].except_code)//(cdb_except_o)
);

branch_rs #(.RS_DEPTH (RS_DEPTH)) u_branch_rs
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),
    .arbiter_valid_i (ex_ready_i[EU_BRANCH_UNIT]),
    .arbiter_ready_o (ex_valid_o[EU_BRANCH_UNIT]),
	.branch_type_i(branch_type_i),
	//.eu_ctl_i (ex_eu_ctl_i),
    .rs1_ready_i (ex_rs1_ready_i),
    .rs1_idx_i (ex_rs1_idx_i),
    .rs1_value_i (ex_rs1_value_i),
    .rs2_ready_i (ex_rs2_ready_i),
    .rs2_idx_i (ex_rs2_idx_i),
    .rs2_value_i (ex_rs2_value_i),
	.imm_value_i (ex_imm_value_i),
    .dest_idx_i (ex_rob_idx_i),
	.pred_pc_i(ex_pred_pc_i),
    .pred_target_i(ex_pred_target_i),
    .pred_taken_i(ex_pred_taken_i),
	.res_pc_o(res_pc_o),
  	.res_target_o(res_target_o),
  	.res_taken_o(res_taken_o),
	.res_mispredict_o(res_mispredict_o),
	.cdb_ready_i (cdb_ready_i[EU_BRANCH_UNIT]),
    .cdb_valid_i (cdb_valid_i),
    .cdb_valid_o (cdb_valid_o[EU_BRANCH_UNIT]),
    .cdb_data_i (cdb_data_i[EU_BRANCH_UNIT]),
    .cdb_data_o (cdb_data_o[EU_BRANCH_UNIT])
);

load_store_unit u_load_store_unit
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),
	.vm_mode_i(vm_mode_i),
	.issue_lb_valid_i(ex_ready_i[EU_LOAD_BUFFER]),
    .issue_sb_valid_i(ex_ready_i[EU_STORE_BUFFER]),
    .lb_issue_ready_o(ex_valid_o[EU_LOAD_BUFFER]),
    .sb_issue_ready_o(ex_valid_o[EU_STORE_BUFFER]),
	.ldst_type_i(ldst_type_i),
	//.eu_ctl_i (ex_eu_ctl_i),
    .rs1_ready_i (ex_rs1_ready_i),
    .rs1_idx_i (ex_rs1_idx_i),
    .rs1_value_i (ex_rs1_value_i),
    .rs2_ready_i (ex_rs2_ready_i),
    .rs2_idx_i (ex_rs2_idx_i),
    .rs2_value_i (ex_rs2_value_i),
	.imm_value_i (ex_imm_value_i),
    .dest_idx_i (ex_rob_idx_i),
	.dtlb_ans_i(dtlb_ans_i),
    .dtlb_wup_i(dtlb_wup_i),
    .dtlb_ready_i(dtlb_ready_i),
    .dtlb_req_o(dtlb_req_o),
    .dcache_ans_i(dcache_ans_i),
    .dcache_wup_i(dcache_wup_i),
    .dcache_ready_i(dcache_ready_i),
    .dcache_req_o(dcache_req_o),
	.rob_head_idx_i(rob_head_idx_i),
    .rob_store_committing_o(rob_store_committing_o),
    .cdb_lb_valid_i(cdb_valid_i),//(cdb_lb_valid_i),
    .cdb_sb_valid_i(cdb_valid_i),//(cdb_sb_valid_i),
    .cdb_lb_ready_i(cdb_ready_i[EU_LOAD_BUFFER]),//cdb_lb_ready_i),
    .cdb_sb_ready_i(cdb_ready_i[EU_STORE_BUFFER]),//cdb_sb_ready_i),
    .lb_cdb_valid_o(cdb_valid_o[EU_LOAD_BUFFER]),//(lb_cdb_valid_o),
    .sb_cdb_valid_o(cdb_valid_o[EU_STORE_BUFFER]),//(sb_cdb_valid_o),
    .cdb_lsb_data_i(cdb_data_i[EU_LOAD_BUFFER]),//(cdb_lsb_data_i),
    .lb_cdb_data_o(cdb_data_o[EU_LOAD_BUFFER]),//(lb_cdb_data_o),
    .sb_cdb_data_o(cdb_data_o[EU_STORE_BUFFER])//(sb_cdb_data_o)
);
    
// TODO: add OPERANDS-ONLY
assign cdb_valid_o[EU_OPERANDS_ONLY] = 0;
assign ex_valid_o[EU_OPERANDS_ONLY] = 0;

endmodule

