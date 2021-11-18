// Copyright 2021 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: exec_stage.sv
// Author: Michele Caon, Walid Walid
// Date: 17/11/2021

// LEN5 compilation switches
`include "len5_config.svh"

import len5_pkg::*;
import expipe_pkg::*;

module exec_stage
(
    // Clock, reset, and flush
    input   logic                       clk_i,
    input   logic                       rst_n_i,
    input   logic                       flush_i,

    // FETCH UNIT
    // ----------
    output  logic [XLEN-1:0]            fetch_res_pc_o,
    output  logic [XLEN-1:0]            fetch_res_target_o,
    output  logic                       fetch_res_taken_o,
    output  logic                       fetch_res_mispredict_o,

    // ISSUE STAGE
    // -----------

    // Issue stage handshaking
    input   logic                       issue_valid_i [0:EU_N-1], // valid to each RS
    output  logic                       issue_ready_o [0:EU_N-1], // ready from each RS

    // Issue stage data
    input   logic [MAX_EU_CTL_LEN-1:0]  issue_eu_ctl_i,     // controls for the associated EU
    input   logic                       issue_rs1_ready_i,  // first operand is ready at issue time (from the RF or the ROB)
    input   logic [ROB_IDX_LEN-1:0]     issue_rs1_idx_i,    // the index of the ROB where the first operand can be found (if not ready
    input   logic [XLEN-1:0]            issue_rs1_value_i,  // the value of the first operand (if ready)
    input   logic                       issue_rs2_ready_i,  // second operand is ready at issue time (from the RF or the ROB)
    input   logic [ROB_IDX_LEN-1:0]     issue_rs2_idx_i,    // the index of the ROB where the first operand can be found (if not ready)
    input   logic [XLEN-1:0]            issue_rs2_value_i,  // the value of the first operand (if ready)
    input   logic [I_IMM-1:0]           issue_imm_value_i,  // the value of the immediate field (for st and branches)                   
    input   logic [ROB_IDX_LEN-1:0]     issue_rob_idx_i,    // the location of the ROB assigned to the instruction
    input   logic [XLEN-1:0]            issue_pred_pc_i,    // the PC of the current issuing instr (branches only)
    input   logic [XLEN-1:0]            issue_pred_target_i,// the predicted target of the current issuing instr (branches only)
    input   logic                       issue_pred_taken_i, // the predicted taken bit of the current issuing instr (branches only)

    // COMMON DATA BUS (CDB)
    // ---------------------

    // CDB handshaking
    input   logic                       cdb_ready_i [0:EU_N-1], // from the CDB arbiter
    input   logic                       cdb_valid_i,            // CDB data is valid
    output  logic                       cdb_valid_o [0:EU_N-1], // to the CDB arbiter

    // CDB data
    input   cdb_data_t                  cdb_data_i [0:EU_N-1],
    output  cdb_data_t                  cdb_data_o [0:EU_N-1],

    // ROB AND CSRs
    // ------------

    // ROB data
    input   logic [ROB_IDX_LEN-1:0]     rob_head_idx_i,
    output  logic                       rob_store_committing_o,

    // CSRs data
    input   satp_mode_t                 vm_mode_i,      // virtual memory mode

    // MEMORY SYSTEM
    // -------------

    // D-TLB handshaking and data
    input   dtlb_lsq_ans_t              dtlb_ans_i,
    input   dtlb_lsq_wup_t              dtlb_wup_i,
    input   logic                       dtlb_ready_i,
    output  lsq_dtlb_req_t              dtlb_req_o,

    // D$ handshaking and data
    input   l1dc_lsq_ans_t              dcache_ans_i,
    input   l1dc_lsq_wup_t              dcache_wup_i,
    input   logic                       dcache_ready_i,
    output  lsq_l1dc_req_t              dcache_req_o
);


    // ---------------
    // LOAD/STORE UNIT
    // ---------------

    load_store_unit u_load_store_unit
    (
        .clk_i                      (clk_i),
        .rst_n_i                    (rst_n_i),
        .flush_i                    (flush_i),
        .vm_mode_i                  (vm_mode_i),
        .issue_lb_valid_i           (issue_valid_i[EU_LOAD_BUFFER]),
        .issue_sb_valid_i           (issue_valid_i[EU_STORE_BUFFER]),
        .lb_issue_ready_o           (issue_ready_o[EU_LOAD_BUFFER]),
        .sb_issue_ready_o           (issue_ready_o[EU_STORE_BUFFER]),
        .ldst_type_i                (issue_eu_ctl_i[LDST_TYPE_LEN-1:0]),
        .rs1_ready_i                (issue_rs1_ready_i),
        .rs1_idx_i                  (issue_rs1_idx_i),
        .rs1_value_i                (issue_rs1_value_i),
        .rs2_ready_i                (issue_rs2_ready_i),
        .rs2_idx_i                  (issue_rs2_idx_i),
        .rs2_value_i                (issue_rs2_value_i),
        .imm_value_i                (issue_imm_value_i),
        .dest_idx_i                 (issue_rob_idx_i),
        .dtlb_ans_i                 (dtlb_ans_i),
        .dtlb_wup_i                 (dtlb_wup_i),
        .dtlb_ready_i               (dtlb_ready_i),
        .dtlb_req_o                 (dtlb_req_o),
        .dcache_ans_i               (dcache_ans_i),
        .dcache_wup_i               (dcache_wup_i),
        .dcache_ready_i             (dcache_ready_i),
        .dcache_req_o               (dcache_req_o),
        .rob_head_idx_i             (rob_head_idx_i),
        .rob_store_committing_o     (rob_store_committing_o),
        .cdb_lb_valid_i             (cdb_valid_i),
        .cdb_sb_valid_i             (cdb_valid_i),
        .cdb_lb_ready_i             (cdb_ready_i[EU_LOAD_BUFFER]),
        .cdb_sb_ready_i             (cdb_ready_i[EU_STORE_BUFFER]),
        .lb_cdb_valid_o             (cdb_valid_o[EU_LOAD_BUFFER]),
        .sb_cdb_valid_o             (cdb_valid_o[EU_STORE_BUFFER]),
        .cdb_lsb_data_i             (cdb_data_i[EU_LOAD_BUFFER]),
        .lb_cdb_data_o              (cdb_data_o[EU_LOAD_BUFFER]),
        .sb_cdb_data_o              (cdb_data_o[EU_STORE_BUFFER])
    );

    // -----------
    // BRANCH UNIT
    // -----------

    branch_unit #(.RS_DEPTH (BU_RS_DEPTH)) u_branch_rs
    (
        .clk_i                      (clk_i),
        .rst_n_i                    (rst_n_i),
        .flush_i                    (flush_i),
        .issue_valid_i              (issue_valid_i[EU_BRANCH_UNIT]),
        .issue_ready_o              (issue_ready_o[EU_BRANCH_UNIT]),
        .branch_type_i              (issue_eu_ctl_i[BU_CTL_LEN-1:0]),
        .rs1_ready_i                (issue_rs1_ready_i),
        .rs1_idx_i                  (issue_rs1_idx_i),
        .rs1_value_i                (issue_rs1_value_i),
        .rs2_ready_i                (issue_rs2_ready_i),
        .rs2_idx_i                  (issue_rs2_idx_i),
        .rs2_value_i                (issue_rs2_value_i),
        .imm_value_i                (issue_imm_value_i),
        .dest_idx_i                 (issue_rob_idx_i),
        .pred_pc_i                  (issue_pred_pc_i),
        .pred_target_i              (issue_pred_target_i),
        .pred_taken_i               (issue_pred_taken_i),
        .res_pc_o                   (fetch_res_pc_o),
        .res_target_o               (fetch_res_target_o),
        .res_taken_o                (fetch_res_taken_o),
        .res_mispredict_o           (fetch_res_mispredict_o),
        .cdb_ready_i                (cdb_ready_i[EU_BRANCH_UNIT]),
        .cdb_valid_i                (cdb_valid_i),
        .cdb_valid_o                (cdb_valid_o[EU_BRANCH_UNIT]),
        .cdb_data_i                 (cdb_data_i[EU_BRANCH_UNIT]),
        .cdb_data_o                 (cdb_data_o[EU_BRANCH_UNIT])
    );

    // ------------------------
    // INTEGER ARITHMETIC UNITS
    // ------------------------

    // Integer ALU
    // -----------
    alu_unit #(.EU_CTL_LEN (ALU_CTL_LEN), .RS_DEPTH (ALU_RS_DEPTH), .EXCEPT_LEN(ALU_EXCEPT_LEN)) u_alu_rs
    (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .flush_i                (flush_i),
        .issue_valid_i          (issue_valid_i[EU_INT_ALU]),
        .issue_ready_o          (issue_ready_o[EU_INT_ALU]),
        .eu_ctl_i               (issue_eu_ctl_i[ALU_CTL_LEN-1:0]),
        .rs1_ready_i            (issue_rs1_ready_i),
        .rs1_idx_i              (issue_rs1_idx_i),
        .rs1_value_i            (issue_rs1_value_i),
        .rs2_ready_i            (issue_rs2_ready_i),
        .rs2_idx_i              (issue_rs2_idx_i),
        .rs2_value_i            (issue_rs2_value_i),
        .dest_idx_i             (issue_rob_idx_i),
        .cdb_ready_i            (cdb_ready_i[EU_INT_ALU]),
        .cdb_valid_i            (cdb_valid_i),
        .cdb_valid_o            (cdb_valid_o[EU_INT_ALU]),
        .cdb_idx_i              (cdb_data_i[EU_INT_ALU].rob_idx),
        .cdb_data_i             (cdb_data_i[EU_INT_ALU].value),
        .cdb_except_raised_i    (cdb_data_i[EU_INT_ALU].except_raised),
        .cdb_idx_o              (cdb_data_o[EU_INT_ALU].rob_idx),
        .cdb_data_o             (cdb_data_o[EU_INT_ALU].value),
        .cdb_except_raised_o    (cdb_data_o[EU_INT_ALU].except_raised),
        .cdb_except_o           (cdb_data_o[EU_INT_ALU].except_code)
    );

    `ifdef LEN5_M_EN
    // Integer multiplier
    // ------------------
    mult_unit #(.EU_CTL_LEN (MULT_CTL_LEN), .RS_DEPTH (MULT_RS_DEPTH), .EXCEPT_LEN(MULT_EXCEPT_LEN)) u_mult_rs
    (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .flush_i                (flush_i),
        .issue_valid_i          (issue_valid_i[EU_INT_MULT]),
        .issue_ready_o          (issue_ready_o[EU_INT_MULT]),
        .eu_ctl_i               (issue_eu_ctl_i[MULT_CTL_LEN-1:0]),
        .rs1_ready_i            (issue_rs1_ready_i),
        .rs1_idx_i              (issue_rs1_idx_i),
        .rs1_value_i            (issue_rs1_value_i),
        .rs2_ready_i            (issue_rs2_ready_i),
        .rs2_idx_i              (issue_rs2_idx_i),
        .rs2_value_i            (issue_rs2_value_i),
        .dest_idx_i             (issue_rob_idx_i),
        .cdb_ready_i            (cdb_ready_i[EU_INT_MULT]),
        .cdb_valid_i            (cdb_valid_i),
        .cdb_valid_o            (cdb_valid_o[EU_INT_MULT]),
        .cdb_idx_i              (cdb_data_i[EU_INT_MULT].rob_idx),
        .cdb_data_i             (cdb_data_i[EU_INT_MULT].value),
        .cdb_except_raised_i    (cdb_data_i[EU_INT_MULT].except_raised),
        .cdb_idx_o              (cdb_data_o[EU_INT_MULT].rob_idx),,
        .cdb_data_o             (cdb_data_o[EU_INT_MULT].value),
        .cdb_except_raised_o    (cdb_data_o[EU_INT_MULT].except_raised),
        .cdb_except_o           (cdb_data_o[EU_INT_MULT].except_code)
    );

    // Integer divider
    // ---------------
    div_unit #(.EU_CTL_LEN (DIV_CTL_LEN), .RS_DEPTH (DIV_RS_DEPTH), .EXCEPT_LEN(DIV_EXCEPT_LEN)) u_div_rs
    (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .flush_i                (flush_i),
        .issue_valid_i          (issue_valid_i[EU_INT_DIV]),
        .issue_ready_o          (issue_ready_o[EU_INT_DIV]),
        .eu_ctl_i               (issue_eu_ctl_i[DIV_CTL_LEN-1:0]),
        .rs1_ready_i            (issue_rs1_ready_i),
        .rs1_idx_i              (issue_rs1_idx_i),
        .rs1_value_i            (issue_rs1_value_i),
        .rs2_ready_i            (issue_rs2_ready_i),
        .rs2_idx_i              (issue_rs2_idx_i),
        .rs2_value_i            (issue_rs2_value_i),
        .dest_idx_i             (issue_rob_idx_i),
        .cdb_ready_i            (cdb_ready_i[EU_INT_DIV]),
        .cdb_valid_i            (cdb_valid_i),
        .cdb_valid_o            (cdb_valid_o[EU_INT_DIV]),
        .cdb_idx_i              (cdb_data_i[EU_INT_DIV].rob_idx),
        .cdb_data_i             (cdb_data_i[EU_INT_DIV].value),
        .cdb_except_raised_i    (cdb_data_i[EU_INT_DIV].except_raised),
        .cdb_idx_o              (cdb_data_o[EU_INT_DIV].rob_idx),
        .cdb_data_o             (cdb_data_o[EU_INT_DIV].value),
        .cdb_except_raised_o    (cdb_data_o[EU_INT_DIV].except_raised),
        .cdb_except_o           (cdb_data_o[EU_INT_DIV].except_code)
    );
    `endif /* LEN5_M_EN */

    // -------------------
    // FLOATING-POINT UNIT
    // -------------------

    `ifdef LEN5_FP_EN
    fp_unit #(.EU_CTL_LEN (FPU_CTL_LEN), .RS_DEPTH (FPU_RS_DEPTH), .EXCEPT_LEN(FPU_EXCEPT_LEN)) u_fpu_rs
    (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .flush_i                (flush_i),
        .issue_valid_i          (issue_valid_i[EU_FPU]),
        .issue_ready_o          (issue_ready_o[EU_FPU]),
        .eu_ctl_i               (issue_eu_ctl_i[FPU_CTL_LEN-1:0]),
        .rs1_ready_i            (issue_rs1_ready_i),
        .rs1_idx_i              (issue_rs1_idx_i),
        .rs1_value_i            (issue_rs1_value_i),
        .rs2_ready_i            (issue_rs2_ready_i),
        .rs2_idx_i              (issue_rs2_idx_i),
        .rs2_value_i            (issue_rs2_value_i),
        .dest_idx_i             (issue_rob_idx_i),
        .cdb_ready_i            (cdb_ready_i[EU_FPU]),
        .cdb_valid_i            (cdb_valid_i),
        .cdb_valid_o            (cdb_valid_o[EU_FPU]),
        .cdb_idx_i              (cdb_data_i[EU_FPU].rob_idx),
        .cdb_data_i             (cdb_data_i[EU_FPU].value),
        .cdb_except_raised_i    (cdb_data_i[EU_FPU].except_raised),
        .cdb_idx_o              (cdb_data_o[EU_FPU].rob_idx),
        .cdb_data_o             (cdb_data_o[EU_FPU].value),
        .cdb_except_raised_o    (cdb_data_o[EU_FPU].except_raised),
        .cdb_except_o           (cdb_data_o[EU_FPU].except_code)
    );
    `endif /* LEN5_FP_EN */

    // ------------------
    // OPERANDS ONLY UNIT
    // ------------------

    op_only_unit #(.RS_DEPTH(OP_ONLY_RS_DEPTH), .EU_CTL_LEN(OP_ONLY_CTL_LEN))
    (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .flush_i            (flush_i),
        .issue_valid_i      (issue_valid_i[EU_OPERANDS_ONLY]),
        .issue_ready_o      (issue_ready_o[EU_OPERANDS_ONLY]),
        .rs1_ready_i        (issue_rs1_ready_i),
        .rs1_idx_i          (issue_rs1_idx_i),
        .rs1_value_i        (issue_rs1_value_i),
        .cdb_ready_i        (cdb_ready_i[EU_OPERANDS_ONLY]),
        .cdb_valid_i        (cdb_valid_i),
        .cdb_valid_o        (cdb_valid_o[EU_OPERANDS_ONLY]),
        .cdb_data_i         (cdb_data_i[EU_OPERANDS_ONLY]),
        .cdb_data_o         (cdb_data_o[EU_OPERANDS_ONLY])
    )

endmodule