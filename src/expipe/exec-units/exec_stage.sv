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
import memory_pkg::mem_req_t;
import memory_pkg::mem_ans_t;
import csr_pkg::SATP_MODE_LEN;

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
    output  logic                       fetch_res_valid_o,
    output  logic                       fetch_res_mispredict_o,

    // ISSUE STAGE
    // -----------

    // Issue stage handshaking
    input   logic                       issue_valid_i [0:EU_N-1], // valid to each RS
    output  logic                       issue_ready_o [0:EU_N-1], // ready from each RS

    // Issue stage data
    input   logic [MAX_EU_CTL_LEN-1:0]  issue_eu_ctl_i,     // controls for the associated EU
    input   logic                       issue_rs1_ready_i,  // first operand is ready at issue time (from the RF or the ROB)
    input   rob_idx_t                   issue_rs1_idx_i,    // the index of the ROB where the first operand can be found (if not ready
    input   logic [XLEN-1:0]            issue_rs1_value_i,  // the value of the first operand (if ready)
    input   logic                       issue_rs2_ready_i,  // second operand is ready at issue time (from the RF or the ROB)
    input   rob_idx_t                   issue_rs2_idx_i,    // the index of the ROB where the first operand can be found (if not ready)
    input   logic [XLEN-1:0]            issue_rs2_value_i,  // the value of the first operand (if ready)
    input   logic [XLEN-1:0]            issue_imm_value_i,  // the value of the immediate field (for st and branches)                   
    input   rob_idx_t                   issue_rob_idx_i,    // the location of the ROB assigned to the instruction
    input   logic [XLEN-1:0]            issue_curr_pc_i,    // the PC of the current issuing instr (branches only)
    input   logic [XLEN-1:0]            issue_pred_target_i,// the predicted target of the current issuing instr (branches only)
    input   logic                       issue_pred_taken_i, // the predicted taken bit of the current issuing instr (branches only)

    // COMMON DATA BUS (CDB)
    // ---------------------

    // CDB handshaking
    input   logic [0:EU_N-1]            cdb_ready_i, // from the CDB arbiter
    input   logic                       cdb_valid_i,            // CDB data is valid
    output  logic [0:EU_N-1]            cdb_valid_o, // to the CDB arbiter

    // CDB data
    input   cdb_data_t                  cdb_data_i,
    output  cdb_data_t [0:EU_N-1]       cdb_data_o,

    // ROB AND CSRs
    // ------------

    // Commit logic data
    input   logic                       cl_sb_pop_store_i,
    output  logic                       cl_sb_sb_head_completed_o,
    output  rob_idx_t                   cl_sb_sb_head_rob_idx_o,

    // CSRs data
    input   logic [SATP_MODE_LEN-1:0]   vm_mode_i,      // virtual memory mode
`ifdef LEN5_FP_EN
    input   logic [FCSR_FRM_LEN-1:0]    csr_frm_i,      // global rounding mode for the FPU
`endif /* LEN5_FP_EN */

    // MEMORY SYSTEM
    // -------------

    input   logic                       mem_valid_i,
    input   logic                       mem_ready_i,
    output  logic                       mem_valid_o,
    output  logic                       mem_ready_o,
    output  mem_req_t                   mem_req_o,
    input   mem_ans_t                   mem_ans_i
);


    // ---------------
    // LOAD/STORE UNIT
    // ---------------

    op_data_t   issue_rs1_data;
    op_data_t   issue_rs2_data;
    assign issue_rs1_data.ready   = issue_rs1_ready_i;
    assign issue_rs1_data.rob_idx = issue_rs1_idx_i;
    assign issue_rs1_data.value   = issue_rs1_value_i;
    assign issue_rs2_data.ready   = issue_rs2_ready_i;
    assign issue_rs2_data.rob_idx = issue_rs2_idx_i;
    assign issue_rs2_data.value   = issue_rs2_value_i;

    load_store_unit #(
        .LB_DEPTH (LDBUFF_DEPTH ),
        .SB_DEPTH (STBUFF_DEPTH )
    ) u_load_store_unit (
    	.clk_i                          (clk_i                            ),
        .rst_n_i                        (rst_n_i                          ),
        .flush_i                        (flush_i                          ),
        .issue_lb_valid_i               (issue_valid_i[EU_LOAD_BUFFER]    ),
        .issue_sb_valid_i               (issue_valid_i[EU_STORE_BUFFER]   ),
        .issue_lb_ready_o               (issue_ready_o[EU_LOAD_BUFFER]    ),
        .issue_sb_ready_o               (issue_ready_o[EU_STORE_BUFFER]   ),
        .issue_type_i                   (issue_eu_ctl_i[2:0]),
        .issue_rs1_i                    (issue_rs1_data                   ),
        .issue_rs2_i                    (issue_rs2_data                   ),
        .issue_imm_i                    (issue_imm_value_i                ),
        .issue_dest_rob_idx_i           (issue_rob_idx_i                  ),
        .commit_pop_store_i             (cl_sb_pop_store_i                ),
        .commit_sb_head_completed_o     (cl_sb_sb_head_completed_o        ),
        .commit_sb_head_rob_idx_o       (cl_sb_sb_head_rob_idx_o          ),
        .cdb_valid_i                    (cdb_valid_i                      ),
        .cdb_lb_ready_i                 (cdb_ready_i[EU_LOAD_BUFFER]      ),
        .cdb_sb_ready_i                 (cdb_ready_i[EU_STORE_BUFFER]     ),
        .cdb_lb_valid_o                 (cdb_valid_o[EU_LOAD_BUFFER]      ),
        .cdb_sb_valid_o                 (cdb_valid_o[EU_STORE_BUFFER]     ),
        .cdb_data_i                     (cdb_data_i                       ),
        .cdb_lb_data_o                  (cdb_data_o[EU_LOAD_BUFFER]       ),
        .cdb_sb_data_o                  (cdb_data_o[EU_STORE_BUFFER]      ),
        .mem_valid_i                    (mem_valid_i                      ),
        .mem_ready_i                    (mem_ready_i                      ),
        .mem_valid_o                    (mem_valid_o                      ),
        .mem_ready_o                    (mem_ready_o                      ),
        .mem_req_o                      (mem_req_o                        ),
        .mem_ans_i                      (mem_ans_i                        )
    );

    // -----------
    // BRANCH UNIT
    // -----------

    branch_unit #(.RS_DEPTH (BU_RS_DEPTH)) u_branch_unit
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
        .curr_pc_i                  (issue_curr_pc_i),
        .pred_target_i              (issue_pred_target_i),
        .pred_taken_i               (issue_pred_taken_i),
        .cdb_ready_i                (cdb_ready_i[EU_BRANCH_UNIT]),
        .cdb_valid_i                (cdb_valid_i),
        .cdb_valid_o                (cdb_valid_o[EU_BRANCH_UNIT]),
        .cdb_data_i                 (cdb_data_i),
        .cdb_data_o                 (cdb_data_o[EU_BRANCH_UNIT])
    );

    // ------------------------
    // INTEGER ARITHMETIC UNITS
    // ------------------------

    // Integer ALU
    // -----------
    alu_unit #(.EU_CTL_LEN (ALU_CTL_LEN), .RS_DEPTH (ALU_RS_DEPTH)) u_alu_unit
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
        .cdb_idx_i              (cdb_data_i.rob_idx),
        .cdb_res_value_i        (cdb_data_i.res_value),
        .cdb_except_raised_i    (cdb_data_i.except_raised),
        .cdb_data_o             (cdb_data_o[EU_INT_ALU])
    );

    `ifdef LEN5_M_EN
    // Integer multiplier
    // ------------------
    mult_unit #(.EU_CTL_LEN (MULT_CTL_LEN), .RS_DEPTH (MULT_RS_DEPTH)) u_mult_unit
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
        .cdb_idx_i              (cdb_data_i.rob_idx),
        .cdb_data_i             (cdb_data_i.value),
        .cdb_except_raised_i    (cdb_data_i.except_raised),
        .cdb_data_o             (cdb_data_o[EU_INT_MULT])
    );

    // Integer divider
    // ---------------
    div_unit #(.EU_CTL_LEN (DIV_CTL_LEN), .RS_DEPTH (DIV_RS_DEPTH)) u_div_unit
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
        .cdb_idx_i              (cdb_data_i.rob_idx),
        .cdb_data_i             (cdb_data_i.value),
        .cdb_except_raised_i    (cdb_data_i.except_raised),
        .cdb_data_o             (cdb_data_o[EU_INT_DIV])
    );
    `endif /* LEN5_M_EN */

    // -------------------
    // FLOATING-POINT UNIT
    // -------------------

    `ifdef LEN5_FP_EN
    fp_unit #(.EU_CTL_LEN (FPU_CTL_LEN), .RS_DEPTH (FPU_RS_DEPTH)) u_fpu_unit
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
        .cdb_idx_i              (cdb_data_i.rob_idx),
        .cdb_data_i             (cdb_data_i.value),
        .cdb_except_raised_i    (cdb_data_i.except_raised),
        .cdb_data_o             (cdb_data_o[EU_FPU]),
        .csr_frm_i              (csr_frm_i)
    );
    `endif /* LEN5_FP_EN */

    // ------------------
    // OPERANDS ONLY UNIT
    // ------------------

    op_only_unit #(.RS_DEPTH(OP_ONLY_RS_DEPTH), .EU_CTL_LEN(OP_ONLY_CTL_LEN)) u_op_only_unit
    (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .flush_i            (flush_i),
        .issue_valid_i      (issue_valid_i[EU_OPERANDS_ONLY]),
        .issue_ready_o      (issue_ready_o[EU_OPERANDS_ONLY]),
        .rs1_ready_i        (issue_rs1_ready_i),
        .rs1_idx_i          (issue_rs1_idx_i),
        .rs1_value_i        (issue_rs1_value_i),
        .dest_idx_i         (issue_rob_idx_i),
        .cdb_ready_i        (cdb_ready_i[EU_OPERANDS_ONLY]),
        .cdb_valid_i        (cdb_valid_i),
        .cdb_valid_o        (cdb_valid_o[EU_OPERANDS_ONLY]),
        .cdb_data_i         (cdb_data_i),
        .cdb_data_o         (cdb_data_o[EU_OPERANDS_ONLY])
    );

endmodule