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
    input   logic                       mis_flush_i,
    input   logic                       except_flush_i,

    // ISSUE STAGE
    input   logic                       issue_valid_i [0:EU_N-1], // valid to each RS
    output  logic                       issue_ready_o [0:EU_N-1], // ready from each RS
    input   eu_ctl_t                    issue_eu_ctl_i,     // controls for the associated EU
    input   op_data_t                   issue_rs1_i,        // rs1 value, ROB index and availability
    input   op_data_t                   issue_rs2_i,        // rs1 value, ROB index and availability
    input   logic [XLEN-1:0]            issue_imm_value_i,  // the value of the immediate field (for st and branches)                   
    input   rob_idx_t                   issue_rob_idx_i,    // the location of the ROB assigned to the instruction
    input   logic [XLEN-1:0]            issue_curr_pc_i,    // the PC of the current issuing instr (branches only)
    input   logic [XLEN-1:0]            issue_pred_target_i,// the predicted target of the current issuing instr (branches only)
    input   logic                       issue_pred_taken_i, // the predicted taken bit of the current issuing instr (branches only)

    // COMMON DATA BUS (CDB)
    input   logic [0:EU_N-1]            cdb_ready_i, // from the CDB arbiter
    input   logic                       cdb_valid_i,            // CDB data is valid
    output  logic [0:EU_N-1]            cdb_valid_o, // to the CDB arbiter
    input   cdb_data_t                  cdb_data_i,
    output  cdb_data_t [0:EU_N-1]       cdb_data_o,

    // ROB AND CSRs
    input   logic                       comm_sb_spec_instr_i,
    input   rob_idx_t                   comm_sb_rob_head_idx_i,
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
    load_store_unit #(
        .LB_DEPTH (LDBUFF_DEPTH ),
        .SB_DEPTH (STBUFF_DEPTH )
    ) u_load_store_unit (
    	.clk_i                          (clk_i                          ),
        .rst_n_i                        (rst_n_i                        ),
        .mis_flush_i                    (mis_flush_i                    ),
        .except_flush_i                 (except_flush_i                 ),
        .issue_lb_valid_i               (issue_valid_i[EU_LOAD_BUFFER]  ),
        .issue_sb_valid_i               (issue_valid_i[EU_STORE_BUFFER] ),
        .issue_lb_ready_o               (issue_ready_o[EU_LOAD_BUFFER]  ),
        .issue_sb_ready_o               (issue_ready_o[EU_STORE_BUFFER] ),
        .issue_type_i                   (issue_eu_ctl_i.lsu             ),
        .issue_rs1_i                    (issue_rs1_i                    ),
        .issue_rs2_i                    (issue_rs2_i                    ),
        .issue_imm_i                    (issue_imm_value_i              ),
        .issue_dest_rob_idx_i           (issue_rob_idx_i                ),
        .comm_spec_instr_i              (comm_sb_spec_instr_i           ),
        .comm_rob_head_idx_i            (comm_sb_rob_head_idx_i         ),
        .cdb_valid_i                    (cdb_valid_i                    ),
        .cdb_lb_ready_i                 (cdb_ready_i[EU_LOAD_BUFFER]    ),
        .cdb_sb_ready_i                 (cdb_ready_i[EU_STORE_BUFFER]   ),
        .cdb_lb_valid_o                 (cdb_valid_o[EU_LOAD_BUFFER]    ),
        .cdb_sb_valid_o                 (cdb_valid_o[EU_STORE_BUFFER]   ),
        .cdb_data_i                     (cdb_data_i                     ),
        .cdb_lb_data_o                  (cdb_data_o[EU_LOAD_BUFFER]     ),
        .cdb_sb_data_o                  (cdb_data_o[EU_STORE_BUFFER]    ),
        .mem_valid_i                    (mem_valid_i                    ),
        .mem_ready_i                    (mem_ready_i                    ),
        .mem_valid_o                    (mem_valid_o                    ),
        .mem_ready_o                    (mem_ready_o                    ),
        .mem_req_o                      (mem_req_o                      ),
        .mem_ans_i                      (mem_ans_i                      )
    );

    // -----------
    // BRANCH UNIT
    // -----------
    branch_unit #(.RS_DEPTH (BU_RS_DEPTH)) u_branch_unit
    (
        .clk_i                      (clk_i                          ),
        .rst_n_i                    (rst_n_i                        ),
        .flush_i                    (mis_flush_i                    ),
        .issue_valid_i              (issue_valid_i[EU_BRANCH_UNIT]  ),
        .issue_ready_o              (issue_ready_o[EU_BRANCH_UNIT]  ),
        .issue_branch_type_i        (issue_eu_ctl_i.bu              ),
        .issue_rs1_i                (issue_rs1_i                    ),
        .issue_rs2_i                (issue_rs2_i                    ),
        .issue_imm_value_i          (issue_imm_value_i              ),
        .issue_dest_rob_idx_i       (issue_rob_idx_i                ),
        .issue_curr_pc_i            (issue_curr_pc_i                ),
        .issue_pred_target_i        (issue_pred_target_i            ),
        .issue_pred_taken_i         (issue_pred_taken_i             ),
        .cdb_ready_i                (cdb_ready_i[EU_BRANCH_UNIT]    ),
        .cdb_valid_i                (cdb_valid_i                    ),
        .cdb_valid_o                (cdb_valid_o[EU_BRANCH_UNIT]    ),
        .cdb_data_i                 (cdb_data_i                     ),
        .cdb_data_o                 (cdb_data_o[EU_BRANCH_UNIT]     )
    );

    // ------------------------
    // INTEGER ARITHMETIC UNITS
    // ------------------------

    // Integer ALU
    // -----------
    alu_unit #(.EU_CTL_LEN (MAX_EU_CTL_LEN), .RS_DEPTH (ALU_RS_DEPTH)) u_alu_unit
    (
        .clk_i                  (clk_i                      ),
        .rst_n_i                (rst_n_i                    ),
        .flush_i                (mis_flush_i                ),
        .issue_valid_i          (issue_valid_i[EU_INT_ALU]  ),
        .issue_ready_o          (issue_ready_o[EU_INT_ALU]  ),
        .issue_eu_ctl_i         (issue_eu_ctl_i.alu         ),
        .issue_rs1_i            (issue_rs1_i                ),
        .issue_rs2_i            (issue_rs2_i                ),
        .issue_dest_rob_idx_i   (issue_rob_idx_i            ),
        .cdb_ready_i            (cdb_ready_i[EU_INT_ALU]    ),
        .cdb_valid_i            (cdb_valid_i                ),
        .cdb_valid_o            (cdb_valid_o[EU_INT_ALU]    ),
        .cdb_data_i             (cdb_data_i                 ),
        .cdb_data_o             (cdb_data_o[EU_INT_ALU]     )
    );

    `ifdef LEN5_M_EN
    // Integer multiplier
    // ------------------
    mult_unit #(
        .EU_CTL_LEN (MAX_EU_CTL_LEN ), 
        .RS_DEPTH   (MULT_RS_DEPTH  )
    ) u_mult_unit (
        .clk_i                  (clk_i                      ),
        .rst_n_i                (rst_n_i                    ),
        .flush_i                (mis_flush_i                ),
        .issue_valid_i          (issue_valid_i[EU_INT_MULT] ),
        .issue_ready_o          (issue_ready_o[EU_INT_MULT] ),
        .issue_eu_ctl_i         (issue_eu_ctl_i.mult        ),
        .issue_rs1_i            (issue_rs1_i                ),
        .issue_rs2_i            (issue_rs2_i                ),
        .issue_dest_rob_idx_i   (issue_rob_idx_i            ),
        .cdb_ready_i            (cdb_ready_i[EU_INT_MULT]   ),
        .cdb_valid_i            (cdb_valid_i                ),
        .cdb_valid_o            (cdb_valid_o[EU_INT_MULT]   ),
        .cdb_data_i             (cdb_data_i                 ),
        .cdb_data_o             (cdb_data_o[EU_INT_MULT]    )
    );

    // Integer divider
    // ---------------
    div_unit #(
        .EU_CTL_LEN (MAX_EU_CTL_LEN ), 
        .RS_DEPTH   (DIV_RS_DEPTH   ),
        .PIPE_DEPTH (DIV_PIPE_DEPTH )
    ) u_div_unit (
        .clk_i                  (clk_i                     ),
        .rst_n_i                (rst_n_i                   ),
        .flush_i                (mis_flush_i               ),
        .issue_valid_i          (issue_valid_i[EU_INT_DIV] ),
        .issue_ready_o          (issue_ready_o[EU_INT_DIV] ),
        .issue_eu_ctl_i         (issue_eu_ctl_i.div        ),
        .issue_rs1_i            (issue_rs1_i               ),
        .issue_rs2_i            (issue_rs2_i               ),
        .issue_dest_rob_idx_i   (issue_rob_idx_i           ),
        .cdb_ready_i            (cdb_ready_i[EU_INT_DIV]   ),
        .cdb_valid_i            (cdb_valid_i               ),
        .cdb_valid_o            (cdb_valid_o[EU_INT_DIV]   ),
        .cdb_data_i             (cdb_data_i                ),
        .cdb_data_o             (cdb_data_o[EU_INT_DIV]    )
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
        .flush_i                (mis_flush_i),
        .issue_valid_i          (issue_valid_i[EU_FPU]),
        .issue_ready_o          (issue_ready_o[EU_FPU]),
        .eu_ctl_i               (issue_eu_ctl_i[FPU_CTL_LEN-1:0]),
        .rs1_ready_i            (issue_rs1_i.ready),
        .rs1_idx_i              (issue_rs1_i.rob_idx),
        .rs1_value_i            (issue_rs1_i.value),
        .rs2_ready_i            (issue_rs2_i.ready),
        .rs2_idx_i              (issue_rs2_i.rob_idx),
        .rs2_value_i            (issue_rs2_i.value),
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
endmodule