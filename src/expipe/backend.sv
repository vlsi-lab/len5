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
// File: backend.sv
// Author: Michele Caon
// Date: 17/11/2021

// LEN5 compilation switches
`include "len5_config.svh"

import len5_pkg::*;
import expipe_pkg::*;
import fetch_pkg::prediction_t;
import fetch_pkg::resolution_t;
import csr_pkg::*;
import memory_pkg::*;

module backend (
    // Clock, reset, and flush
    input   logic                   clk_i,
    input   logic                   rst_n_i,

    // Frontend
    input   logic                   fetch_valid_i,
    output  logic                   fetch_ready_o,
    input   logic [ILEN-1:0]        fetch_instr_i,
    input   prediction_t            fetch_pred_i,
    input   logic                   fetch_except_raised_i,
    input   except_code_t           fetch_except_code_i,
    output  logic                   fetch_bpu_flush_o,
    output  logic                   fetch_res_valid_o,
    output  resolution_t            fetch_res_o,
    output  logic                   fetch_except_raised_o,
    output  logic [XLEN-1:0]        fetch_except_pc_o,

    /* Memory system */
    input   logic                   mem_valid_i,
    input   logic                   mem_ready_i,
    output  logic                   mem_valid_o,
    output  logic                   mem_ready_o,
    output  mem_req_t               mem_req_o,
    input   mem_ans_t               mem_ans_i
);

    // ----------------
    // INTERNAL SIGNALS
    // ----------------

    // Issue logic <--> integer register status register
    // -------------------------------------------------
    logic                       int_regstat_il_ready;
    logic                       il_int_regstat_valid;
    logic                       int_regstat_il_rs1_busy;
    rob_idx_t     int_regstat_il_rs1_rob_idx;
    logic                       int_regstat_il_rs2_busy;
    rob_idx_t     int_regstat_il_rs2_rob_idx;
    logic [REG_IDX_LEN-1:0]     il_int_regstat_rd_idx;
    rob_idx_t     il_int_regstat_rob_idx;
    logic [REG_IDX_LEN-1:0]     il_int_regstat_rs1_idx;
    logic [REG_IDX_LEN-1:0]     il_int_regstat_rs2_idx;

    // Integer register status register <--> commit logic
    // --------------------------------------------------
    logic                       comm_intrs_valid;
    logic                       int_regstat_comm_ready;

    // Issue logic <--> integer register file
    // --------------------------------------
    logic [XLEN-1:0]            intrf_il_rs1_value;
    logic [XLEN-1:0]            intrf_il_rs2_value;
    logic [REG_IDX_LEN-1:0]     il_intrf_rs1_idx;
    logic [REG_IDX_LEN-1:0]     il_intrf_rs2_idx;

    // Integer register file <--> commit logic
    // ---------------------------------------
    logic                       comm_intrf_valid;
    logic                       intrf_comm_ready;

`ifdef LEN5_FP_EN
    // Issue logic <--> floating-point register status register
    // --------------------------------------------------------
    logic                       fp_regstat_il_ready;
    logic                       il_fp_regstat_valid;
    logic                       fp_regstat_il_rs1_busy;
    rob_idx_t     fp_regstat_il_rs1_rob_idx;
    logic                       fp_regstat_il_rs2_busy;
    rob_idx_t     fp_regstat_il_rs2_rob_idx;
    logic [REG_IDX_LEN-1:0]     il_fp_regstat_rd_idx;
    rob_idx_t     il_fp_regstat_rob_idx;
    logic [REG_IDX_LEN-1:0]     il_fp_regstat_rs1_idx;
    logic [REG_IDX_LEN-1:0]     il_fp_regstat_rs2_idx;

    // Floating-point register status register <--> commit logic
    // ---------------------------------------------------------
    logic                       comm_fprs_valid;
    logic                       fp_regstat_comm_ready;

    // Issue logic <--> floating-point register file
    // ---------------------------------------------
    logic [XLEN-1:0]            fprf_il_rs1_value;
    logic [XLEN-1:0]            fprf_il_rs2_value;
    logic [REG_IDX_LEN-1:0]     il_fprf_rs1_idx;
    logic [REG_IDX_LEN-1:0]     il_fprf_rs2_idx;

    // Floating-point register file <--> commit logic
    // ----------------------------------------------
    logic                       comm_fprf_valid;
    logic                       fprf_comm_ready;
`endif /* LEN5_FP_EN */

    // Issue stage <--> execution units
    // --------------------------------
    logic                       ex_issue_ready [0:EU_N-1];
    logic                       il_ex_valid [0:EU_N-1];
    logic [MAX_EU_CTL_LEN-1:0]  issue_ex_eu_ctl;
    logic                       issue_ex_rs1_ready;
    rob_idx_t                   issue_ex_rs1_idx;
    logic [XLEN-1:0]            issue_ex_rs1_value;
    logic                       issue_ex_rs2_ready;
    rob_idx_t                   issue_ex_rs2_idx;
    logic [XLEN-1:0]            issue_ex_rs2_value;
    logic [XLEN-1:0]            issue_ex_imm_value;
    rob_idx_t                   issue_ex_rob_idx;
    logic [XLEN-1:0]            issue_ex_curr_pc;
    logic [XLEN-1:0]            issue_ex_pred_target;
    logic                       issue_ex_pred_taken;

    // Issue stage <--> ROB
    // --------------------
    logic                       rob_il_ready;
    logic                       il_rob_valid;
    logic                       rob_il_rs1_ready;
    logic [XLEN-1:0]            rob_il_rs1_value;
    logic                       rob_il_rs2_ready;
    logic [XLEN-1:0]            rob_il_rs2_value;
    rob_idx_t                   rob_il_tail_idx;
    rob_idx_t                   il_rob_rs1_idx;
    rob_idx_t                   il_rob_rs2_idx;
    rob_entry_t                 il_rob_data;

    // Issue stage <--> CSRs
    // ---------------------
    logic                       csr_il_mstatus_tsr;

    // Execution stage <--> CDB
    // ------------------------
    logic [0:EU_N-1]            cdb_ex_ready;
    logic [0:EU_N-1]            ex_cdb_valid;
    cdb_data_t [0:EU_N-1]       ex_cdb_data;

    // Execution stage <--> commit logic
    // ---------------------------------
    logic                       cl_sb_pop_store;
    logic                       sb_comm_store_head_completed;
    rob_idx_t                   sb_comm_store_head_rob_idx;

    // Execution stage <--> CSRs
    // -------------------------
    logic [FCSR_FRM_LEN-1:0]    csr_ex_frm;
    logic [SATP_MODE_LEN-1:0]   csr_ex_vm_mode;

    // CDB <--> ROB
    // ------------
    logic                       rob_cdb_ready;

    // CDB --> multiple units
    // ----------------------
    logic                       cdb_others_valid;
    cdb_data_t                  cdb_others_data;

    // ROB <--> commit logic
    // ---------------------
    logic                       comm_rob_ready;
    logic                       rob_comm_valid;
    rob_entry_t                 rob_comm_head_entry;
    rob_idx_t                   rob_comm_head_idx;

    // Commit logic --> (both) register status registers
    // -------------------------------------------------
    rob_idx_t                   comm_rs_head_idx;

    // Commit logic --> (both) register files
    // --------------------------------------
    logic [REG_IDX_LEN-1:0]     comm_rf_rd_idx;
    logic [XLEN-1:0]            comm_rf_rd_value;

    // Commit logic --> issue logic
    // ----------------------------
    logic                       comm_issue_resume;
    logic                       comm_issue_reg0_valid;
    logic [XLEN-1:0]            comm_issue_reg0_value;
    rob_idx_t                   comm_issue_reg0_idx;
    logic                       comm_issue_reg1_valid;
    logic [XLEN-1:0]            comm_issue_reg1_value;
    rob_idx_t                   comm_issue_reg1_idx;
    logic                       comm_issue_commreg_valid;
    logic [XLEN-1:0]            comm_issue_commreg_value;
    rob_idx_t                   comm_issue_commreg_idx;

    // Commit logic <--> CSRs
    // ----------------------
    logic                       comm_csr_valid;
    logic                       csr_comm_ready;
    logic [XLEN-1:0]            csr_comm_data;
    logic                       csr_comm_acc_exc;
    csr_instr_t                 comm_csr_instr_type;
    logic [FUNCT3_LEN-1:0]      comm_csr_funct3;
    logic [CSR_ADDR_LEN-1:0]    comm_csr_addr;
    logic [REG_IDX_LEN]         comm_csr_rs1_idx;
    logic [XLEN-1:0]            comm_csr_rs1_value;
    except_code_t               comm_csr_except_code;
    logic [REG_IDX_LEN-1:0]     comm_csr_rd_idx;

    // Commit Logic <--> others
    // ------------------------
    logic                       mis_flush; // flush on misprediction

    // -----------
    // ISSUE STAGE
    // -----------
    // Issue queue and issue logic (includes the instruction decoder)

    issue_stage u_issue_stage
    (
        .clk_i                          (clk_i),
        .rst_n_i                        (rst_n_i),
        .flush_i                        (mis_flush),

        .fetch_valid_i                  (fetch_valid_i),
        .fetch_ready_o                  (fetch_ready_o),
        .fetch_curr_pc_i                (fetch_pred_i.pc),
        .fetch_instr_i                  (fetch_instr_i),
        .fetch_pred_target_i            (fetch_pred_i.target),
        .fetch_pred_taken_i             (fetch_pred_i.taken),
        .fetch_except_raised_i          (fetch_except_raised_i),
        .fetch_except_code_i            (fetch_except_code_i),

        .int_regstat_ready_i            (int_regstat_il_ready),
        .int_regstat_valid_o            (il_int_regstat_valid),
        .int_regstat_rs1_busy_i         (int_regstat_il_rs1_busy),
        .int_regstat_rs1_rob_idx_i      (int_regstat_il_rs1_rob_idx),
        .int_regstat_rs2_busy_i         (int_regstat_il_rs2_busy),
        .int_regstat_rs2_rob_idx_i      (int_regstat_il_rs2_rob_idx),
        .int_regstat_rd_idx_o           (il_int_regstat_rd_idx),
        .int_regstat_rob_idx_o          (il_int_regstat_rob_idx),
        .int_regstat_rs1_idx_o          (il_int_regstat_rs1_idx),
        .int_regstat_rs2_idx_o          (il_int_regstat_rs2_idx),

        .intrf_rs1_value_i              (intrf_il_rs1_value),
        .intrf_rs2_value_i              (intrf_il_rs2_value),
        .intrf_rs1_idx_o                (il_intrf_rs1_idx),
        .intrf_rs2_idx_o                (il_intrf_rs2_idx),

    `ifdef LEN5_FP_EN
        .fp_regstat_ready_i             (fp_regstat_il_ready),
        .fp_regstat_valid_o             (il_fp_regstat_valid),
        .fp_regstat_rs1_busy_i          (fp_regstat_il_rs1_busy),
        .fp_regstat_rs1_rob_idx_i       (fp_regstat_il_rs1_rob_idx),
        .fp_regstat_rs2_busy_i          (fp_regstat_il_rs2_busy),
        .fp_regstat_rs2_rob_idx_i       (fp_regstat_il_rs2_rob_idx),
        .fp_regstat_rd_idx_o            (il_fp_regstat_rd_idx),
        .fp_regstat_rob_idx_o           (il_fp_regstat_rob_idx),
        .fp_regstat_rs1_idx_o           (il_fp_regstat_rs1_idx),
        .fp_regstat_rs2_idx_o           (il_fp_regstat_rs2_idx),

        .fprf_rs1_value_i               (fprf_il_rs1_value),
        .fprf_rs2_value_i               (fprf_il_rs2_value),
        .fprf_rs1_idx_o                 (il_fprf_rs1_idx),
        .fprf_rs2_idx_o                 (il_fprf_rs2_idx),
    `endif /* LEN5_FP_EN */

    `ifdef LEN5_PRIVILEGED_EN
        .mstatus_tsr_i                  (csr_il_mstatus_tsr),
    `endif /* LEN5_PRIVILEGED_EN */

        .ex_ready_i                     (ex_issue_ready),
        .ex_valid_o                     (il_ex_valid),
        .ex_eu_ctl_o                    (issue_ex_eu_ctl),
        .ex_rs1_ready_o                 (issue_ex_rs1_ready),
        .ex_rs1_idx_o                   (issue_ex_rs1_idx),
        .ex_rs1_value_o                 (issue_ex_rs1_value),
        .ex_rs2_ready_o                 (issue_ex_rs2_ready),
        .ex_rs2_idx_o                   (issue_ex_rs2_idx),
        .ex_rs2_value_o                 (issue_ex_rs2_value),
        .ex_imm_value_o                 (issue_ex_imm_value),
        .ex_rob_idx_o                   (issue_ex_rob_idx),
        .ex_curr_pc_o                   (issue_ex_curr_pc),
        .ex_pred_target_o               (issue_ex_pred_target),
        .ex_pred_taken_o                (issue_ex_pred_taken),

        .cdb_valid_i                    (cdb_others_valid),
        .cdb_except_raised_i            (cdb_others_data.except_raised),
        .cdb_value_i                    (cdb_others_data.res_value),
        .cdb_rob_idx_i                  (cdb_others_data.rob_idx),

        .rob_ready_i                    (rob_il_ready),
        .rob_valid_o                    (il_rob_valid),
        .rob_rs1_ready_i                (rob_il_rs1_ready),
        .rob_rs1_value_i                (rob_il_rs1_value),
        .rob_rs2_ready_i                (rob_il_rs2_ready),
        .rob_rs2_value_i                (rob_il_rs2_value),
        .rob_tail_idx_i                 (rob_il_tail_idx),
        .rob_rs1_idx_o                  (il_rob_rs1_idx),
        .rob_rs2_idx_o                  (il_rob_rs2_idx),
        .rob_data_o                     (il_rob_data),

        .cl_resume_i                    (comm_issue_resume),
        .cl_reg0_valid_i                (comm_issue_reg0_valid),
        .cl_reg0_value_i                (comm_issue_reg0_value),
        .cl_reg0_idx_i                  (comm_issue_reg0_idx),
        .cl_reg1_valid_i                (comm_issue_reg1_valid),
        .cl_reg1_value_i                (comm_issue_reg1_value),
        .cl_reg1_idx_i                  (comm_issue_reg1_idx),
        .cl_comm_reg_valid_i            (comm_issue_commreg_valid),
        .cl_comm_reg_value_i            (comm_issue_commreg_value),
        .cl_comm_reg_idx_i              (comm_issue_commreg_idx)
    );

    // --------------------------------------------
    // REGISTER STATUS REGISTERS AND REGISTER FILES
    // --------------------------------------------

    // Integer register status register
    // --------------------------------
    int_regstat #(.REG_NUM(XREG_NUM)) u_int_regstat
    (
        .clk_i                  (clk_i                      ),
        .rst_n_i                (rst_n_i                    ),
        .issue_valid_i          (il_int_regstat_valid       ),
        .issue_rd_idx_i         (il_int_regstat_rd_idx      ),
        .issue_rob_idx_i        (il_int_regstat_rob_idx     ),
        .issue_rs1_idx_i        (il_int_regstat_rs1_idx     ),
        .issue_rs2_idx_i        (il_int_regstat_rs2_idx     ),
        .issue_rs1_busy_o       (int_regstat_il_rs1_busy    ),
        .issue_rs1_rob_idx_o    (int_regstat_il_rs1_rob_idx ),
        .issue_rs2_busy_o       (int_regstat_il_rs2_busy    ),
        .issue_rs2_rob_idx_o    (int_regstat_il_rs2_rob_idx ),
        .comm_valid_i           (comm_intrs_valid           ),
        .comm_rd_idx_i          (comm_rf_rd_idx             ),
        .comm_head_idx_i        (comm_rs_head_idx           )
    );

    // Integer register file
    // ---------------------
    int_rf u_int_rf 
    (
        .clk_i                  (clk_i              ),
        .rst_n_i                (rst_n_i            ),
        .comm_valid_i           (comm_intrf_valid   ),
        .comm_rd_idx_i          (comm_rf_rd_idx     ),
        .comm_rd_value_i        (comm_rf_rd_value   ),
        .issue_rs1_idx_i        (il_intrf_rs1_idx   ),
        .issue_rs2_idx_i        (il_intrf_rs2_idx   ),
        .issue_rs1_value_o      (intrf_il_rs1_value ),
        .issue_rs2_value_o      (intrf_il_rs2_value )
    );

`ifdef LEN5_FP_EN
    // Floating-point register status register
    // ---------------------------------------

    // FP register status register
    fp_regstat #(.REG_NUM(XREG_NUM)) u_fp_regstat
    (
        .clk_i                  (clk_i                      ),
        .rst_n_i                (rst_n_i                    ),
        .issue_valid_i          (il_fp_regstat_valid        ),
        .issue_ready_o          (fp_regstat_il_ready        ),
        .issue_rd_idx_i         (il_fp_regstat_rd_idx       ),
        .issue_rob_idx_i        (il_fp_regstat_rob_idx      ),
        .issue_rs1_idx_i        (il_fp_regstat_rs1_idx      ),
        .issue_rs2_idx_i        (il_fp_regstat_rs2_idx      ),
        .issue_rs1_busy_o       (fp_regstat_il_rs1_busy     ),
        .issue_rs1_rob_idx_o    (fp_regstat_il_rs1_rob_idx  ),
        .issue_rs2_busy_o       (fp_regstat_il_rs2_busy     ),
        .issue_rs2_rob_idx_o    (fp_regstat_il_rs2_rob_idx  ),
        .comm_valid_i           (comm_fprs_valid            ),
        .comm_ready_o           (fp_regstat_comm_ready      ),
        .comm_rd_idx_i          (comm_rf_rd_idx             ),
        .comm_head_idx_i        (comm_rs_head_idx           )
    );

    // Floating-point register file
    // ----------------------------
    fp_rf u_fp_rf 
    (
        .clk_i                  (clk_i             ),
        .rst_n_i                (rst_n_i           ),
        .comm_valid_i           (comm_fprf_valid   ),
        .comm_ready_o           (fprf_comm_ready   ),
        .comm_rd_idx_i          (comm_rf_rd_idx    ),
        .comm_rd_value_i        (comm_rf_rd_value  ),
        .issue_rs1_idx_i        (il_fprf_rs1_idx   ),
        .issue_rs2_idx_i        (il_fprf_rs2_idx   ),
        .issue_rs1_value_o      (fprf_il_rs1_value ),
        .issue_rs2_value_o      (fprf_il_rs2_value )
    );
`endif /* LEN5_FP_EN */

    // ---------------
    // EXECUTION STAGE
    // ---------------
    
    // Execution units
    // ---------------
    exec_stage u_exec_stage 
    (
        .clk_i                      (clk_i                  ),
        .rst_n_i                    (rst_n_i                ),
        .flush_i                    (mis_flush              ),

        .fetch_res_pc_o             (fetch_res_pc_o         ),
        .fetch_res_target_o         (fetch_res_target_o     ),
        .fetch_res_taken_o          (fetch_res_taken_o      ),
        .fetch_res_valid_o          (fetch_res_valid_o      ),
        .fetch_res_mispredict_o     (fetch_res_mispredict_o ),

        .issue_valid_i              (il_ex_valid            ),
        .issue_ready_o              (ex_issue_ready         ),
        .issue_eu_ctl_i             (issue_ex_eu_ctl        ),
        .issue_rs1_ready_i          (issue_ex_rs1_ready     ),
        .issue_rs1_idx_i            (issue_ex_rs1_idx       ),
        .issue_rs1_value_i          (issue_ex_rs1_value     ),
        .issue_rs2_ready_i          (issue_ex_rs2_ready     ),
        .issue_rs2_idx_i            (issue_ex_rs2_idx       ),
        .issue_rs2_value_i          (issue_ex_rs2_value     ),
        .issue_imm_value_i          (issue_ex_imm_value     ),
        .issue_rob_idx_i            (issue_ex_rob_idx       ),
        .issue_curr_pc_i            (issue_ex_curr_pc       ),
        .issue_pred_target_i        (issue_ex_pred_target   ),
        .issue_pred_taken_i         (issue_ex_pred_taken    ),

        .cdb_ready_i                (cdb_ex_ready           ),
        .cdb_valid_i                (cdb_others_valid       ), 
        .cdb_valid_o                (ex_cdb_valid           ),
        .cdb_data_i                 (cdb_others_data        ),
        .cdb_data_o                 (ex_cdb_data            ),

        .cl_sb_pop_store_i          (cl_sb_pop_store        ),
        .cl_sb_sb_head_completed_o  (sb_comm_store_head_completed),
        .cl_sb_sb_head_rob_idx_o    (sb_comm_store_head_rob_idx),

        .vm_mode_i                  (csr_ex_vm_mode         ),
    `ifdef LEN5_FP_EN
        .csr_frm_i                  (csr_ex_frm             ),
    `endif /* LEN5_FP_EN */

        .mem_valid_i                (mem_valid_i            ),
        .mem_ready_i                (mem_ready_i            ),
        .mem_valid_o                (mem_valid_o            ),
        .mem_ready_o                (mem_ready_o            ),
        .mem_req_o                  (mem_req_o              ),
        .mem_ans_i                  (mem_ans_i              )
    );

    // Common Data Bus (CDB)
    // ---------------------
    cdb u_cdb
    (
        .clk_i                  (clk_i                  ),
        .rst_n_i                (rst_n_i                ),
        .flush_i                (mis_flush              ),
        .max_prio_valid_i       (ex_cdb_valid[0]        ),
        .max_prio_ready_o       (cdb_ex_ready[0]        ),
        .max_prio_data_i        (ex_cdb_data[0]         ),
        .rs_valid_i             (ex_cdb_valid[1:EU_N-1] ), 
        .rs_ready_o             (cdb_ex_ready[1:EU_N-1] ),
        .rs_data_i              (ex_cdb_data[1:EU_N-1]  ),
        .rob_ready_i            (rob_cdb_ready          ),
        .valid_o                (cdb_others_valid       ),
        .data_o                 (cdb_others_data        )
    );

    // Reorder Buffer (ROB)
    // --------------------
    rob #(
        .DEPTH (ROB_DEPTH   )
    ) u_rob(
    	.clk_i               (clk_i               ),
        .rst_n_i             (rst_n_i             ),
        .flush_i             (mis_flush           ),
        .issue_valid_i       (il_rob_valid        ),
        .issue_ready_o       (rob_il_ready        ),
        .issue_data_i        (il_rob_data         ),
        .issue_tail_idx_o    (rob_il_tail_idx     ),
        .issue_rs1_rob_idx_i (il_rob_rs1_idx      ),
        .issue_rs1_ready_o   (rob_il_rs1_ready    ),
        .issue_rs1_value_o   (rob_il_rs1_value    ),
        .issue_rs2_rob_idx_i (il_rob_rs2_idx      ),
        .issue_rs2_ready_o   (rob_il_rs2_ready    ),
        .issue_rs2_value_o   (rob_il_rs2_value    ),
        .comm_valid_o        (rob_comm_valid      ),
        .comm_ready_i        (comm_rob_ready      ),
        .comm_data_o         (rob_comm_head_entry ),
        .comm_head_idx_o     (rob_comm_head_idx   ),
        .cdb_valid_i         (cdb_others_valid    ),
        .cdb_data_i          (cdb_others_data     )
    );

    // ------------
    // COMMIT STAGE
    // ------------

    // Commit logic
    // ------------
    commit_stage u_commit_stage
    (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .mis_flush_o            (mis_flush),
        .fe_bpu_flush_o         (fetch_bpu_flush_o),
        .fe_res_valid_o         (fetch_res_valid_o),
        .fe_res_o               (fetch_res_o),
        .fe_except_raised_o     (fetch_except_raised_o),
        .fe_except_pc_o         (fetch_except_pc_o),
        .il_resume_o            (comm_issue_resume),
        .il_reg0_valid_o        (comm_issue_reg0_valid),
        .il_reg0_value_o        (comm_issue_reg0_value),
        .il_reg0_idx_o          (comm_issue_reg0_idx),
        .il_reg1_valid_o        (comm_issue_reg1_valid),
        .il_reg1_value_o        (comm_issue_reg1_value),
        .il_reg1_idx_o          (comm_issue_reg1_idx),
        .il_comm_reg_valid_o    (comm_issue_commreg_valid),
        .il_comm_reg_value_o    (comm_issue_commreg_value),
        .il_comm_reg_idx_o      (comm_issue_commreg_idx),
        .rob_valid_i            (rob_comm_valid),
        .rob_ready_o            (comm_rob_ready), 
        .rob_head_entry_i       (rob_comm_head_entry),
        .rob_head_idx_i         (rob_comm_head_idx),
        .sb_head_completed_i    (sb_comm_store_head_completed),
        .sb_head_rob_idx_i      (sb_comm_store_head_rob_idx),
        .sb_pop_store_o         (comm_sb_pop_store),
        .int_rs_valid_o         (comm_intrs_valid),
        .int_rf_valid_o         (comm_intrf_valid),
    `ifdef LEN5_FP_EN
        .fp_rs_valid_o          (comm_fprs_valid),
        .fp_rf_valid_o          (comm_fprf_valid),
    `endif /* LEN5_FP_EN */
        .rs_head_idx_o          (comm_rs_head_idx),
        .rd_idx_o               (comm_rf_rd_idx),
        .rd_value_o             (comm_rf_rd_value),
        .csr_valid_o            (comm_csr_valid),
        .csr_ready_i            (csr_comm_ready),
        .csr_data_i             (csr_comm_data),
        .csr_acc_exc_i          (csr_comm_acc_exc),
        .csr_instr_type_o       (comm_csr_instr_type),
        .csr_funct3_o           (comm_csr_funct3),
        .csr_addr_o             (comm_csr_addr),
        .csr_rs1_idx_o          (comm_csr_rs1_idx),
        .csr_rs1_value_o        (comm_csr_rs1_value),
        .csr_except_code_o      (comm_csr_except_code),
        .csr_rd_idx_o           (comm_csr_rd_idx)
    );

    // ----
    // CSRS
    // ----

    csrs u_csrs
    (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .valid_i            (comm_csr_valid),
        .ready_o            (csr_comm_ready),
        .instr_type_i       (comm_csr_instr_type),
        .funct3_i           (comm_csr_funct3),
        .addr_i             (comm_csr_addr),
        .rs1_idx_i          (comm_csr_rs1_idx),
        .rs1_value_i        (comm_csr_rs1_value),
        .exc_data_i         (comm_csr_except_code),
        .rd_idx_i           (comm_csr_rd_idx),
        .data_o             (csr_comm_data),
        .acc_exc_o          (csr_comm_acc_exc),
    `ifdef LEN5_FP_EN
        .fpu_frm_o          (csr_ex_frm),
    `endif /* LEN5_FP_EN */
        .vm_mode_o          (csr_ex_vm_mode),
    `ifdef LEN5_PRIVILEGED_EN
        .mstatus_tsr_o      (csr_il_mstatus_tsr),
    `endif /* LEN5_PRIVILEGED_EN */
        .mem_vmem_on_o      (),
        .mem_sum_bit_o      (),
        .mem_mxr_bit_o      (),
        .mem_priv_mode_o    (),
        .mem_priv_mode_ls_o (),
        .mem_base_asid_o    (),
        .mem_csr_root_ppn_o ()
    );

endmodule