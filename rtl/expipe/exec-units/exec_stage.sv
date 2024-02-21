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
module exec_stage (
  // Clock, reset, and flush
  input logic clk_i,
  input logic rst_ni,
  input logic mis_flush_i,
  input logic except_flush_i,

  // Fetch stage
  input  logic                   fe_pcgen_ready_i,
  output logic                   fe_bpu_valid_o,
  output logic                   fe_pcgen_valid_o,
  output fetch_pkg::resolution_t fe_res_o,

  // ISSUE STAGE
  input logic [len5_config_pkg::MAX_EU_N-1:0] issue_valid_i,  // valid to each RS
  output logic [len5_config_pkg::MAX_EU_N-1:0] issue_ready_o,  // ready from each RS
  input expipe_pkg::eu_ctl_t issue_eu_ctl_i,  // controls for the associated EU
  input expipe_pkg::op_data_t issue_rs1_i,  // rs1 value, ROB index and availability
  input expipe_pkg::op_data_t issue_rs2_i,  // rs1 value, ROB index and availability
  input  logic     [len5_pkg::XLEN-1:0] issue_imm_value_i,              // the value of the immediate field (for st and branches)
  input expipe_pkg::rob_idx_t issue_rob_idx_i,  // the location of the ROB assigned to the instruction
  input logic [len5_pkg::XLEN-1:0] issue_curr_pc_i,  // the PC of the current issuing instr (branches only)
  input  logic     [len5_pkg::XLEN-1:0] issue_pred_target_i,// predicted target of the current issuing instr (branches only)
  input  logic                issue_pred_taken_i, // predicted taken bit of the current issuing instr (branches only)
  output logic issue_mis_o,

  // COMMON DATA BUS (CDB)
  input logic [len5_config_pkg::MAX_EU_N-1:0] cdb_ready_i,  // from the CDB arbiter
  input logic cdb_valid_i,  // CDB data is valid
  output logic [len5_config_pkg::MAX_EU_N-1:0] cdb_valid_o,  // to the CDB arbiter
  input expipe_pkg::cdb_data_t cdb_data_i,
  output expipe_pkg::cdb_data_t [len5_config_pkg::MAX_EU_N-1:0] cdb_data_o,

  // ROB AND CSRs
  input  logic                 comm_sb_mem_clear_i,  // store is clear to execute
  output expipe_pkg::rob_idx_t comm_sb_mem_idx_o,    // executing store ROB index

  // input logic     [FCSR_FRM_LEN-1:0] csr_frm_i,               // global rounding mode for the FPU

  // MEMORY SYSTEM
  // -------------
  output logic                                                mem_load_valid_o,
  input  logic                                                mem_load_ready_i,
  input  logic                                                mem_load_valid_i,
  output logic                                                mem_load_ready_o,
  output logic                                                mem_load_we_o,
  output logic                   [        len5_pkg::XLEN-1:0] mem_load_addr_o,
  output logic                   [                       7:0] mem_load_be_o,
  output logic                   [len5_pkg::BUFF_IDX_LEN-1:0] mem_load_tag_o,
  input  logic                   [        len5_pkg::XLEN-1:0] mem_load_rdata_i,
  input  logic                   [len5_pkg::BUFF_IDX_LEN-1:0] mem_load_tag_i,
  input  logic                                                mem_load_except_raised_i,
  input  len5_pkg::except_code_t                              mem_load_except_code_i,

  output logic                                                mem_store_valid_o,
  input  logic                                                mem_store_ready_i,
  input  logic                                                mem_store_valid_i,
  output logic                                                mem_store_ready_o,
  output logic                                                mem_store_we_o,
  output logic                   [        len5_pkg::XLEN-1:0] mem_store_addr_o,
  output logic                   [                       7:0] mem_store_be_o,
  output logic                   [        len5_pkg::XLEN-1:0] mem_store_wdata_o,
  output logic                   [len5_pkg::BUFF_IDX_LEN-1:0] mem_store_tag_o,
  input  logic                   [len5_pkg::BUFF_IDX_LEN-1:0] mem_store_tag_i,
  input  logic                                                mem_store_except_raised_i,
  input  len5_pkg::except_code_t                              mem_store_except_code_i
);

  import len5_config_pkg::*;
  import len5_pkg::*;
  import expipe_pkg::*;
  import fetch_pkg::*;
  import memory_pkg::*;

  // ---------------
  // LOAD/STORE UNIT
  // ---------------
  load_store_unit #(
    .LB_DEPTH(LDBUFF_DEPTH),
    .SB_DEPTH(STBUFF_DEPTH)
  ) u_load_store_unit (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .mis_flush_i         (mis_flush_i),
    .except_flush_i      (except_flush_i),
    .issue_lb_valid_i    (issue_valid_i[EU_LOAD_BUFFER]),
    .issue_sb_valid_i    (issue_valid_i[EU_STORE_BUFFER]),
    .issue_lb_ready_o    (issue_ready_o[EU_LOAD_BUFFER]),
    .issue_sb_ready_o    (issue_ready_o[EU_STORE_BUFFER]),
    .issue_type_i        (issue_eu_ctl_i.lsu),
    .issue_rs1_i         (issue_rs1_i),
    .issue_rs2_i         (issue_rs2_i),
    .issue_imm_i         (issue_imm_value_i),
    .issue_dest_rob_idx_i(issue_rob_idx_i),
    .comm_sb_mem_clear_i (comm_sb_mem_clear_i),
    .comm_sb_mem_idx_o   (comm_sb_mem_idx_o),
    .cdb_valid_i         (cdb_valid_i),
    .cdb_lb_ready_i      (cdb_ready_i[EU_LOAD_BUFFER]),
    .cdb_sb_ready_i      (cdb_ready_i[EU_STORE_BUFFER]),
    .cdb_lb_valid_o      (cdb_valid_o[EU_LOAD_BUFFER]),
    .cdb_sb_valid_o      (cdb_valid_o[EU_STORE_BUFFER]),
    .cdb_data_i          (cdb_data_i),
    .cdb_lb_data_o       (cdb_data_o[EU_LOAD_BUFFER]),
    .cdb_sb_data_o       (cdb_data_o[EU_STORE_BUFFER]),

    .mem_load_valid_o        (mem_load_valid_o),
    .mem_load_ready_i        (mem_load_ready_i),
    .mem_load_valid_i        (mem_load_valid_i),
    .mem_load_ready_o        (mem_load_ready_o),
    .mem_load_we_o           (mem_load_we_o),
    .mem_load_be_o           (mem_load_be_o),
    .mem_load_addr_o         (mem_load_addr_o),
    .mem_load_rdata_i        (mem_load_rdata_i),
    .mem_load_tag_o          (mem_load_tag_o),
    .mem_load_tag_i          (mem_load_tag_i),
    .mem_load_except_raised_i(mem_load_except_raised_i),
    .mem_load_except_code_i  (mem_load_except_code_i),

    .mem_store_valid_o        (mem_store_valid_o),
    .mem_store_ready_i        (mem_store_ready_i),
    .mem_store_valid_i        (mem_store_valid_i),
    .mem_store_ready_o        (mem_store_ready_o),
    .mem_store_be_o           (mem_store_be_o),
    .mem_store_we_o           (mem_store_we_o),
    .mem_store_addr_o         (mem_store_addr_o),
    .mem_store_tag_o          (mem_store_tag_o),
    .mem_store_wdata_o        (mem_store_wdata_o),
    .mem_store_tag_i          (mem_store_tag_i),
    .mem_store_except_raised_i(mem_store_except_raised_i),
    .mem_store_except_code_i  (mem_store_except_code_i)
  );

  // -----------
  // BRANCH UNIT
  // -----------
  branch_unit #(
    .RS_DEPTH(BU_RS_DEPTH)
  ) u_branch_unit (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .flush_i             (mis_flush_i),
    .fe_pcgen_ready_i    (fe_pcgen_ready_i),
    .fe_bpu_valid_o      (fe_bpu_valid_o),
    .fe_pcgen_valid_o    (fe_pcgen_valid_o),
    .fe_res_o            (fe_res_o),
    .issue_valid_i       (issue_valid_i[EU_BRANCH_UNIT]),
    .issue_ready_o       (issue_ready_o[EU_BRANCH_UNIT]),
    .issue_branch_type_i (issue_eu_ctl_i.bu),
    .issue_rs1_i         (issue_rs1_i),
    .issue_rs2_i         (issue_rs2_i),
    .issue_imm_value_i   (issue_imm_value_i),
    .issue_dest_rob_idx_i(issue_rob_idx_i),
    .issue_curr_pc_i     (issue_curr_pc_i),
    .issue_pred_target_i (issue_pred_target_i),
    .issue_pred_taken_i  (issue_pred_taken_i),
    .issue_mis_o         (issue_mis_o),
    .cdb_ready_i         (cdb_ready_i[EU_BRANCH_UNIT]),
    .cdb_valid_i         (cdb_valid_i),
    .cdb_valid_o         (cdb_valid_o[EU_BRANCH_UNIT]),
    .cdb_data_i          (cdb_data_i),
    .cdb_data_o          (cdb_data_o[EU_BRANCH_UNIT])
  );

  // ------------------------
  // INTEGER ARITHMETIC UNITS
  // ------------------------

  // Integer ALU
  // -----------
  alu_unit #(
    .EU_CTL_LEN(MAX_EU_CTL_LEN),
    .RS_DEPTH  (ALU_RS_DEPTH)
  ) u_alu_unit (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .flush_i             (mis_flush_i),
    .issue_valid_i       (issue_valid_i[EU_INT_ALU]),
    .issue_ready_o       (issue_ready_o[EU_INT_ALU]),
    .issue_eu_ctl_i      (issue_eu_ctl_i.alu),
    .issue_rs1_i         (issue_rs1_i),
    .issue_rs2_i         (issue_rs2_i),
    .issue_dest_rob_idx_i(issue_rob_idx_i),
    .cdb_ready_i         (cdb_ready_i[EU_INT_ALU]),
    .cdb_valid_i         (cdb_valid_i),
    .cdb_valid_o         (cdb_valid_o[EU_INT_ALU]),
    .cdb_data_i          (cdb_data_i),
    .cdb_data_o          (cdb_data_o[EU_INT_ALU])
  );

  // Integer multiplier and divider
  // ------------------------------
  generate
    if (LEN5_M_EN && !LEN5_D_EN) begin : gen_mult_unit  // TODO: unify flags and units
      mult_unit #(
        .EU_CTL_LEN(MAX_EU_CTL_LEN),
        .RS_DEPTH  (MULT_RS_DEPTH)
      ) u_mult_unit (
        .clk_i               (clk_i),
        .rst_ni              (rst_ni),
        .flush_i             (mis_flush_i),
        .issue_valid_i       (issue_valid_i[EU_INT_MULT]),
        .issue_ready_o       (issue_ready_o[EU_INT_MULT]),
        .issue_eu_ctl_i      (issue_eu_ctl_i.mult),
        .issue_rs1_i         (issue_rs1_i),
        .issue_rs2_i         (issue_rs2_i),
        .issue_dest_rob_idx_i(issue_rob_idx_i),
        .cdb_ready_i         (cdb_ready_i[EU_INT_MULT]),
        .cdb_valid_i         (cdb_valid_i),
        .cdb_valid_o         (cdb_valid_o[EU_INT_MULT]),
        .cdb_data_i          (cdb_data_i),
        .cdb_data_o          (cdb_data_o[EU_INT_MULT])
      );
      assign issue_ready_o[EU_INT_DIV] = 1'b0;
      assign cdb_valid_o[EU_INT_DIV]   = 1'b0;
      assign cdb_data_o[EU_INT_DIV]    = '0;
    end else if (LEN5_D_EN && !LEN5_M_EN) begin : gen_div_unit
      div_unit #(
        .EU_CTL_LEN(MAX_EU_CTL_LEN),
        .RS_DEPTH  (DIV_RS_DEPTH),
        .PIPE_DEPTH(DIV_PIPE_DEPTH)
      ) u_div_unit (
        .clk_i               (clk_i),
        .rst_ni              (rst_ni),
        .flush_i             (mis_flush_i),
        .issue_valid_i       (issue_valid_i[EU_INT_DIV]),
        .issue_ready_o       (issue_ready_o[EU_INT_DIV]),
        .issue_eu_ctl_i      (issue_eu_ctl_i.div),
        .issue_rs1_i         (issue_rs1_i),
        .issue_rs2_i         (issue_rs2_i),
        .issue_dest_rob_idx_i(issue_rob_idx_i),
        .cdb_ready_i         (cdb_ready_i[EU_INT_DIV]),
        .cdb_valid_i         (cdb_valid_i),
        .cdb_valid_o         (cdb_valid_o[EU_INT_DIV]),
        .cdb_data_i          (cdb_data_i),
        .cdb_data_o          (cdb_data_o[EU_INT_DIV])
      );
      assign issue_ready_o[EU_INT_MULT] = 1'b0;
      assign cdb_valid_o[EU_INT_MULT]   = 1'b0;
      assign cdb_data_o[EU_INT_MULT]    = '0;
    end else if (LEN5_D_EN && LEN5_M_EN) begin : gen_mult_div_unit
      mult_unit #(
        .EU_CTL_LEN(MAX_EU_CTL_LEN),
        .RS_DEPTH  (MULT_RS_DEPTH)
      ) u_mult_unit (
        .clk_i               (clk_i),
        .rst_ni              (rst_ni),
        .flush_i             (mis_flush_i),
        .issue_valid_i       (issue_valid_i[EU_INT_MULT]),
        .issue_ready_o       (issue_ready_o[EU_INT_MULT]),
        .issue_eu_ctl_i      (issue_eu_ctl_i.mult),
        .issue_rs1_i         (issue_rs1_i),
        .issue_rs2_i         (issue_rs2_i),
        .issue_dest_rob_idx_i(issue_rob_idx_i),
        .cdb_ready_i         (cdb_ready_i[EU_INT_MULT]),
        .cdb_valid_i         (cdb_valid_i),
        .cdb_valid_o         (cdb_valid_o[EU_INT_MULT]),
        .cdb_data_i          (cdb_data_i),
        .cdb_data_o          (cdb_data_o[EU_INT_MULT])
      );

      div_unit #(
        .EU_CTL_LEN(MAX_EU_CTL_LEN),
        .RS_DEPTH  (DIV_RS_DEPTH),
        .PIPE_DEPTH(DIV_PIPE_DEPTH)
      ) u_div_unit (
        .clk_i               (clk_i),
        .rst_ni              (rst_ni),
        .flush_i             (mis_flush_i),
        .issue_valid_i       (issue_valid_i[EU_INT_DIV]),
        .issue_ready_o       (issue_ready_o[EU_INT_DIV]),
        .issue_eu_ctl_i      (issue_eu_ctl_i.div),
        .issue_rs1_i         (issue_rs1_i),
        .issue_rs2_i         (issue_rs2_i),
        .issue_dest_rob_idx_i(issue_rob_idx_i),
        .cdb_ready_i         (cdb_ready_i[EU_INT_DIV]),
        .cdb_valid_i         (cdb_valid_i),
        .cdb_valid_o         (cdb_valid_o[EU_INT_DIV]),
        .cdb_data_i          (cdb_data_i),
        .cdb_data_o          (cdb_data_o[EU_INT_DIV])
      );
    end else begin : gen_no_mult_unit
      assign issue_ready_o[EU_INT_MULT] = 1'b0;
      assign cdb_valid_o[EU_INT_MULT]   = 1'b0;
      assign cdb_data_o[EU_INT_MULT]    = '0;
      assign issue_ready_o[EU_INT_DIV]  = 1'b0;
      assign cdb_valid_o[EU_INT_DIV]    = 1'b0;
      assign cdb_data_o[EU_INT_DIV]     = '0;
    end
  endgenerate

  // -------------------
  // FLOATING-POINT UNIT
  // -------------------

  // fp_unit #(
  //   .EU_CTL_LEN(FPU_CTL_LEN),
  //   .RS_DEPTH  (FPU_RS_DEPTH)
  // ) u_fpu_unit (
  //   .clk_i              (clk_i),
  //   .rst_ni            (rst_ni),
  //   .flush_i            (mis_flush_i),
  //   .issue_valid_i      (issue_valid_i[EU_FPU]),
  //   .issue_ready_o      (issue_ready_o[EU_FPU]),
  //   .eu_ctl_i           (issue_eu_ctl_i[FPU_CTL_LEN-1:0]),
  //   .rs1_ready_i        (issue_rs1_i.ready),
  //   .rs1_idx_i          (issue_rs1_i.rob_idx),
  //   .rs1_value_i        (issue_rs1_i.value),
  //   .rs2_ready_i        (issue_rs2_i.ready),
  //   .rs2_idx_i          (issue_rs2_i.rob_idx),
  //   .rs2_value_i        (issue_rs2_i.value),
  //   .dest_idx_i         (issue_rob_idx_i),
  //   .cdb_ready_i        (cdb_ready_i[EU_FPU]),
  //   .cdb_valid_i        (cdb_valid_i),
  //   .cdb_valid_o        (cdb_valid_o[EU_FPU]),
  //   .cdb_idx_i          (cdb_data_i.rob_idx),
  //   .cdb_data_i         (cdb_data_i.value),
  //   .cdb_except_raised_i(cdb_data_i.except_raised),
  //   .cdb_data_o         (cdb_data_o[EU_FPU]),
  //   .csr_frm_i          (csr_frm_i)
  // );
endmodule
