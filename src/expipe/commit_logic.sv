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
// File: commit_stage.sv
// Author: Michele Caon 
// Date: 20/11/2019

// THIS FILE IS ONYL A TEMPLATE, THE COMMIT LOGIC IS NOT IMPLEMENTED YET, SINCE IT REQUIRES ALL THE PROCESSOR PARTS TO BE FUNCTIONAL

// LEN5 compilation switches
`include "len5_config.svh"

`include "instr_macros.svh"

import expipe_pkg::*;
import len5_pkg::*;
import csr_pkg::csr_instr_t;
import csr_pkg::CSR_ADDR_LEN;
import csr_pkg::CSR_INSTR;

module commit_stage (
	input   logic                       clk_i,
    input   logic                       rst_n_i,

    // Control to the main control unit
    output  logic                       main_cu_flush_o,
    output  logic                       main_cu_resume_o,

    // Data to frontend
    output  logic                       fe_except_raised_o,
    output  logic [XLEN-1:0]            fe_except_pc_o,

    // Issue logic <--> commit logic
    output  logic                       il_reg0_valid_o,
    output  logic [XLEN-1:0]            il_reg0_value_o,
    output  logic [ROB_IDX_LEN-1:0]     il_reg0_idx_o,
    output  logic                       il_reg1_valid_o,
    output  logic [XLEN-1:0]            il_reg1_value_o,
    output  logic [ROB_IDX_LEN-1:0]     il_reg1_idx_o,
    output  logic                       il_comm_reg_valid_o,
    output  logic [XLEN-1:0]            il_comm_reg_value_o,
    output  logic [ROB_IDX_LEN-1:0]     il_comm_reg_idx_o,

    // Control to the ROB
    input   logic                       rob_valid_i,
    output  logic                       rob_ready_o, 

    // Data from the ROB
    input   rob_entry_t                 rob_head_entry_i,
    input   logic [ROB_IDX_LEN-1:0]     rob_head_idx_i,

    // Commit logic <--> store buffer
    input   logic                       cl_sb_head_completed_i,
    input   logic [ROB_IDX_LEN-1:0]     cl_sb_head_rob_idx_i,
    output  logic                       cl_pop_store_o,     // pop the head store iunstruction in the store buffer

	// Commit logic <--> register files and status
    // input   logic                       int_rs_ready_i,
    output  logic                       int_rs_valid_o,
    // input   logic                       int_rf_ready_i,
    output  logic                       int_rf_valid_o,
`ifdef LEN5_FP_EN
    // input   logic                       fp_rs_ready_i,
    output  logic                       fp_rs_valid_o,
    // input   logic                       fp_rf_ready_i,
    output  logic                       fp_rf_valid_o,
`endif /* LEN5_FP_EN */

    // Data to the register status registers
    output  logic [ROB_IDX_LEN-1:0]     rs_head_idx_o,

    // Data to the register files
    output  logic [REG_IDX_LEN-1:0]     rd_idx_o,           // the index of the destination register (rd)
    output  logic [XLEN-1:0]            rd_value_o,         // the value to be stored in rd

    // CSRs handshaking
    output  logic                       csr_valid_o,
    input   logic                       csr_ready_i,
    
    // CSRs data
    input   logic [XLEN-1:0]            csr_data_i,
    input   logic                       csr_acc_exc_i,      // CSR illegal instruction or access permission denied
    output  csr_instr_t                 csr_instr_type_o,
    output  logic [FUNCT3_LEN-1:0]      csr_funct3_o,
    output  logic [CSR_ADDR_LEN-1:0]    csr_addr_o,
    output  logic [REG_IDX_LEN-1:0]     csr_rs1_idx_o,
    output  logic [XLEN-1:0]            csr_rs1_value_o,
    output  logic [ROB_EXCEPT_LEN-1:0]  csr_except_data_o,
    output  logic [REG_IDX_LEN-1:0]     csr_rd_idx_o
);

    // INTERNAL SIGNALS
    // ----------------

    // Input register data
    typedef struct packed {
        rob_entry_t             data;
        logic [ROB_IDX_LEN-1:0] rob_idx;
    } inreg_data_t;

    // Commit decoder
    comm_type_t                 cd_comm_type;

    // ROB <--> input register
	logic [OPCODE_LEN -1:0]     instr_opcode;
	logic                       sb_store_committing_t;
    logic                       mispredict;

    // Input register <--> commit CU
    logic                       cu_inreg_valid;
    logic                       inreg_cu_valid;

    // Input registers <--> outputs
    logic                       inreg_buff_full;
    inreg_data_t                inreg_buff_data;

    // Committing instruction register
    logic                       comm_reg_en;
    rob_entry_t                 comm_reg_data;

    // commit CU --> others
    logic                       cu_instr_valid;
    logic                       cu_store_comm;
    logic                       cu_csr_type;

    // ------------------------
    // INPUT ROB ENTRY REGISTER
    // ------------------------
    inreg_data_t    inreg_data_in, inreg_data_out;

    assign  inreg_data_in.data      = rob_head_entry_i;
    assign  inreg_data_in.rob_idx   = rob_head_idx_i;

    // Input spill cell
    spill_cell_ext #(.DATA_T(rob_entry_t)) u_input_reg (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .flush_i        (1'b0),
        .valid_i        (rob_valid_i),
        .ready_i        (cu_inreg_valid),
        .valid_o        (inreg_cu_valid),
        .ready_o        (rob_ready_o),
        .data_i         (inreg_data_in),
        .data_o         (inreg_data_out),
        .buff_full_o    (inreg_buff_full),
        .buff_data_o    (inreg_buff_data)
    );

    // -------------------------------
    // COMMITTING INSTRUCTION REGISTER
    // -------------------------------

    always_ff @( posedge clk_i or negedge rst_n_i ) begin : comm_reg
        if (!rst_n_i)           comm_reg_data   = 'h0;
        else if (comm_reg_en)   comm_reg_data   = inreg_data_out.data;
    end

    // --------------
    // COMMIT DECODER
    // --------------
    commit_decoder u_comm_decoder (
        .instruction_i      (rob_instr_i),
        .except_raised_i    (rob_except_raised_i),
        .comm_type_o        (cd_comm_type)
    );

    // -------------------
    // COMMIT CONTROL UNIT
    // -------------------
    assign instr_opcode         = inreg_data_out.data.instruction.r.opcode;
    assign mispredict           = inreg_data_out.data.res_value[0];
    assign cu_store_comm        = (cl_sb_head_rob_idx_i == inreg_data_out.rob_idx) && cl_sb_head_completed_i;

    commit_cu u_commit_cu (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .comm_type_i        (cd_comm_type),
        .store_comm_i       (cu_store_comm),
        .mispredict_i       (mispredict),
        .comm_reg_en_o      (comm_reg_en),
        .valid_i            (inreg_data_out.data.valid),
        .ready_o            (cu_inreg_valid),
        .instr_i            (inreg_data_out.data.instruction),
        .except_raised_i    (inreg_data_out.data.except_raised),
        .except_code_i      (inreg_data_out.data.except_code),
        .int_rs_valid_o     (int_rs_valid_o),
        .int_rf_valid_o     (int_rf_valid_o),
    `ifdef LEN5_FP_EN
        .fp_rs_valid_o      (fp_rs_valid_o),
        .fp_rf_valid_o      (fp_rf_valid_o),
    `endif /* LEN5_FP_EN */
        .sb_pop_store_o     (cl_pop_store_o),
        .csr_valid_o        (csr_valid_o),
        .csr_type_o         (csr_instr_type_o),
        .flush_o            (main_cu_flush_o),
        .resume_o           (main_cu_resume_o)
    );
    
    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    // Data to the issue logic
    assign  il_reg0_valid_o         = inreg_buff_full;
    assign  il_reg0_value_o         = inreg_buff_data.data.res_value;
    assign  il_reg0_idx_o           = inreg_buff_data.rob_idx;
    assign  il_reg1_valid_o         = inreg_cu_valid;
    assign  il_reg1_value_o         = inreg_data_out.data.res_value;
    assign  il_reg1_idx_o           = inreg_data_out.rob_idx;
    assign  il_comm_reg_valid_o     = cu_inreg_valid;
    assign  il_comm_reg_value_o     = comm_reg_data.res_value;
    assign  il_comm_reg_idx_o       = comm_reg_data.rd_idx;

    // TODO: properly handle flush signal to main CU
    assign  main_cu_flush_o         = 1'b0;

    assign  rs_head_idx_o           = rob_head_idx_i;

    // Data to CSRs
    assign  csr_funct3_o            = comm_reg_data.instruction.i.funct3;
    assign  csr_addr_o              = comm_reg_data.instruction.i.imm11;
    assign  csr_rs1_idx_o           = comm_reg_data.instruction.r.rs1;
    assign  csr_rs1_value_o         = comm_reg_data.res_value;
    assign  csr_except_data_o       = comm_reg_data.except_code;
    assign  csr_rd_idx_o            = comm_reg_data.rd_idx;
    
endmodule
