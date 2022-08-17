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

/* Include UVM macros */
`include "uvm_macros.svh"

/* Import UVM package */
import uvm_pkg::*;

import expipe_pkg::*;
import len5_pkg::*;
import fetch_pkg::resolution_t;
import csr_pkg::csr_instr_t;
import csr_pkg::CSR_ADDR_LEN;
import csr_pkg::CSR_INSTR;

module commit_stage (
	input   logic                       clk_i,
    input   logic                       rst_n_i,

    // Misprediction flush signal
    output  logic                       mis_flush_o, // flush after misprediction

    // Data to frontend
    output  logic                       fe_bpu_flush_o, // flush the Branch Prediction Unit internal structures
    output  logic                       fe_res_valid_o,
    output  resolution_t                fe_res_o,
    output  logic                       fe_except_raised_o,
    output  logic [XLEN-1:0]            fe_except_pc_o,

    // Issue logic <--> commit logic
    output  logic                       il_resume_o, // resume execution after stall
    output  logic                       il_reg0_valid_o,
    output  logic [XLEN-1:0]            il_reg0_value_o,
    output  rob_idx_t                   il_reg0_idx_o,
    output  logic                       il_reg1_valid_o,
    output  logic [XLEN-1:0]            il_reg1_value_o,
    output  rob_idx_t                   il_reg1_idx_o,
    output  logic                       il_comm_reg_valid_o,
    output  logic [XLEN-1:0]            il_comm_reg_value_o,
    output  rob_idx_t                   il_comm_reg_idx_o,

    // Control to the ROB
    input   logic                       rob_valid_i,
    output  logic                       rob_ready_o, 

    // Data from the ROB
    input   rob_entry_t                 rob_head_entry_i,
    input   rob_idx_t                   rob_head_idx_i,

    // Commit logic <--> store buffer
    input   logic                       sb_head_completed_i,
    input   rob_idx_t                   sb_head_rob_idx_i,
    output  logic                       sb_pop_store_o,     // pop the head store iunstruction in the store buffer

	// Commit logic <--> register files and status
    output  logic                       int_rs_valid_o,
    output  logic                       int_rf_valid_o,
`ifdef LEN5_FP_EN
    output  logic                       fp_rs_valid_o,
    output  logic                       fp_rf_valid_o,
`endif /* LEN5_FP_EN */

    // Data to the register status registers
    output  rob_idx_t                   rs_head_idx_o,

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
    output  except_code_t               csr_except_code_o,
    output  logic [REG_IDX_LEN-1:0]     csr_rd_idx_o
);

    // INTERNAL SIGNALS
    // ----------------

    // Input register data
    typedef struct packed {
        rob_entry_t             data;
        rob_idx_t rob_idx;
    } inreg_data_t;

    // Commit decoder
    comm_type_t                 cd_comm_type;

    // ROB <--> input register
	logic [OPCODE_LEN -1:0]     instr_opcode;
	logic                       sb_store_committing_t;

    // Input register <--> commit CU
    logic                       inreg_cu_mispredicted;
    logic                       cu_inreg_ready;
    logic                       inreg_cu_valid;

    // Input registers <--> outputs
    logic                       inreg_buff_full;
    inreg_data_t                inreg_buff_data;

    // Committing instruction register
    logic                       comm_reg_en;
    rob_entry_t                 comm_reg_data;
    logic                       comm_reg_valid;

    // Jump adder and MUX
    logic [XLEN-1:0]            link_addr;
    logic [XLEN-1:0]            rd_value;

    // commit CU <--> others
    logic                       cu_instr_valid;
    logic                       cu_store_comm;
    logic                       cu_csr_type;
    logic                       cu_is_jump;

    // ------------------------
    // INPUT ROB ENTRY REGISTER
    // ------------------------
    inreg_data_t    inreg_data_in, inreg_data_out;

    assign  inreg_data_in.data      = rob_head_entry_i;
    assign  inreg_data_in.rob_idx   = rob_head_idx_i;

    // Input spill cell
    spill_cell_ext #(.DATA_T(inreg_data_t)) u_input_reg (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .flush_i        (1'b0),
        .valid_i        (rob_valid_i),
        .ready_i        (cu_inreg_ready),
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
        if (!rst_n_i) begin
            comm_reg_data   = 'h0;
            comm_reg_valid  = 1'b0;
        end
        else if (comm_reg_en) begin
            comm_reg_data   = inreg_data_out.data;
            comm_reg_valid  = inreg_cu_valid;
        end
    end

    // --------------
    // COMMIT DECODER
    // --------------
    commit_decoder u_comm_decoder (
        .instruction_i      (inreg_data_out.data.instruction),
        .except_raised_i    (inreg_data_out.data.except_raised),
        .comm_type_o        (cd_comm_type)
    );

    // -------------------
    // COMMIT CONTROL UNIT
    // -------------------
    // NOTE: the commit CU is a Moore FSM that receives inputs from the commit
    //       logic input register (spill cell). Since its output will only be
    //       available the next cycle, the instruction is buffered inside the
    //       'comm_reg' register above. 
    assign instr_opcode             = inreg_data_out.data.instruction.r.opcode;
    assign inreg_cu_mispredicted    = inreg_data_out.data.res_aux.jb.mispredicted;
    assign cu_store_comm            = (sb_head_rob_idx_i == inreg_data_out.rob_idx) && sb_head_completed_i;

    commit_cu u_commit_cu (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .comm_type_i        (cd_comm_type),
        .store_comm_i       (cu_store_comm),
        .mispredict_i       (inreg_cu_mispredicted),
        .comm_reg_en_o      (comm_reg_en),
        .is_jump_o          (cu_is_jump),
        .valid_i            (inreg_cu_valid),
        .ready_o            (cu_inreg_ready),
        .instr_i            (inreg_data_out.data.instruction),
        .res_ready_i        (inreg_data_out.data.res_ready),
        .except_raised_i    (inreg_data_out.data.except_raised),
        .except_code_i      (inreg_data_out.data.except_code),
        .int_rs_valid_o     (int_rs_valid_o),
        .int_rf_valid_o     (int_rf_valid_o),
    `ifdef LEN5_FP_EN
        .fp_rs_valid_o      (fp_rs_valid_o),
        .fp_rf_valid_o      (fp_rf_valid_o),
    `endif /* LEN5_FP_EN */
        .sb_pop_store_o     (sb_pop_store_o),
        .csr_valid_o        (csr_valid_o),
        .csr_type_o         (csr_instr_type_o),
        .fe_res_valid_o     (fe_res_valid_o),
        .fe_bpu_flush_o     (fe_bpu_flush_o),
        .mis_flush_o        (mis_flush_o),
        .issue_resume_o     (il_resume_o)
    );

    // Jump commit adder and MUX
    // -------------------------
    assign  link_addr       = comm_reg_data.instr_pc + (ILEN >> 3);
    assign  rd_value        = (cu_is_jump) ? link_addr : comm_reg_data.res_value;
    
    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    // Data to front-end
    assign  fe_res_o.pc         = comm_reg_data.instr_pc;
    assign  fe_res_o.target     = comm_reg_data.res_value;  // computed target address
    assign  fe_res_o.taken      = comm_reg_data.res_aux.jb.taken;
    assign  fe_res_o.mispredict = comm_reg_data.res_aux.jb.mispredicted;
    assign  fe_except_raised_o  = comm_reg_data.except_raised;
    assign  fe_except_pc_o      = 64'hffffffffffffffff; // TODO: add proper exception handling

    // Data to the issue logic
    assign  il_reg0_valid_o         = inreg_buff_full;
    assign  il_reg0_value_o         = inreg_buff_data.data.res_value;
    assign  il_reg0_idx_o           = inreg_buff_data.rob_idx;
    assign  il_reg1_valid_o         = inreg_cu_valid;
    assign  il_reg1_value_o         = inreg_data_out.data.res_value;
    assign  il_reg1_idx_o           = inreg_data_out.rob_idx;
    assign  il_comm_reg_valid_o     = comm_reg_valid;
    assign  il_comm_reg_value_o     = comm_reg_data.res_value;
    assign  il_comm_reg_idx_o       = comm_reg_data.rd_idx;

    assign  rs_head_idx_o           = rob_head_idx_i;

    // Data to the register file(s)
    assign  rd_idx_o                = comm_reg_data.rd_idx;
    assign  rd_value_o              = rd_value;

    // Data to CSRs
    assign  csr_funct3_o            = comm_reg_data.instruction.i.funct3;
    assign  csr_addr_o              = comm_reg_data.instruction.i.imm11;
    assign  csr_rs1_idx_o           = comm_reg_data.instruction.r.rs1;
    assign  csr_rs1_value_o         = comm_reg_data.res_value;
    assign  csr_except_code_o       = comm_reg_data.except_code;
    assign  csr_rd_idx_o            = comm_reg_data.rd_idx;
    
endmodule
