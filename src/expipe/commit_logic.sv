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
// File: commit_logic.sv
// Author: Michele Caon 
// Date: 20/11/2019

// THIS FILE IS ONYL A TEMPLATE, THE COMMIT LOGIC IS NOT IMPLEMENTED YET, SINCE IT REQUIRES ALL THE PROCESSOR PARTS TO BE FUNCTIONAL

// LEN5 compilation switches
`include "len5_config.svh"

`include "instr_macros.svh"

import expipe_pkg::*;
import len5_pkg::*;

module commit_logic (
	input   logic                       clk_i,
    input   logic                       rst_n_i,

    // Control to the main control unit
    output  logic                       main_cu_flush_o;

    // Data to frontend
    output  logic                       fe_except_raised_o;
    output  logic [XLEN-1:0]            fe_except_pc_o;

    // Control to the ROB
    input   logic                       rob_valid_i,
    output  logic                       rob_ready_o, 

    // Data from the ROB
    input   instr_t                     rob_instr_i,
    input   logic [XLEN-1:0]            rob_pc_i,
    input   logic [REG_IDX_LEN-1:0]     rob_rd_idx_i,
    input   logic [XLEN-1:0]            rob_value_i,
    input   logic                       rob_except_raised_i,
	input   except_code_t               rob_except_code_i,
    input   logic [ROB_IDX_LEN-1:0]     rob_head_idx_i,

    // Conditions
    input   logic                       sb_store_committing_i, // a store is ready to commit from the store buffer

	// HS from to the register status
    input   logic                       int_rs_ready_i,
    output  logic                       int_rs_valid_o,

    // HS from to the register files
    input   logic                       int_rf_ready_i,
    output  logic                       int_rf_valid_o,
`ifdef LEN5_FP_EN
    input   logic                       fp_rs_ready_i,
    output  logic                       fp_rs_valid_o,
    input   logic                       fp_rf_ready_i,
    output  logic                       fp_rf_valid_o,
`endif /* LEN5_FP_EN */

    // Data to the register status registers
    output  logic [ROB_IDX_LEN-1:0]     rs_head_idx_o,

    // Data to the register files
    output  logic [REG_IDX_LEN-1:0]     rd_idx_o,           // the index of the destination register (rd)
    output  logic [XLEN-1:0]            rd_value_o          // the value to be stored in rd

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
    output  logic [REG_IDX_LEN-1:0]     csr_rd_idx_o,
);

    // DEFINITIONS
    // Commit decoder
    logic                       cd_comm_possible;

    // Exception handling logic
    logic                       eh_no_except;

    // Data to instruction decoder
	logic [OPCODE_LEN -1:0]     instr_opcode;
	logic                       sb_store_committing_t;
    logic                       mispredict;

	assign instr_opcode         = rob_instr_i.r.opcode;
    assign mispredict           = rob_value_i[0];

    // ------------
    // COMMIT LOGIC
    // ------------
    always_comb begin: commit_control_logic
        // Pop the head instruction from the ROB if commit actions have been perf
        rob_ready_o          = cd_comm_possible & eh_no_except; // I think it is wrong
    end

    // --------------
    // COMMIT DECODER
    // --------------
    commit_decoder u_comm_decoder (
	.instruction_i              (rob_instr_i),
    .sb_store_committing_i      (sb_store_committing_i), 
	.rob_valid_i				(rob_valid_i),
    .no_exception_i				(eh_no_except),
	.int_rs_ready_i				(int_rs_ready_i),
    .int_rf_ready_i				(int_rf_ready_i),
`ifdef LEN5_FP_EN
    .fp_rs_ready_i				(fp_rs_ready_i),
    .fp_rf_ready_i				(fp_rf_ready_i),
`endif /* LEN5_FP_EN */
    .csr_ready_i                (csr_ready_i),
    .mispredict_i				(mispredict),
    .comm_possible_o            (cd_comm_possible)    
    );

    // ------------------------
    // EXCEPTION HANDLING LOGIC
    // ------------------------
    // The exception handling logic must be insserted here when available;
    assign eh_no_except = (rob_except_raised_i && rob_valid_i)?'b0:'b1;

    // TODO: properly handle exception feedback to frontend
    assign  fe_except_raised_o        = !eh_no_except;
    assign  fe_except_pc_o            = 'h0;

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    // Data to the register files
    assign rd_idx_o          = rob_rd_idx_i;
    assign rd_value_o           = rob_value_i;
`ifdef LEN5_FP_EN
    assign fp_rd_idx_o          = fp_rob_rd_idx_i;
    assign fp_value_o           = fp_rob_value_i;
`endif /* LEN5_FP_EN */

	always_comb begin: comm_decoder
        // Default values
        int_rf_valid_o  = 1'b0;
        int_rs_valid_o  = 1'b0;
        csr_valid_o     = 1'b0;

        // Integer register instructions
        case(instr_opcode)
	       	`OPCODE_ADD, 
            `OPCODE_ADDI, 
            `OPCODE_ADDIW, 
            `OPCODE_ADDW, 
            `OPCODE_AND, 
            `OPCODE_AND, 
            `OPCODE_OR, 
            `OPCODE_ORI, 
            `OPCODE_SLL, 
            `OPCODE_SLLI, 
            `OPCODE_SLLW, 
            `OPCODE_SLLIW, 
            `OPCODE_SLT, 
            `OPCODE_SLTU, 
            `OPCODE_SLTI, 
            `OPCODE_SLTIU, 
            `OPCODE_SRA, 
            `OPCODE_SRAI, 
            `OPCODE_SRAW, 
            `OPCODE_SRAIW, 
            `OPCODE_SRL, 
            `OPCODE_SRLI, 
            `OPCODE_SRLW, 
            `OPCODE_SRLIW, 
            `OPCODE_SUB, 
            `OPCODE_SUBW, 
            `OPCODE_XOR, 
            `OPCODE_XORI, 
            `OPCODE_LD: begin 
                int_rf_valid_o = (cd_comm_possible) ? 1'b1 : 1'b0;
				int_rs_valid_o = (cd_comm_possible) ? 1'b1 : 1'b0;
            end

        // Floating-point instructions
        `ifdef LEN5_FP_EN
            `OPCODE_FLW,
            `OPCODE_FMADD_S,
            `OPCODE_FMSUB_S,
            `OPCODE_FNMSUB_S,
            `OPCODE_FNMADD_S,
            `OPCODE_FADD_S,
            `OPCODE_FSUB_S,
            `OPCODE_FMUL_S,
            `OPCODE_FDIV_S,
            `OPCODE_FSQRT_S,
            `OPCODE_FSGNJ_S,
            `OPCODE_FSGNJN_S,
            `OPCODE_FSGNJX_S,
            `OPCODE_FMIN_S,
            `OPCODE_FMAX_S,
            `OPCODE_FCVT_W_S,
            `OPCODE_FCVT_WU_S,
            `OPCODE_FMV_X_W,
            `OPCODE_FEQ_S,
            `OPCODE_FLT_S,
            `OPCODE_FLE_S,
            `OPCODE_FCLASS_S,
            `OPCODE_FCVT_S_W,
            `OPCODE_FCVT_S_WU,
            `OPCODE_FMV_W_X,
            `OPCODE_FCVT_L_S,
            `OPCODE_FCVT_LU_S,
            `OPCODE_FCVT_S_L,
            `OPCODE_FCVT_S_LU: begin
                fp_rf_valid_o       = (cd_comm_possible) ? 1'b1 : 1'b0;
                fp_rs_valid_o       = (cd_comm_possible) ? 1'b1 : 1'b0;
                csr_instr_type_o    = FP_INSTR;
                csr_valid_o         = (rob_except_raised_i) ? 1'b1 : 1'b0;
            end
        `endif /* LEN5_FP_EN */

            // CSR instructions
            `OPCODE_CSRRC,
            `OPCODE_CSRRCI,
            `OPCODE_CSRRS,
            `OPCODE_CSRRSI,
            `OPCODE_CSRRW,
            `OPCODE_CSRRWI: begin
                csr_valid_o         = (cd_comm_possible) ? 1'b1 : 1'b0;
                csr_instr_type_o    = CSR_INSTR;
            end

            default:; // commit without writing the register files
        endcase
    end

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    // TODO: properly handle flush signal to main CU
    assign  main_cu_flush_o     = 1'b0;

    assign  rs_head_idx_o       = rob_head_idx_i;
    assign  csr_funct3_o        = rob_instr_i.i.funct3;
    assign  csr_addr_o          = rob_instr_i.i.imm;
    assign  csr_rs1_value_o     = rob_value_i;
    assign  csr_except_data_o   = rob_except_code_i;
    assign  csr_rd_idx_o        = rob_rd_idx_i;
    
endmodule
