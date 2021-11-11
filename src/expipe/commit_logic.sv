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

// Include LEN5 configuration
`include "len5_config.svh"

`include "instr_macros.svh"

import expipe_pkg::*;
import len5_pkg::*;

module commit_logic (
	input   logic                       clk_i,
    input   logic                       rst_n_i,
    // Control to the ROB
    input   logic                       rob_valid_i,
    output  logic                       rob_ready_o, 
	   

    // Data from the ROB
    input   instr_t                     rob_instr_i,
    input   logic [XLEN-1:0]            rob_pc_i,
    input   logic [REG_IDX_LEN-1:0]     rob_rd_idx_i,
    input   logic [XLEN-1:0]            rob_value_i,
`ifdef LEN5_FP_EN
    input   logic [REG_IDX_LEN-1:0]     fp_rob_rd_idx_i,
    input   logic [XLEN-1:0]            fp_rob_value_i,
`endif /* LEN5_FP_EN */
    input   logic                       rob_except_raised_i,
	input   except_code_t  rob_except_code_i,
    input   logic [ROB_IDX_LEN-1:0]     rob_head_idx_i,

    // Conditions
    input   logic                       sb_store_committing_i, // a store is ready to commit from the store buffer

    output   logic                      rob_except_raised_o,
    //output   logic [ROB_EXCEPT_LEN-1:0]  rob_except_code_o,
	output   except_code_t              rob_except_code_o,
    output   logic                      except_new_o,
    output   logic [XLEN-1:0]           except_new_pc_o,

	// HS from to the register status
    input   logic                       int_rs_ready_i,
    output  logic                       int_rs_valid_o,
`ifdef LEN5_FP_EN
    input   logic                       fp_rs_ready_i,
    output  logic                       fp_rs_valid_o,
`endif /* LEN5_FP_EN */

    // HS from to the register files
    input   logic                       int_rf_ready_i,
    output  logic                       int_rf_valid_o,
`ifdef LEN5_FP_EN
    input   logic                       fp_rf_ready_i,
    output  logic                       fp_rf_valid_o,
`endif /* LEN5_FP_EN */

    // Data to the register files
    output  logic [REG_IDX_LEN-1:0]     rf_rd_idx_o,        // the index of the destination register (rd)
    output  logic [XLEN-1:0]            rf_value_o          // the value to be stored in rd
`ifdef LEN5_FP_EN
   ,output  logic [REG_IDX_LEN-1:0]     fp_rd_idx_o,        // the index of the destination register (rd)
    output  logic [XLEN-1:0]            fp_value_o          // the value to be stored in rd
`endif /* LEN5_FP_EN */
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
	assign except_new_pc_o		= (rob_valid_i & rob_except_raised_i) ? 'd1 : 'd0 ;
	assign except_new_o			= (rob_valid_i) ? rob_except_raised_i : 'b0;
    assign mispredict           = rob_value_i[0];

    // ------------
    // COMMIT LOGIC
    // ------------
    always_comb begin: commit_control_logic
        // Pop the head instruction from the ROB if commit actions have been perf
        rob_ready_o          = cd_comm_possible & eh_no_except /*& !stall*/; // I think it is wrong
    end

    // --------------
    // COMMIT DECODER
    // --------------
    commit_decoder u_comm_decoder (
	.instruction_i              (rob_instr_i),
    //.instruction_i              (rob_instr_t),
    .sb_store_committing_i      (sb_store_committing_i),
	//.sb_store_committing_i      (sb_store_committing_t),    
	.rob_valid_i				(rob_valid_i),
    .no_exception_i				(eh_no_except),
	.int_rs_ready_i				(int_rs_ready_i),
    .int_rf_ready_i				(int_rf_ready_i),
`ifdef LEN5_FP_EN
    .fp_rs_ready_i				(fp_rs_ready_i),
    .fp_rf_ready_i				(fp_rf_ready_i),
`endif /* LEN5_FP_EN */
    .mispredict_i				(mispredict),
    .comm_possible_o            (cd_comm_possible)    
    );

    // ------------------------
    // EXCEPTION HANDLING LOGIC
    // ------------------------
    // The exception handling logic must be insserted here when available
    // assign eh_no_except = (rob_except_raised_t && rob_valid_i)?'b0:'b1/*& !stall*/;
    assign eh_no_except = (rob_except_raised_i && rob_valid_i)?'b0:'b1/*& !stall*/;

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    // Data to the register files
    assign rf_rd_idx_o          = rob_rd_idx_i;
    assign rf_value_o           = rob_value_i;
`ifdef LEN5_FP_EN
    assign fp_rd_idx_o          = fp_rob_rd_idx_i;
    assign fp_value_o           = fp_rob_value_i;
`endif /* LEN5_FP_EN */
	
	assign rob_except_raised_o	= (rob_valid_i) ? rob_except_raised_i : 'b0;
	assign rob_except_code_o	= (rob_valid_i) ? rob_except_code_i   : E_UNKNOWN;

	always_comb begin: comm_decoder
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
            `OPCODE_LD: 
            begin 
                int_rf_valid_o = (cd_comm_possible) ? 1'b1 : 1'b0;
				int_rs_valid_o = (cd_comm_possible) ? 1'b1 : 1'b0;
            end

            default: begin int_rf_valid_o = 1'b0; int_rs_valid_o = 1'b0; end // normally commit without further checks
        endcase
    end

	assign fp_rf_valid_o  = (cd_comm_possible) ? ((instr_opcode == `OPCODE_AUIPC) ? 'b1 : 'b0) : 'b0;// Fix for float
	assign fp_rs_valid_o  = (cd_comm_possible) ? ((instr_opcode == `OPCODE_AUIPC) ? 'b1 : 'b0) : 'b0;// Fix for float
    
endmodule
