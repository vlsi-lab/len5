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

`include "expipe_pkg.sv"
`include "len5_pkg.sv"
`include "control_pkg.sv"

`include "commit_decoder.sv"
//`include "commit_decoder.sv"

module commit_logic
    import expipe_pkg::*;
    // import len5_pkg::*;
    import len5_pkg::ILEN;
    import len5_pkg::XLEN;
    import len5_pkg::REG_IDX_LEN;
(
    // Control to the ROB
    input   logic                       rob_valid_i,
    output  logic                       rob_ready_o, 
	//input logic stall,   

    // Data from the ROB
    input   logic [ILEN-1:0]            rob_instr_i,
    input   logic [XLEN-1:0]            rob_pc_i,
    input   logic [REG_IDX_LEN-1:0]     rob_rd_idx_i,
    input   logic [XLEN-1:0]            rob_value_i,
	input   logic [REG_IDX_LEN-1:0]     fp_rob_rd_idx_i,
    input   logic [XLEN-1:0]            fp_rob_value_i,
    input   logic                       rob_except_raised_i,
    input   logic [ROB_EXCEPT_LEN-1:0]  rob_except_code_i,
    input   logic [ROB_IDX_LEN-1:0]     rob_head_idx_i,

    // Conditions
    input   logic                       sb_store_committing_i, // a store is ready to commit from the store buffer

    // HS from to the register files
    input   logic                       int_rf_ready_i,
    input   logic                       fp_rf_ready_i,
    output  logic                       int_rf_valid_o,
    output  logic                       fp_rf_valid_o,

    // Data to the register files
    output  logic [REG_IDX_LEN-1:0]     rf_rd_idx_o,        // the index of the destination register (rd)
    output  logic [XLEN-1:0]            rf_value_o,          // the value to be stored in rd
	output  logic [REG_IDX_LEN-1:0]     fp_rd_idx_o,        // the index of the destination register (rd)
    output  logic [XLEN-1:0]            fp_value_o          // the value to be stored in rd
);

    // DEFINITIONS
    // Commit decoder
    logic                       cd_comm_possible;

    // Exception handling logic
    logic                       eh_no_except;

    //------------------------\\
    //----- COMMIT LOGIC -----\\
    //------------------------\\
    always_comb begin: commit_control_logic
        // Pop the head instruction from the ROB if commit actions have been perf
        rob_ready_o          = cd_comm_possible & eh_no_except /*& !stall*/;
    end

    //--------------------------\\
    //----- COMMIT DECODER -----\\
    //--------------------------\\
    commit_decoder u_comm_decoder (
    .instruction_i              (rob_instr_i),
    .sb_store_committing_i      (sb_store_committing_i),
    .comm_possible_o            (cd_comm_possible)    
    );

    //------------------------------------\\
    //----- EXCEPTION HANDLING LOGIC -----\\
    //------------------------------------\\
    // The exception handling logic must be insserted here when available
    assign eh_no_except = cd_comm_possible/*& !stall*/;


    //-----------------------------\\
    //----- OUTPUT EVALUATION -----\\
    //-----------------------------\\
    // Data to the register files
    assign rf_rd_idx_o          = rob_rd_idx_i;
    assign rf_value_o           = rob_value_i;
	assign fp_rd_idx_o          = rob_rd_idx_i;
    assign fp_value_o           = rob_value_i;
    
endmodule
