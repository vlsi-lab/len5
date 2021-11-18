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
// File: issue_stage.sv
// Author: Michele Caon
// Date: 17/11/2021

// LEN5 compilation switches
`include "len5_config.svh"

import len5_pkg::*;
import expipe_pkg::*;

module issue_stage 
(
    // Clock, reset, and flush
    input   logic                       clk_i,
    input   logic                       rst_n_i,
    input   logic                       flush_i,

    // Issue CU control
    output  logic                       main_cu_stall_o,

    // Fetch unit handshaking
    input   logic                       fetch_valid_i,
    output  logic                       fetch_ready_o,

    // Fetch unit data
    input   logic [XLEN-1:0]            fetch_curr_pc_i,
    input   logic [ILEN-1:0]            fetch_instr_i,
    input   logic [XLEN-1:0]            fetch_pred_target_i,
    input   logic                       fetch_pred_taken_i,
    input   logic                       fetch_except_raised_i,
    input   except_code_t               fetch_except_code_i,

    // Integer register status register handshaking
    input   logic                       int_regstat_ready_i,        // should always be asserted
    output  logic                       int_regstat_valid_o,

    // Integer register status register data
    input   logic                       int_regstat_rs1_busy_i,     // rs1 value is in the ROB or has to be computed
    input   logic [ROB_IDX_LEN-1:0]     int_regstat_rs1_rob_idx_i,  // the index of the ROB where the result is found
    input   logic                       int_regstat_rs2_busy_i,     // rs1 value is in the ROB or has to be computed
    input   logic [ROB_IDX_LEN-1:0]     int_regstat_rs2_rob_idx_i,  // the index of the ROB where the result is found
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rd_idx_o,       // destination register of the issuing instruction
    output  logic [ROB_IDX_LEN-1:0]int_regstat_rob_idx_o,//ROB index where the instruction is being allocated(tail pointer of the ROB)
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rs1_idx_o,      // first source register index
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rs2_idx_o,      // second source register index

	// Integer register file data
    input   logic [XLEN-1:0]            intrf_rs1_value_i,      // value of the first operand
    input   logic [XLEN-1:0]            intrf_rs2_value_i,      // value of the second operand
    output  logic [REG_IDX_LEN-1:0]     intrf_rs1_idx_o,        // RF address of the first operand 
    output  logic [REG_IDX_LEN-1:0]     intrf_rs2_idx_o,        // RF address of the second operand

`ifdef LEN5_FP_EN
	// Floating-point register status register hanshaking
    input   logic                       fp_regstat_ready_i,
    output  logic                       fp_regstat_valid_o,

	// Floating-point register status register data
    input   logic                       fp_regstat_rs1_busy_i,     // rs1 value is in the ROB or has to be computed
    input   logic [ROB_IDX_LEN-1:0]     fp_regstat_rs1_rob_idx_i,  // the index of the ROB where the result is found
    input   logic                       fp_regstat_rs2_busy_i,     // rs1 value is in the ROB or has to be computed
    input   logic [ROB_IDX_LEN-1:0]     fp_regstat_rs2_rob_idx_i,  // the index of the ROB where the result is found
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rd_idx_o,       // destination register of the issuing instruction
    output  logic [ROB_IDX_LEN-1:0] fp_regstat_rob_idx_o,//ROB index where the instruction is being allocated(tail pointer of the ROB)
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rs1_idx_o,      // first source register index
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rs2_idx_o,      // second source register index

    // Floating-point register file data
    input   logic [XLEN-1:0]            fprf_rs1_value_i,       // value of the first operand
    input   logic [XLEN-1:0]            fprf_rs2_value_i,       // value of the second operand
    output  logic [REG_IDX_LEN-1:0]     fprf_rs1_idx_o,         // RF address of the first operand 
    output  logic [REG_IDX_LEN-1:0]     fprf_rs2_idx_o,         // RF address of the second operand    
`endif /* LEN5_FP_EN */

	// Execution pipeline handhsaking
    input   logic                       ex_ready_i [0:EU_N-1],  // ready signal from each reservation station
    output  logic                       ex_valid_o [0:EU_N-1],  // valid signal to each reservation station

    // Execution pipeline data
    output  logic [MAX_EU_CTL_LEN-1:0]  ex_eu_ctl_o,            // controls for the associated EU
    output  logic                       ex_rs1_ready_o,         // first operand is ready at issue time (from the RF or the ROB)
    output  logic [ROB_IDX_LEN-1:0]     ex_rs1_idx_o,    // the index of the ROB where the first operand can be found (if not ready
    output  logic [XLEN-1:0]            ex_rs1_value_o,         // the value of the first operand (if ready)
    output  logic                       ex_rs2_ready_o,         // second operand is ready at issue time (from the RF or the ROB)
    output  logic [ROB_IDX_LEN-1:0]     ex_rs2_idx_o,    // the index of the ROB where the first operand can be found (if not ready)
    output  logic [XLEN-1:0]            ex_rs2_value_o,         // the value of the first operand (if ready)
    output  logic [I_IMM-1:0]           ex_imm_value_o, // the value of the immediate field (for st and branches)                   
    output  logic [ROB_IDX_LEN-1:0]     ex_rob_idx_o,           // the location of the ROB assigned to the instruction
    output  logic [XLEN-1:0]            ex_pred_pc_o,              // the PC of the current issuing instr (branches only)
    output  logic [XLEN-1:0]            ex_pred_target_o,  // the predicted target of the current issuing instr (branches only)
    output  logic                       ex_pred_taken_o   // the predicted taken bit of the current issuing instr (branches only)

    // CDB handshaking
	input   logic                       cdb_valid_i,
	output  logic                       cdb_ready_o,

	// CDB data
	input   logic                       cdb_except_raised_i,
	input   logic [XLEN-1:0]            cdb_value_i,
	input   logic [ROB_IDX_LEN-1:0]		cdb_rob_idx_i,

    // ROB handshaking
    input   logic                       rob_ready_i,            // the ROB has an empty entry available
    output  logic                       rob_valid_o,            // a new instruction can be issued

    // ROB data
    input   logic                       rob_rs1_ready_i,        // the first operand is ready in the ROB
    input   logic [XLEN-1:0]            rob_rs1_value_i,        // the value of the first operand
    input   logic                       rob_rs2_ready_i,        // the second operand is ready in the ROB
    input   logic [XLEN-1:0]            rob_rs2_value_i,        // the value of the second operand
    input   logic [ROB_IDX_LEN-1:0]     rob_tail_idx_i,         // the entry of the ROB where the instr is being allocated
    
    output  logic [ROB_IDX_LEN-1:0]     rob_rs1_idx_o,          // ROB entry containing rs1 value
    output  logic [ROB_IDX_LEN-1:0]     rob_rs2_idx_o,          // ROB entry containing rs2 value
    output  logic [ILEN-1:0]            rob_instr_o,            // to identify the instruction
    output  logic [REG_IDX_LEN-1:0]     rob_rd_idx_o,           // the destination register index (rd)
    output  logic                       rob_except_raised_o,    // an exception has been raised
    output  logic [ROB_EXCEPT_LEN-1:0]  rob_except_code_o,      // the exception code
    output  logic [XLEN-1:0]            rob_except_aux_o,       // exception auxilliary data (e.g. offending virtual address)
    output  logic                       rob_res_ready_o,       // force the ready-to-commit state in the ROB to handle special instr. 
    output  logic [XLEN-1:0]            rob_res_value_o
);

    // INTERNAL SIGNALS

    // Issue queue <--> issue logic
    logic               iq_il_valid;
    logic               il_iq_ready;

    // Issue queue <--> issue logic
    logic [XLEN-1:0]    iq_il_curr_pc;
    logic [ILEN-1:0]    iq_il_instr;
    logic [XLEN-1:0]    iq_il_pred_target;
    logic               iq_il_pred_taken;
    logic               iq_il_except_raised;
    except_code_t       iq_il_except_code;

    // -----------
    // ISSUE QUEUE
    // -----------

    issue_queue u_issue_queue
    (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .flush_i                (flush_i),

        // Fetch unit handshaking
        .fetch_valid_i          (fetch_valid_i),
        .fetch_ready_o          (fetch_ready_o),

        // Fetch unit handshaking
        .fetch_curr_pc_i          (fetch_curr_pc_i),
        .fetch_instr_i          (fetch_instr_i),
        .fetch_pred_target_i    (fetch_pred_target_i),
        .fetch_pred_taken_i     (fetch_pred_taken_i),
        .fetch_except_raised_i  (fetch_except_raised_i),
        .fetch_except_code_i    (fetch_except_code_i),

        // Execution pipeline handshaking
        .issue_ready_i          (il_iq_ready),
        .issue_valid_o          (iq_il_valid),

        // Execution pipeline data
        .curr_pc_o              (iq_il_curr_pc),
        .instruction_o          (iq_il_instr),
        .pred_target_o          (iq_il_pred_target),
        .pred_taken_o           (iq_il_pred_taken),
        .except_raised_o        (iq_il_except_raised),
        .except_code_o          (iq_il_except_code)
    );

    // -----------
    // ISSUE LOGIC
    // -----------
    // Contains the instruction decoder

    issue_logic u_issue_logic
    (
        // To the main control 
        .main_cu_stall_o                (main_cu_stall_o),

        // Issue queue handshaking
        .iq_valid_i                     (iq_il_valid),
        .iq_ready_o                     (il_iq_ready),

        // Issue queue data
        .iq_curr_pc_i                   (iq_il_curr_pc),
        .iq_instruction_i               (iq_il_instr),
        .iq_pred_target_i               (iq_il_pred_target),
        .iq_pred_taken_i                (iq_il_pred_taken),
        .iq_except_raised_i             (iq_il_except_raised),
        .iq_except_code_i               (iq_il_except_code),

        // Interger register status register handshaking
        .int_regstat_ready_i            (int_regstat_ready_i),        
        .int_regstat_valid_o            (int_regstat_valid_o),

        // Interger register status register data
        .int_regstat_rs1_busy_i         (int_regstat_rs1_busy_i),     
        .int_regstat_rs1_rob_idx_i      (int_regstat_rs1_rob_idx_i), 
        .int_regstat_rs2_busy_i         (int_regstat_rs2_busy_i),     
        .int_regstat_rs2_rob_idx_i      (int_regstat_rs2_rob_idx_i), 
        .int_regstat_rd_idx_o           (int_regstat_rd_idx_o),       
        .int_regstat_rob_idx_o          (int_regstat_rob_idx_o),   
        .int_regstat_rs1_idx_o          (int_regstat_rs1_idx_o),      
        .int_regstat_rs2_idx_o          (int_regstat_rs2_idx_o),     

    `ifdef LEN5_FP_EN
        // Floating-point register status register handshaking
        .fp_regstat_ready_i             (fp_regstat_ready_i),
        .fp_regstat_valid_o             (fp_regstat_valid_o),

        // Floating-point register status register data
        .fp_regstat_rs1_busy_i          (fp_regstat_rs1_busy_i),    
        .fp_regstat_rs1_rob_idx_i       (fp_regstat_rs1_rob_idx_i),  
        .fp_regstat_rs2_busy_i          (fp_regstat_rs2_busy_i),     
        .fp_regstat_rs2_rob_idx_i       (fp_regstat_rs2_rob_idx_i),  
        .fp_regstat_rd_idx_o            (fp_regstat_rd_idx_o),     
        .fp_regstat_rob_idx_o           (fp_regstat_rob_idx_o),    
        .fp_regstat_rs1_idx_o           (fp_regstat_rs1_idx_o),    
        .fp_regstat_rs2_idx_o           (fp_regstat_rs2_idx_o),    
    `endif /* LEN5_FP_EN */

        // Interger register file handshaking
        .intrf_rs1_value_i              (intrf_rs1_value_i),     
        .intrf_rs2_value_i              (intrf_rs2_value_i),      
        .intrf_rs1_idx_o                (intrf_rs1_idx_o), 
        .intrf_rs2_idx_o                (intrf_rs2_idx_o),       

    `ifdef LEN5_FP_EN
        // Floating-point register file handshaking
        .fprf_rs1_value_i               (fprf_rs1_value_i),       
        .fprf_rs2_value_i               (fprf_rs2_value_i),      
        .fprf_rs1_idx_o                 (fprf_rs1_idx_o),       
        .fprf_rs2_idx_o                 (fprf_rs2_idx_o),     
    `endif /* LEN5_FP_EN */

        // Execution pipeline handshaking
        .ex_ready_i                     (ex_ready_i),
        .ex_valid_o                     (ex_valid_o),            

        // Execution pipeline data
        .ex_eu_ctl_o                    (ex_eu_ctl_o),
        .ex_rs1_ready_o                 (ex_rs1_ready_o),
        .ex_rs1_idx_o                   (ex_rs1_idx_o),
        .ex_rs1_value_o                 (ex_rs1_value_o),
        .ex_rs2_ready_o                 (ex_rs2_ready_o),
        .ex_rs2_idx_o                   (ex_rs2_idx_o),
        .ex_rs2_value_o                 (ex_rs2_value_o),
        .ex_imm_value_o                 (ex_imm_value_o),
        .ex_rob_idx_o                   (ex_rob_idx_o),
        .ex_pred_pc_o                   (ex_pred_pc_o),
        .ex_pred_target_o               (ex_pred_target_o),
        .ex_pred_taken_o                (ex_pred_taken_o),

        // CDB handshaking
        .cdb_valid_i                    (cdb_valid_i),
        .cdb_ready_o                    (cdb_ready_o),

        // CDB data
        .cdb_except_raised_i            (cdb_except_raised_i),
        .cdb_value_i                    (cdb_value_i),
        .cdb_rob_idx_i                  (cdb_rob_idx_i),

        // Handshake from/to the ROB
        .rob_ready_i                    (rob_ready_i),
        .rob_valid_o                    (rob_valid_o),

        // Data from/to the ROB
        .rob_rs1_ready_i                (rob_rs1_ready_i),        
        .rob_rs1_value_i                (rob_rs1_value_i),       
        .rob_rs2_ready_i                (rob_rs2_ready_i),       
        .rob_rs2_value_i                (rob_rs2_value_i),     
        .rob_tail_idx_i                 (rob_tail_idx_i),         
        .rob_rs1_idx_o                  (rob_rs1_idx_o),
        .rob_rs2_idx_o                  (rob_rs2_idx_o),
        .rob_instr_o                    (rob_instr_o),
        .rob_rd_idx_o                   (rob_rd_idx_o),
        .rob_except_raised_o            (rob_except_raised_o),
        .rob_except_code_o              (rob_except_code_o),
        .rob_except_aux_o               (rob_except_aux_o),
        .rob_res_ready_o                (rob_res_ready_o),
        .rob_res_value_o                (rob_res_value_o)
);

endmodule