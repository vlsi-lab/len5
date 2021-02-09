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
// File: issue_logic.sv
// Author: Michele Caon
// Date: 12/11/2019

`ifndef SYNTHESIS
// Include packages
`include "len5_pkg.sv"
`include "expipe_pkg.sv"
`endif

`include "control_pkg.sv"
`include "0_issue_decoder.sv"

import len5_pkg::XLEN;
import len5_pkg::ILEN;
import len5_pkg::EU_N;
import len5_pkg::I_IMM;
import len5_pkg::S_IMM;
import len5_pkg::B_IMM;
import len5_pkg::U_IMM;
import len5_pkg::J_IMM;
import len5_pkg::REG_IDX_LEN;

import expipe_pkg::*;
import control_pkg::*;

module issue_logic (
    // To the main control 
    output  logic                       main_cu_stall_o,

    // Handshake from/to the issue queue
    input   logic                       iq_valid_i,
    output  logic                       iq_ready_o,

    // Data from the issue queue
    input   logic [XLEN-1:0]            iq_curr_pc_i,           // the PC of the current instruction
    input   logic [ILEN-1:0]            iq_instruction_i,
    input   logic [XLEN-1:0]            iq_pred_target_i,
    input   logic                       iq_pred_taken_i,
    input   logic                       iq_except_raised_i,
    input   except_code_t               iq_except_code_i,

    // Handshake from/to the integer register status register
    input   logic                       int_regstat_ready_i,        // should always be asserted
    output  logic                       int_regstat_valid_o,

    // Data from/to the integer register status register
    input   logic                       int_regstat_rs1_busy_i,     // rs1 value is in the ROB or has to be computed
    input   logic [ROB_IDX_LEN-1:0]     int_regstat_rs1_rob_idx_i,  // the index of the ROB where the result is found
    input   logic                       int_regstat_rs2_busy_i,     // rs1 value is in the ROB or has to be computed
    input   logic [ROB_IDX_LEN-1:0]     int_regstat_rs2_rob_idx_i,  // the index of the ROB where the result is found
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rd_idx_o,       // destination register of the issuing instruction
    output  logic [ROB_IDX_LEN-1:0]     int_regstat_rob_idx_o,      // ROB index where the instruction is being allocated (tail pointer of the ROB)
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rs1_idx_o,      // first source register index
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rs2_idx_o,      // second source register index

    // Handshake from/to the floating point register status register
    input   logic                       fp_regstat_ready_i,
    output  logic                       fp_regstat_valid_o,

    // Data from/to the floating point register status register
    input   logic                       fp_regstat_rs1_busy_i,     // rs1 value is in the ROB or has to be computed
    input   logic [ROB_IDX_LEN-1:0]     fp_regstat_rs1_rob_idx_i,  // the index of the ROB where the result is found
    input   logic                       fp_regstat_rs2_busy_i,     // rs1 value is in the ROB or has to be computed
    input   logic [ROB_IDX_LEN-1:0]     fp_regstat_rs2_rob_idx_i,  // the index of the ROB where the result is found
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rd_idx_o,       // destination register of the issuing instruction
    output  logic [ROB_IDX_LEN-1:0]     fp_regstat_rob_idx_o,      // ROB index where the instruction is being allocated (tail pointer of the ROB)
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rs1_idx_o,      // first source register index
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rs2_idx_o,      // second source register index

    // Data from/to the integer register file
    input   logic [XLEN-1:0]            intrf_rs1_value_i,      // value of the first operand
    input   logic [XLEN-1:0]            intrf_rs2_value_i,      // value of the second operand
    output  logic [REG_IDX_LEN-1:0]     intrf_rs1_idx_o,        // RF address of the first operand 
    output  logic [REG_IDX_LEN-1:0]     intrf_rs2_idx_o,        // RF address of the second operand

    // Data from/to the floating point register file
    input   logic [XLEN-1:0]            fprf_rs1_value_i,       // value of the first operand
    input   logic [XLEN-1:0]            fprf_rs2_value_i,       // value of the second operand
    output  logic [REG_IDX_LEN-1:0]     fprf_rs1_idx_o,         // RF address of the first operand 
    output  logic [REG_IDX_LEN-1:0]     fprf_rs2_idx_o,         // RF address of the second operand

    // Handshake from/to the execution pipeline
    input   logic [0:EU_N-1]            ex_ready_i,             // valid signal from each reservation station
    output  logic [0:EU_N-1]            ex_valid_o,             // ready signal to each reservation station

    // Data to the execution pipeline reservation stations
    output  logic [8-1:0]  ex_eu_ctl_o,            // controls for the associated EU
    output  logic                       ex_rs1_ready_o,         // first operand is ready at issue time (from the RF or the ROB)
    output  logic [ROB_IDX_LEN-1:0]     ex_rs1_idx_o,           // the index of the ROB where the first operand can be found (if not ready
    output  logic [XLEN-1:0]            ex_rs1_value_o,         // the value of the first operand (if ready)
    output  logic                       ex_rs2_ready_o,         // second operand is ready at issue time (from the RF or the ROB)
    output  logic [ROB_IDX_LEN-1:0]     ex_rs2_idx_o,           // the index of the ROB where the first operand can be found (if not ready)
    output  logic [XLEN-1:0]            ex_rs2_value_o,         // the value of the first operand (if ready)
    output  logic [I_IMM-1:0]           ex_imm_value_o,         // the value of the immediate field (for stores and branches)                   
    output  logic [ROB_IDX_LEN-1:0]     ex_rob_idx_o,           // the location of the ROB assigned to the instruction
    output  logic [XLEN-1:0]            ex_pred_pc_o,              // the PC of the current issuing instr (branches only)
    output  logic [XLEN-1:0]            ex_pred_target_o,          // the predicted target of the current issuing instr (branches only)
    output  logic                       ex_pred_taken_o,           // the predicted taken bit of the current issuing instr (branches only)

    // Handshake from/to the ROB
    input   logic                       rob_ready_i,            // the ROB has an empty entry available
    output  logic                       rob_valid_o,            // a new instruction can be issued

    // Data from/to the ROB
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
    output  logic                       rob_res_ready_o         // force the ready-to-commit state in the ROB to handle special instr. 
);

    // DEFINITIONS
    // Instruction data 
    logic [REG_IDX_LEN-1:0]             instr_rs1_idx, instr_rs2_idx, instr_rd_idx;
    logic [I_IMM-1:0]                   instr_imm_i_value;
    logic [S_IMM-1:0]                   instr_imm_s_value;
    logic [B_IMM-1:0]                   instr_imm_b_value;
    logic [U_IMM-1:0]                   instr_imm_u_value;
    logic [J_IMM-1:0]                   instr_imm_j_value;

    logic [ROB_IDX_LEN-1:0]             rob_tail_idx;

    // Handshake control
    logic                               regstat_ready;

    // Operand fetch
    logic [ROB_IDX_LEN-1:0]             rob_rs1_idx, rob_rs2_idx;
    logic                               rs1_ready, rs2_ready;
    logic [XLEN-1:0]                    rs1_value, rs2_value;
    logic [XLEN-1:0]                    imm_value;

    // Instruction issue decoder
    logic                               id_except_raised;
    except_code_t                       id_except_code;
    logic                               id_res_ready;
    logic                               id_stall_possible;
    
    issue_eu_t                          id_assigned_eu;
    logic [8-1:0]          id_eu_ctl;
    logic                               id_fp_rs;
    logic                               id_rs1_req;
    logic                               id_rs2_req;
    logic                               id_imm_req;
    imm_format_t                        id_imm_format; 
    logic                               id_regstat_upd;

    // Exception handling 
    logic                               eh_stall_possible, eh_except_raised;
    except_code_t                       eh_except_code;
    logic [XLEN-1:0]                    eh_except_aux;

    //---------------------------------------\\
    //----- INSTRUCTION INFO EXTRACTION -----\\
    //---------------------------------------\\
    // Source and destination registers
    assign  instr_rs1_idx           = iq_instruction_i[19 -: REG_IDX_LEN];
    assign  instr_rs2_idx           = iq_instruction_i[24 -: REG_IDX_LEN];
    assign  instr_rd_idx            = iq_instruction_i[11 -: REG_IDX_LEN];
    // Immediate values
    assign  instr_imm_i_value       = iq_instruction_i[31 -: I_IMM];
    assign  instr_imm_s_value       = { iq_instruction_i[31 : 25], iq_instruction_i[11:7] };
    assign  instr_imm_b_value       = { iq_instruction_i[31], iq_instruction_i[7], iq_instruction_i[30:25], iq_instruction_i[11:8] };
    assign  instr_imm_u_value       = iq_instruction_i[31 -: U_IMM];
    assign  instr_imm_j_value       = { iq_instruction_i[31], iq_instruction_i[19:12], iq_instruction_i[20], iq_instruction_i[30:21] };

    assign rob_tail_idx             = rob_tail_idx_i;

    //-----------------------------\\
    //----- HANDSHAKE CONTROL -----\\
    //-----------------------------\\

    // Select the corresponfing register status register ready signal
    assign regstat_ready    = (id_fp_rs) ? fp_regstat_ready_i : int_regstat_ready_i;

    always_comb begin: issue_control_logic
        // Default values 
        iq_ready_o      = 1'b0;
        ex_valid_o      = '0;
        rob_valid_o     = 1'b0;

        // The instruction can be issue (i.e. popped from the issue queue) if both the assigned reservation station and the ROB can accept it
        
        if (iq_valid_i && rob_ready_i && regstat_ready) begin // an instr. can be issued
            case(id_assigned_eu)
                // IMPORTANT: check the order of the valid/ready connections to each RS
                EU_LOAD_BUFFER: begin   // 0
                    if (ex_ready_i[0]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                        ex_valid_o [0]  = 1'b1;
                    end
                end
                EU_STORE_BUFFER: begin   // 1
                    if (ex_ready_i[1]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                        ex_valid_o [1]  = 1'b1;
                    end
                end
                EU_BRANCH_UNIT: begin   // 2
                    if (ex_ready_i[2]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                        ex_valid_o [2]  = 1'b1;
                    end
                end
                EU_INT_ALU: begin       // 3
                    if (ex_ready_i[3]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                        ex_valid_o [3]  = 1'b1;
                    end
                end
                EU_INT_MULT: begin   // 4
                    if (ex_ready_i[4]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                        ex_valid_o [4]  = 1'b1;
                    end
                end
                EU_INT_DIV: begin   // 5
                    if (ex_ready_i[5]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                        ex_valid_o [5]  = 1'b1;
                    end
                end
                EU_FPU: begin   // 6
                    if (ex_ready_i[6]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                        ex_valid_o [6]  = 1'b1;
                    end
                end
                EU_NONE: begin          // the instr. is sent directly to the ROB
                    rob_valid_o         = 1'b1;
                    iq_ready_o          = 1'b1;
                end
                default: begin
                    rob_valid_o         = 1'b0;
                    ex_valid_o          = 0;
                    iq_ready_o          = 1'b0;
                end
            endcase
        end
    end

    //----------------------------------\\
    //----- REGISTER STATUS UPDATE -----\\
    //----------------------------------\\
    always_comb begin: regstat_upd_logic
        // default values
        fp_regstat_valid_o      = 1'b0;
        int_regstat_valid_o      = 1'b0;
        
        if (iq_valid_i && id_regstat_upd) begin
            if (id_fp_rs)   fp_regstat_valid_o      = 1'b1;
            else            int_regstat_valid_o     = 1'b1;
        end
    end

    //--------------------------\\
    //----- OPERANDS FETCH -----\\
    //--------------------------\\
    // The issue logic accesses the register status to know if the source operands must be fetch from the RF or from the ROB (and from which entry of it). If the source operands are not ready yet, they will be fetched from the CDB by the reservation station as soon as they are produced by the associated EU.

    // Select the correct integer/floating point register status register
    assign  rob_rs1_idx     = (id_fp_rs) ? fp_regstat_rs1_rob_idx_i : int_regstat_rs1_rob_idx_i;
    assign  rob_rs2_idx     = (id_fp_rs) ? fp_regstat_rs2_rob_idx_i : int_regstat_rs2_rob_idx_i;

    always_comb begin: operand_fetch_logic
        // Default values 
        rs1_ready                   = 1'b0;
        rs2_ready                   = 1'b0;
        rs1_value                   = 0;
        rs2_value                   = 0;

        if (!id_fp_rs) begin
            // INTEGER OPERANDS
            // Fetch rs1
            if (id_rs1_req) begin               // rs1 value is required
                if (int_regstat_rs1_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (rob_rs1_ready_i) begin
                        rs1_ready   = 1'b1;
                        rs1_value   = rob_rs1_value_i;
                    end
                end else begin                  // the operand is available in the register file 
                    rs1_ready           = 1'b1;
                    rs1_value           = intrf_rs1_value_i;
                end
            end
            // Fetch rs2
            if (id_rs2_req) begin               // rs2 value is required
                if (int_regstat_rs2_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (rob_rs2_ready_i) begin
                        rs2_ready   = 1'b1;
                        rs2_value   = rob_rs2_value_i;
                    end
                end else begin                  // the operand is available in the register file 
                    rs2_ready           = 1'b1;
                    rs2_value           = intrf_rs2_value_i;
                end
            end
        end else begin    
            // FLOATING POINT 
            // Fetch rs1
            if (id_rs1_req) begin               // rs1 value is required
                if (fp_regstat_rs1_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (rob_rs1_ready_i) begin
                        rs1_ready   = 1'b1;
                        rs1_value   = rob_rs1_value_i;
                    end
                end else begin                  // the operand is available in the register file 
                    rs1_ready           = 1'b1;
                    rs1_value           = fprf_rs1_value_i;
                end
            end
            // Fetch rs2
            if (id_rs2_req) begin               // rs2 value is required
                if (fp_regstat_rs2_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (rob_rs2_ready_i) begin
                        rs2_ready   = 1'b1;
                        rs2_value   = rob_rs2_value_i;
                    end
                end else begin                  // the operand is available in the register file 
                    rs2_ready           = 1'b1;
                    rs2_value           = fprf_rs2_value_i;
                end
            end
        end
    end
    
    //------------------------------\\
    //----- EXCEPTION HANDLING -----\\
    //------------------------------\\
    always_comb begin: exception_handling_logic
        // If an exception was raised during the fetch stage, keep it and discard exception raised during the issue phase (if any)
        if (iq_except_raised_i) begin
            eh_except_raised            = 1'b1;
            eh_except_code              = iq_except_code_i;
            eh_except_aux               = iq_curr_pc_i;     // auxiliary information about the exception. They will be copied into the 
            eh_stall_possible           = 1'b1;             // the pipeline and issue queue will be flushed anyway
        end else if (id_except_raised) begin
            eh_except_raised            = 1'b1;
            eh_except_code              = id_except_code;
            eh_except_aux               = iq_curr_pc_i;     // the current instruction address is passed
            eh_stall_possible           = 1'b1;
        end else begin
            eh_except_raised            = 1'b0;             // no exception
            eh_except_code              = iq_except_code_i; // whatever, it is ignored since rob_except_raised_o is not asserted
            eh_except_aux               = iq_curr_pc_i;
            eh_stall_possible           = 1'b0;
        end
    end

    //-------------------------------------\\
    //----- ISSUE INSTRUCTION DECODER -----\\
    //-------------------------------------\\
    issue_decoder u_issue_decoder (
         // Instruction from the issue logic
        .issue_instruction_i        (iq_instruction_i),     
    
        // Information to the issue logic
        .issue_except_raised_o      (id_except_raised),     
        .issue_except_code_o        (id_except_code),     
        .issue_res_ready_o          (id_res_ready),     
        .issue_stall_possible_o     (id_stall_possible),     

        .issue_eu_o                 (id_assigned_eu),     
        .issue_eu_ctl_o             (id_eu_ctl), 
        .issue_fp_rs_o              (id_fp_rs),       
        .issue_rs1_req_o            (id_rs1_req),     
        .issue_rs2_req_o            (id_rs2_req),     
        .issue_imm_req_o            (id_imm_req),     
        .issue_imm_format_o         (id_imm_format),  
        .issue_regstat_upd_o        (id_regstat_upd)  
    );

    //------------------------------------------------\\
    //----- EXECUTION PIPELINE OUTPUT EVALUATION -----\\
    //------------------------------------------------\\
    // EU control
    assign  ex_eu_ctl_o                 = id_eu_ctl;

    // Source operands info
    assign  ex_rs1_ready_o              = rs1_ready;
    assign  ex_rs2_ready_o              = rs2_ready;
    assign  ex_rs1_idx_o                = instr_rs1_idx;
    assign  ex_rs2_idx_o                = instr_rs2_idx;

    // Operands value
    always_comb begin: operand_value_logic
        // Default values
        ex_rs1_value_o                  = 0;
        ex_rs2_value_o                  = 0;
        ex_imm_value_o                  = 0;
        case(id_assigned_eu)
            // IMPORTANT: check the order of the valid/ready connections to each RS
            EU_LOAD_BUFFER: begin       // 0
                ex_rs1_value_o          = rs1_value;
                ex_imm_value_o          = instr_imm_i_value;
            end
            EU_STORE_BUFFER: begin      // 1
                ex_rs1_value_o          = rs1_value;
                ex_rs2_value_o          = rs2_value;
                ex_imm_value_o          = instr_imm_s_value;
            end
            EU_BRANCH_UNIT: begin       // 2
                ex_rs1_value_o          = rs1_value;
                ex_rs2_value_o          = rs2_value;
                ex_imm_value_o          = instr_imm_b_value;
            end
            EU_INT_ALU: begin           // 3
                ex_rs1_value_o          = rs1_value;
                if (id_imm_req) begin
                    if (id_imm_format == IMM_SHAMT) begin
                        ex_rs2_value_o  = { {58{1'b0}}, instr_imm_i_value[5:0] };
                    end else begin      // sign extended imm.
                        ex_rs2_value_o  = { {(XLEN-I_IMM){instr_imm_i_value[I_IMM-1]}}, instr_imm_i_value };
                    end
                end else begin
                    ex_rs2_value_o      = rs2_value;
                end
            end
            EU_INT_MULT, EU_INT_DIV, EU_FPU: begin // 4, 5, 6
                ex_rs1_value_o          = rs1_value;
                ex_rs2_value_o          = rs2_value;
            end
            EU_NONE: begin              // the instr. is sent directly to the ROB
                ex_rs1_value_o          = 0;
                ex_rs2_value_o          = 0;
                ex_imm_value_o                  = 0;
            end
            default: begin
                ex_rs1_value_o                  = 0;
                ex_rs2_value_o                  = 0;
                ex_imm_value_o                  = 0;
            end
        endcase
    end

    // Destination ROB entry
    assign  ex_rob_idx_o                = rob_tail_idx;

    // Branch additional info (simply forward from the issue queue)
    assign  ex_pred_pc_o                = iq_curr_pc_i;
    assign  ex_pred_target_o            = iq_pred_target_i;
    assign  ex_pred_taken_o             = iq_pred_taken_i;

    //-----------------------------\\
    //----- OUTPUT EVALUATION -----\\
    //-----------------------------\\
    // To the main control 
    assign  main_cu_stall_o             = id_stall_possible || eh_stall_possible;

    // To the integer register status register
    assign  int_regstat_rs1_idx_o       = instr_rs1_idx;
    assign  int_regstat_rs2_idx_o       = instr_rs2_idx; 
    assign  int_regstat_rd_idx_o        = instr_rd_idx;
    assign  int_regstat_rob_idx_o       = rob_tail_idx;

    // To the floating point register status register
    assign  fp_regstat_rs1_idx_o        = instr_rs1_idx;
    assign  fp_regstat_rs2_idx_o        = instr_rs2_idx; 
    assign  fp_regstat_rd_idx_o         = instr_rd_idx;
    assign  fp_regstat_rob_idx_o        = rob_tail_idx;

    // To the integer register file
    assign  intrf_rs1_idx_o             = instr_rs1_idx;
    assign  intrf_rs2_idx_o             = instr_rs2_idx;

    // To the floating point register file
    assign  fprf_rs1_idx_o              = instr_rs1_idx;
    assign  fprf_rs2_idx_o              = instr_rs2_idx;

    // To the ROB
    assign  rob_rs1_idx_o               = rob_rs1_idx;
    assign  rob_rs2_idx_o               = rob_rs2_idx;
    assign  rob_instr_o                 = iq_instruction_i;
    assign  rob_rd_idx_o                = instr_rd_idx;

    assign  rob_except_raised_o         = eh_except_raised;
    assign  rob_except_code_o           = eh_except_code;
    assign  rob_except_aux_o            = eh_except_aux;

    assign  rob_res_ready_o             = id_res_ready;
    
endmodule
