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

// LEN5 compilation switches
`include "len5_config.svh"

import len5_pkg::*;
import expipe_pkg::*;

module issue_logic (
    // To the main control 
    output  logic                       cu_stall_o,

    // Handshake from/to the issue queue
    input   logic                       iq_valid_i,
    output  logic                       iq_ready_o,

    // Data from the issue queue
    input   iq_entry_t                  iq_instr_i,

    // Handshake from/to the integer register status register
    // input   logic                       int_regstat_ready_i,        // should always be asserted
    output  logic                       int_regstat_valid_o,

    // Data from/to the integer register status register
    input   logic                       int_regstat_rs1_busy_i,     // rs1 value is in the ROB or has to be computed
    input   rob_idx_t     int_regstat_rs1_rob_idx_i,  // the index of the ROB where the result is found
    input   logic                       int_regstat_rs2_busy_i,     // rs1 value is in the ROB or has to be computed
    input   rob_idx_t     int_regstat_rs2_rob_idx_i,  // the index of the ROB where the result is found
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rd_idx_o,       // destination register of the issuing instruction
    output  rob_idx_t     int_regstat_rob_idx_o,      // ROB index where the instruction is being allocated (tail pointer of the ROB)
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rs1_idx_o,      // first source register index
    output  logic [REG_IDX_LEN-1:0]     int_regstat_rs2_idx_o,      // second source register index

    // Data from/to the integer register file
    input   logic [XLEN-1:0]            intrf_rs1_value_i,      // value of the first operand
    input   logic [XLEN-1:0]            intrf_rs2_value_i,      // value of the second operand
    output  logic [REG_IDX_LEN-1:0]     intrf_rs1_idx_o,        // RF address of the first operand 
    output  logic [REG_IDX_LEN-1:0]     intrf_rs2_idx_o,        // RF address of the second operand

`ifdef LEN5_FP_EN
    // Handshake from/to the floating point register status register
    // input   logic                       fp_regstat_ready_i,
    output  logic                       fp_regstat_valid_o,

    // Data from/to the floating point register status register
    input   logic                       fp_regstat_rs1_busy_i,     // rs1 value is in the ROB or has to be computed
    input   rob_idx_t     fp_regstat_rs1_rob_idx_i,  // the index of the ROB where the result is found
    input   logic                       fp_regstat_rs2_busy_i,     // rs1 value is in the ROB or has to be computed
    input   rob_idx_t     fp_regstat_rs2_rob_idx_i,  // the index of the ROB where the result is found
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rd_idx_o,       // destination register of the issuing instruction
    output  rob_idx_t     fp_regstat_rob_idx_o,      // ROB index where the instruction is being allocated (tail pointer of the ROB)
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rs1_idx_o,      // first source register index
    output  logic [REG_IDX_LEN-1:0]     fp_regstat_rs2_idx_o,      // second source register index

    // Data from/to the floating point register file
    input   logic [XLEN-1:0]            fprf_rs1_value_i,       // value of the first operand
    input   logic [XLEN-1:0]            fprf_rs2_value_i,       // value of the second operand
    output  logic [REG_IDX_LEN-1:0]     fprf_rs1_idx_o,         // RF address of the first operand 
    output  logic [REG_IDX_LEN-1:0]     fprf_rs2_idx_o,         // RF address of the second operand
`endif /* LEN5_FP_EN */

`ifdef LEN5_PRIVILEGED_EN
    // CSR data
    input                                   mstatus_tsr_i,    // the TSR bit from the mstatus CSR
`endif /* LEN5_PRIVILEGED_EN */

    // Handshake from/to the execution pipeline
    input   logic                       ex_ready_i [0:EU_N-1],             // valid signal from each reservation station
    output  logic                       ex_valid_o [0:EU_N-1],             // ready signal to each reservation station

    // Data to the execution pipeline reservation stations
    output  logic [MAX_EU_CTL_LEN-1:0]  ex_eu_ctl_o,            // controls for the associated EU
    output  logic                       ex_rs1_ready_o,         // first operand is ready at issue time (from the RF or the ROB)
    output  rob_idx_t     ex_rs1_idx_o,           // the index of the ROB where the first operand can be found (if not ready)
    output  logic [XLEN-1:0]            ex_rs1_value_o,         // the value of the first operand (if ready)
    output  logic                       ex_rs2_ready_o,         // second operand is ready at issue time (from the RF or the ROB)
    output  rob_idx_t     ex_rs2_idx_o,           // the index of the ROB where the first operand can be found (if not ready)
    output  logic [XLEN-1:0]            ex_rs2_value_o,         // the value of the first operand (if ready)
    output  logic [XLEN-1:0]            ex_imm_value_o,         // the value of the immediate field
    output  rob_idx_t     ex_rob_idx_o,           // the location of the ROB assigned to the instruction
    output  logic [XLEN-1:0]            ex_curr_pc_o,              // the PC of the current issuing instr (branches only)
    output  logic [XLEN-1:0]            ex_pred_target_o,          // the predicted target of the current issuing instr (branches only)
    output  logic                       ex_pred_taken_o,           // the predicted taken bit of the current issuing instr (branches only)

	// Handshake from/to the cdb
	input   logic                       cdb_valid_i,

	// Data from the cdb
	input   logic                       cdb_except_raised_i,
	input   logic [XLEN-1:0]            cdb_value_i,
	input   rob_idx_t		cdb_rob_idx_i,

    // Handshake from/to the ROB
    input   logic                       rob_ready_i,            // the ROB has an empty entry available
    output  logic                       rob_valid_o,            // a new instruction can be issued

    // Data from/to the ROB
    input   logic                       rob_rs1_ready_i,        // the first operand is ready in the ROB
    input   logic [XLEN-1:0]            rob_rs1_value_i,        // the value of the first operand
    input   logic                       rob_rs2_ready_i,        // the second operand is ready in the ROB
    input   logic [XLEN-1:0]            rob_rs2_value_i,        // the value of the second operand
    input   rob_idx_t                   rob_tail_idx_i,         // the entry of the ROB where the instr is being allocated
    
    output  rob_idx_t                   rob_rs1_idx_o,          // ROB entry containing rs1 value
    output  rob_idx_t                   rob_rs2_idx_o,          // ROB entry containing rs2 value
    output  rob_entry_t                 rob_data_o,             // data to the ROB
    output  instr_t                     rob_instr_o,            // to identify the instruction
    output  logic [XLEN-1:0]            rob_pc_o,               // the PC of the current instruction
    output  logic [REG_IDX_LEN-1:0]     rob_rd_idx_o,           // the destination register index (rd)
    output  logic                       rob_except_raised_o,    // an exception has been raised
    output  except_code_t               rob_except_code_o,      // the exception code
    output  logic [XLEN-1:0]            rob_except_aux_o,       // exception auxilliary data (e.g. offending virtual address)
    output  logic                       rob_res_ready_o,        // force the ready-to-commit state in the ROB to handle special instr. 
    output  logic [XLEN-1:0]            rob_res_value_o,        // result to save in the rob (when available, e.g., immediate)

    // Data from the commit logic (for operands fetch)
    input   logic                       cl_reg0_valid_i,
    input   logic [XLEN-1:0]            cl_reg0_value_i,
    input   rob_idx_t                   cl_reg0_idx_i,
    input   logic                       cl_reg1_valid_i,
    input   logic [XLEN-1:0]            cl_reg1_value_i,
    input   rob_idx_t                   cl_reg1_idx_i,
    input   logic                       cl_comm_reg_valid_i,
    input   logic [XLEN-1:0]            cl_comm_reg_value_i,
    input   rob_idx_t                   cl_comm_reg_idx_i
);

    // DEFINITIONS
    // Instruction data 
    logic [REG_IDX_LEN-1:0]             instr_rs1_idx, instr_rs2_idx, instr_rd_idx;
    logic [XLEN-1:0]                    instr_imm_i_value;
    logic [XLEN-1:0]                    instr_imm_s_value;
    logic [XLEN-1:0]                    instr_imm_b_value;
    logic [XLEN-1:0]                    instr_imm_u_value;
    logic [XLEN-1:0]                    instr_imm_j_value;
    logic [XLEN-1:0]                    instr_imm_rs1_value;    // for CSR immediate instr.
    logic [XLEN-1:0]                    imm_value;              // selected immediate

    rob_idx_t             rob_tail_idx;

    // Handshake control
    // logic                               regstat_ready;

    // Operand fetch
    rob_idx_t             rob_rs1_idx, rob_rs2_idx;
    logic                               rs1_ready, rs2_ready;
    logic [XLEN-1:0]                    rs1_value, rs2_value;

    // Instruction issue decoder
    logic                               id_except_raised;
    except_code_t                       id_except_code;
    logic                               id_res_ready;
    logic                               id_stall_possible;
    
    issue_eu_t                          id_assigned_eu;
    logic [MAX_EU_CTL_LEN-1:0]          id_eu_ctl;
`ifdef LEN5_FP_EN
    logic                               id_fp_rs;
`endif /* LEN5_FP_EN */
    logic                               id_rs1_req;
    logic                               id_rs1_is_pc;
    logic                               id_rs2_req;
    logic                               id_rs2_is_imm;
`ifdef LEN5_FP_EN
    logic                               id_rs3_req;
`endif /* LEN5_FP_EN */
    imm_format_t                        id_imm_format; 
    logic                               id_regstat_upd;

    // Exception handling 
    logic                               eh_stall_possible, eh_except_raised;
    except_code_t                       eh_except_code;
    logic [XLEN-1:0]                    eh_except_aux;

    // ---------------------------
    // INSTRUCTION INFO EXTRACTION
    // ---------------------------
    // Source and destination registers
    assign  instr_rs1_idx           = iq_instr_i.instruction.r.rs1;
    assign  instr_rs2_idx           = iq_instr_i.instruction.r.rs2;
    assign  instr_rd_idx            = iq_instr_i.instruction.r.rd;
    // Immediate values
    assign  instr_imm_i_value       = { {52{iq_instr_i.instruction.i.imm11[31]}}, iq_instr_i.instruction.i.imm11 };
    assign  instr_imm_s_value       = { {52{iq_instr_i.instruction.s.imm11[31]}}, iq_instr_i.instruction.s.imm11, iq_instr_i.instruction.s.imm4 };
    assign  instr_imm_b_value       = { {51{iq_instr_i.instruction.b.imm12}},  iq_instr_i.instruction.b.imm12, iq_instr_i.instruction.b.imm11, iq_instr_i.instruction.b.imm10, iq_instr_i.instruction.b.imm4, 1'b0 };
    assign  instr_imm_u_value       = { {32{iq_instr_i.instruction.u.imm31[31]}},  iq_instr_i.instruction.u.imm31, 12'b0 };
    assign  instr_imm_j_value       = { {43{iq_instr_i.instruction.j.imm20}}, iq_instr_i.instruction.j.imm20, iq_instr_i.instruction.j.imm19, iq_instr_i.instruction.j.imm11, iq_instr_i.instruction.j.imm10, 1'b0 };
    assign  instr_imm_rs1_value     = { '0, iq_instr_i.instruction.r.rs1 };

    assign rob_tail_idx             = rob_tail_idx_i;

    // -----------------
    // HANDSHAKE CONTROL
    // -----------------

    // Select the corresponding register status register ready signal
    // `ifdef LEN5_FP_EN
    //     assign regstat_ready    = (id_fp_rs) ? fp_regstat_ready_i : int_regstat_ready_i;
    // `else
    //     assign regstat_ready    = int_regstat_ready_i;
    // `endif /* LEN5_FP_EN */

    always_comb begin: issue_control_logic
        // Default values 
        iq_ready_o      = 1'b0;
        foreach (ex_valid_o[i]) ex_valid_o[i] = 1'b0;
        rob_valid_o     = 1'b0;

        // The instruction can be issue (i.e. popped from the issue queue) if both the assigned reservation station and the ROB can accept it
        
        if (iq_valid_i && rob_ready_i) begin // an instr. can be issued
            case(id_assigned_eu)
                EU_LOAD_BUFFER: begin   // 0
                    ex_valid_o [EU_LOAD_BUFFER]  = 1'b1;
                    if (ex_ready_i[EU_LOAD_BUFFER]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                    end
                end
                EU_STORE_BUFFER: begin   // 1
                    ex_valid_o [EU_STORE_BUFFER]  = 1'b1;
                    if (ex_ready_i[EU_STORE_BUFFER]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                    end
                end
                EU_BRANCH_UNIT: begin   // 2
                    ex_valid_o [EU_BRANCH_UNIT]  = 1'b1;
                    if (ex_ready_i[EU_BRANCH_UNIT]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                    end
                end
                EU_INT_ALU: begin       // 3
                    ex_valid_o [EU_INT_ALU]  = 1'b1;
                    if (ex_ready_i[EU_INT_ALU]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                    end
                end

            `ifdef LEN5_M_EN
                EU_INT_MULT: begin   // 4
                    ex_valid_o [EU_INT_MULT]  = 1'b1;
                    if (ex_ready_i[EU_INT_MULT]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                    end
                end
                EU_INT_DIV: begin   // 5
                    ex_valid_o [EU_INT_DIV]  = 1'b1;
                    if (ex_ready_i[EU_INT_DIV]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                    end
                end
            `endif /* LEN5_M_EN */

            `ifdef LEN5_FP_EN
                EU_FPU: begin   // 6
                    ex_valid_o [EU_FPU] = 1'b1;
                    if (ex_ready_i[EU_FPU]) begin // if the load buffer can accept the instruction
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                    end
                end
            `endif /* LEN5_FP_EN */
                EU_OPERANDS_ONLY: begin // 7
                    ex_valid_o [EU_OPERANDS_ONLY] = 1'b1;
                    if (ex_ready_i[EU_OPERANDS_ONLY]) begin
                        rob_valid_o     = 1'b1;
                        iq_ready_o      = 1'b1;
                    end
                end
                EU_NONE: begin          // the instr. is sent directly to the ROB
                    rob_valid_o         = 1'b1;
                    iq_ready_o          = 1'b1;
                end
                default: begin
                    rob_valid_o         = 1'b0;
                    foreach (ex_valid_o[i]) ex_valid_o[i] = 1'b0;
                    iq_ready_o          = 1'b0;
                end
            endcase
        end
    end

    // ----------------------
    // REGISTER STATUS UPDATE
    // ----------------------
    always_comb begin: regstat_upd_logic
        // default values
    `ifdef LEN5_FP_EN
        fp_regstat_valid_o      = 1'b0;
    `endif /* LEN5_FP_EN */
        int_regstat_valid_o      = 1'b0;
        
        if (iq_valid_i && id_regstat_upd) begin
        `ifdef LEN5_FP_EN
            if (id_fp_rs)   fp_regstat_valid_o      = 1'b1;
            else            int_regstat_valid_o     = 1'b1;
        `else
            int_regstat_valid_o     = 1'b1;
        `endif /* LEN5_FP_EN */
        end
    end

    // --------------
    // OPERANDS FETCH
    // --------------
    // NOTE: if an operand is required, look for it in the following order:
    // 1) special cases (e.g., the first operand is the current PC)
    // 2) CDB
    // 3) ROB
    // 4) Commit stage buffer 0 (spill register)
    // 5) Commit stage buffer 1
    // 6) Commit stage committing instruction buffer
    // 7) Register file(s)

    // Select the correct integer/floating point register status register
    `ifdef LEN5_FP_EN
    assign  rob_rs1_idx     = (id_fp_rs) ? fp_regstat_rs1_rob_idx_i : int_regstat_rs1_rob_idx_i;
    assign  rob_rs2_idx     = (id_fp_rs) ? fp_regstat_rs2_rob_idx_i : int_regstat_rs2_rob_idx_i;
    `else
    assign  rob_rs1_idx     = int_regstat_rs1_rob_idx_i;
    assign  rob_rs2_idx     = int_regstat_rs2_rob_idx_i;
    `endif /* LEN5_FP_EN */

    always_comb begin: operand_fetch_logic
        // Default values 
        rs1_ready                   = 1'b0;
        rs2_ready                   = 1'b0;
        rs1_value                   = '0;
        rs2_value                   = '0;

        /* INTEGER OPERANDS */
        `ifdef LEN5_FP_EN
        if (!id_fp_rs) begin
        `endif /* LEN5_FP_EN */
            
            // Fetch rs1
            if (id_rs1_is_pc) begin
                rs1_ready       = 1'b1;
                rs1_value       = iq_instr_i.curr_pc;
            end else if (id_rs1_req) begin               // rs1 value is required
                if (int_regstat_rs1_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (rob_rs1_ready_i) begin /* the operand is already available in the ROB */
                        rs1_ready   = 1'b1;
                        rs1_value   = rob_rs1_value_i;
                    end else if (cdb_valid_i && cdb_rob_idx_i == rob_rs1_idx && !cdb_except_raised_i) begin /* the operand is being broadcast on the CDB */
                        rs1_ready   = 1'b1;
                        rs1_value   = cdb_value_i;
                    end else if (cl_reg0_valid_i && cl_reg0_idx_i == rob_rs1_idx) begin
                        rs1_ready   = 1'b1;
                        rs1_value   = cl_reg0_value_i;
                    end else if (cl_reg1_valid_i && cl_reg1_idx_i == rob_rs1_idx) begin
                        rs1_ready   = 1'b1;
                        rs1_value   = cl_reg1_value_i;
                    end else if (cl_comm_reg_valid_i && cl_comm_reg_idx_i == rob_rs1_idx) begin
                        rs1_ready   = 1'b1;
                        rs1_value   = cl_comm_reg_value_i;
                    end else begin /* mark as not ready */
                        rs1_ready   = 1'b0;
                        rs1_value   = 0;
                    end
                end else begin                  // the operand is available in the register file 
                    rs1_ready           = 1'b1;
                    rs1_value           = intrf_rs1_value_i;
                end
            end

            // Fetch rs2
            if (id_rs2_is_imm) begin
                rs2_ready       = 1'b1;
                rs2_value       = imm_value; 
            end else if (id_rs2_req) begin               // rs2 value is required
                if (int_regstat_rs2_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (rob_rs2_ready_i) begin /* the operand is already available in the ROB */
                        rs2_ready   = 1'b1;
                        rs2_value   = rob_rs2_value_i;
                    end else if (cdb_valid_i && cdb_rob_idx_i == rob_rs2_idx && !cdb_except_raised_i) begin
                            rs2_ready   = 1'b1;
                            rs2_value   = cdb_value_i;
                    end else if (cl_reg0_valid_i && cl_reg0_idx_i == rob_rs2_idx) begin
                        rs2_ready   = 1'b1;
                        rs2_value   = cl_reg0_value_i;
                    end else if (cl_reg1_valid_i && cl_reg1_idx_i == rob_rs2_idx) begin
                        rs2_ready   = 1'b1;
                        rs2_value   = cl_reg1_value_i;
                    end else if (cl_comm_reg_valid_i && cl_comm_reg_idx_i == rob_rs2_idx) begin
                        rs2_ready   = 1'b1;
                        rs2_value   = cl_comm_reg_value_i;
				    end else begin /* mark as not ready */
                        rs2_ready   = 1'b0;
                        rs2_value   = 0;
                    end
                end else begin                  // the operand is available in the register file 
                    rs2_ready           = 1'b1;
                    rs2_value           = intrf_rs2_value_i;
                end
            end

        /* FLOATING-POINT OPERANDS */
        `ifdef LEN5_FP_EN
        end else begin  
            
            // Fetch rs1
            if (id_rs1_req) begin               // rs1 value is required
                if (fp_regstat_rs1_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (rob_rs1_ready_i) begin /* the operand is already available in the ROB */
                        rs1_ready   = 1'b1;
                        rs1_value   = rob_rs1_value_i;
                    end else if (cdb_valid_i && cdb_rob_idx_i == rob_rs1_idx && !cdb_except_raised_i) begin /* the operand is being broadcast on the CDB */
                        rs1_ready   = 1'b1;
                        rs1_value   = cdb_value_i;
                    end else if (cl_reg0_valid_i && cl_reg0_idx_i == rob_rs1_idx) begin
                        rs1_ready   = 1'b1;
                        rs1_value   = cl_reg0_value_i;
                    end else if (cl_reg1_valid_i && cl_reg1_idx_i == rob_rs1_idx) begin
                        rs1_ready   = 1'b1;
                        rs1_value   = cl_reg1_value_i;
                    end else if (cl_comm_reg_valid_i && cl_comm_reg_idx_i == rob_rs1_idx) begin
                        rs1_ready   = 1'b1;
                        rs1_value   = cl_comm_reg_value_i;
                    end else begin /* mark as not ready */
                        rs1_ready   = 1'b0;
                        rs1_value   = 0;
                    end
                end else begin                  // the operand is available in the register file 
                    rs1_ready           = 1'b1;
                    rs1_value           = fprf_rs1_value_i;
                end
            end

            // Fetch rs2
            if (id_rs2_req) begin               // rs2 value is required
                if (fp_regstat_rs2_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (rob_rs2_ready_i) begin /* the operand is already available in the ROB */
                        rs2_ready   = 1'b1;
                        rs2_value   = rob_rs2_value_i;
                    end else if (cdb_valid_i && cdb_rob_idx_i == rob_rs2_idx && !cdb_except_raised_i) begin /* the operand is being broadcast on the CDB */
                        rs2_ready   = 1'b1;
                        rs2_value   = cdb_value_i;
                    end else if (cl_reg0_valid_i && cl_reg0_idx_i == rob_rs2_idx) begin
                        rs2_ready   = 1'b1;
                        rs2_value   = cl_reg0_value_i;
                    end else if (cl_reg1_valid_i && cl_reg1_idx_i == rob_rs2_idx) begin
                        rs2_ready   = 1'b1;
                        rs2_value   = cl_reg1_value_i;
                    end else if (cl_comm_reg_valid_i && cl_comm_reg_idx_i == rob_rs2_idx) begin
                        rs2_ready   = 1'b1;
                        rs2_value   = cl_comm_reg_value_i;
                    end else begin /* mark as not ready */
                        rs2_ready   = 1'b0;
                        rs2_value   = 0;
                    end
                end else begin                  // the operand is available in the register file 
                    rs2_ready           = 1'b1;
                    rs2_value           = fprf_rs2_value_i;
                end
            end

            // Fetch rs3
            // ADD RS3 TO FP RF AND RS
        end
        `endif /* LEN5_FP_EN */
    end

    // ------------------
    // IMMEDIATE SELECTOR
    // ------------------

    // Immediate mux
    always_comb begin : imm_sel_logic
        case (id_imm_format)
            IMM_TYPE_I:     imm_value   = instr_imm_i_value;
            IMM_TYPE_S:     imm_value   = instr_imm_s_value;
            IMM_TYPE_B:     imm_value   = instr_imm_b_value;
            IMM_TYPE_U:     imm_value   = instr_imm_u_value;    
            IMM_TYPE_J:     imm_value   = instr_imm_j_value;
            IMM_TYPE_RS1:   imm_value   = instr_imm_rs1_value;
            default:        imm_value   = instr_imm_i_value;
        endcase
    end
    
    // ------------------
    // EXCEPTION HANDLING
    // ------------------
    always_comb begin: exception_handling_logic
        // If an exception was raised during the fetch stage, keep it and discard exception raised during the issue phase (if any)
        if (iq_instr_i.except_raised) begin
            eh_except_raised            = 1'b1;
            eh_except_code              = iq_instr_i.except_code;
            eh_except_aux               = iq_instr_i.curr_pc;     // auxiliary information about the exception. They will be copied into the 
            eh_stall_possible           = 1'b1;             // the pipeline and issue queue will be flushed anyway
        end else if (id_except_raised) begin
            eh_except_raised            = 1'b1;
            eh_except_code              = id_except_code;
            eh_except_aux               = iq_instr_i.curr_pc;     // the current instruction address is passed
            eh_stall_possible           = 1'b1;
        end else begin
            eh_except_raised            = 1'b0;             // no exception
            eh_except_code              = iq_instr_i.except_code; // whatever, it is ignored since rob_except_raised_o is not asserted
            eh_except_aux               = iq_instr_i.curr_pc;
            eh_stall_possible           = 1'b0;
        end
    end

    // -------------------------
    // ISSUE INSTRUCTION DECODER
    // -------------------------
    issue_decoder u_issue_decoder (
         // Instruction from the issue logic
        .instruction_i        (iq_instr_i.instruction), 

    `ifdef LEN5_PRIVILEGED_EN
        .mstatus_tsr_i        (mstatus_tsr_i),
    `endif /* LEN5_PRIVILEGED_EN */

        // Information to the issue logic
        .except_raised_o      (id_except_raised),     
        .except_code_o        (id_except_code),     
        .res_ready_o          (id_res_ready),     
        .stall_possible_o     (id_stall_possible),     

        .eu_o                 (id_assigned_eu),     
        .eu_ctl_o             (id_eu_ctl), 
        .fp_rs_o              (id_fp_rs),       
        .rs1_req_o            (id_rs1_req), 
        .rs1_is_pc_o          (id_rs1_is_pc),
        .rs2_req_o            (id_rs2_req),
        .rs2_is_imm_o         (id_rs2_is_imm),
    `ifdef LEN5_FP_EN
        .rs3_req_o            (id_rs3_req),  
    `endif /* LEN5_FP_EN */     
        .imm_format_o         (id_imm_format),  
        .regstat_upd_o        (id_regstat_upd)  
    );

    // ------------------------------------
    // EXECUTION PIPELINE OUTPUT EVALUATION
    // ------------------------------------
    // EU control
    assign  ex_eu_ctl_o                 = id_eu_ctl;

    // Source operands info
    assign  ex_rs1_ready_o              = rs1_ready;
    assign  ex_rs2_ready_o              = rs2_ready;
    assign  ex_rs1_idx_o                = rob_rs1_idx;
    assign  ex_rs2_idx_o                = rob_rs2_idx;

    assign  ex_rs1_value_o              = rs1_value;
    assign  ex_rs2_value_o              = rs2_value;
    assign  ex_imm_value_o              = imm_value;

    // Destination ROB entry
    assign  ex_rob_idx_o                = rob_tail_idx;

    // Branch additional info (simply forward from the issue queue)
    assign  ex_curr_pc_o                = iq_instr_i.curr_pc;
    assign  ex_pred_target_o            = iq_instr_i.pred_target;
    assign  ex_pred_taken_o             = iq_instr_i.pred_taken;

    // -----------------
    // OUTPUT EVALUATION
    // -----------------
    // To the main control 
    assign  cu_stall_o                  = id_stall_possible || eh_stall_possible;

    // To the integer register status register
    assign  int_regstat_rs1_idx_o       = instr_rs1_idx;
    assign  int_regstat_rs2_idx_o       = instr_rs2_idx; 
    assign  int_regstat_rd_idx_o        = instr_rd_idx;
    assign  int_regstat_rob_idx_o       = rob_tail_idx;

    `ifdef LEN5_FP_EN
    // To the floating point register status register
    assign  fp_regstat_rs1_idx_o        = instr_rs1_idx;
    assign  fp_regstat_rs2_idx_o        = instr_rs2_idx; 
    assign  fp_regstat_rd_idx_o         = instr_rd_idx;
    assign  fp_regstat_rob_idx_o        = rob_tail_idx;
    `endif /* LEN5_FP_EN */

    // To the integer register file
    assign  intrf_rs1_idx_o             = instr_rs1_idx;
    assign  intrf_rs2_idx_o             = instr_rs2_idx;

    `ifdef LEN5_FP_EN
    // To the floating point register file
    assign  fprf_rs1_idx_o              = instr_rs1_idx;
    assign  fprf_rs2_idx_o              = instr_rs2_idx;
    `endif /* LEN5_FP_EN */

    // To the ROB
    assign  rob_rs1_idx_o               = rob_rs1_idx;
    assign  rob_rs2_idx_o               = rob_rs2_idx;
    assign  rob_data_o.instruction      = iq_instr_i.instruction;
    assign  rob_data_o.instr_pc         = iq_instr_i.curr_pc;
    assign  rob_data_o.res_ready        = id_res_ready;
    assign  rob_data_o.res_value        = (eh_except_raised) ? eh_except_aux : imm_value;
    assign  rob_data_o.rd_idx           = instr_rd_idx;
    assign  rob_data_o.except_raised    = eh_except_raised;
    assign  rob_data_o.except_code      = eh_except_code;

    // ----------
    // ASSERTIONS
    // ----------

    `ifndef SYNTHESIS
    property p_assigned_eu;
        @(posedge issue_stage.clk_i) disable iff (!issue_stage.rst_n_i)
        iq_valid_i && rob_ready_i |-> ##0
        rob_valid_o
    endproperty
    a_assigned_eu: assert property (p_assigned_eu);
    `endif /* SYNTHESIS */
    
endmodule
