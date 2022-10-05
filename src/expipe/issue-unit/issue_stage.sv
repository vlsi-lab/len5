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

/* Include UVM macros */
`ifndef SYNTHESIS
`include "uvm_macros.svh"
import uvm_pkg::*;
`endif

import len5_pkg::*;
import expipe_pkg::*;
import csr_pkg::csr_priv_t;

module issue_stage 
(
    // Clock, reset, and flush
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,

    // Fetch unit
    input   logic                   fetch_valid_i,
    output  logic                   fetch_ready_o,
    input   logic [XLEN-1:0]        fetch_curr_pc_i,
    input   logic [ILEN-1:0]        fetch_instr_i,
    input   logic [XLEN-1:0]        fetch_pred_target_i,
    input   logic                   fetch_pred_taken_i,
    input   logic                   fetch_except_raised_i,
    input   except_code_t           fetch_except_code_i,

    // Integer register status register
    output  logic                   int_regstat_valid_o,
    input   logic                   int_regstat_rs1_busy_i,     // rs1 value is in the ROB or has to be computed
    input   rob_idx_t               int_regstat_rs1_rob_idx_i,  // the index of the ROB where the result is found
    input   logic                   int_regstat_rs2_busy_i,     // rs1 value is in the ROB or has to be computed
    input   rob_idx_t               int_regstat_rs2_rob_idx_i,  // the index of the ROB where the result is found
    output  logic [REG_IDX_LEN-1:0] int_regstat_rd_idx_o,       // destination register of the issuing instruction
    output  rob_idx_t               int_regstat_rob_idx_o,//ROB index where the instruction is being allocated(tail pointer of the ROB)
    output  logic [REG_IDX_LEN-1:0] int_regstat_rs1_idx_o,      // first source register index
    output  logic [REG_IDX_LEN-1:0] int_regstat_rs2_idx_o,      // second source register index

	// Integer register file
    input   logic [XLEN-1:0]        intrf_rs1_value_i,      // value of the first operand
    input   logic [XLEN-1:0]        intrf_rs2_value_i,      // value of the second operand
    output  logic [REG_IDX_LEN-1:0] intrf_rs1_idx_o,        // RF address of the first operand 
    output  logic [REG_IDX_LEN-1:0] intrf_rs2_idx_o,        // RF address of the second operand

`ifdef LEN5_FP_EN
	// Floating-point register status register
    output  logic                   fp_regstat_valid_o,
    input   logic                   fp_regstat_rs1_busy_i,     // rs1 value is in the ROB or has to be computed
    input   rob_idx_t               fp_regstat_rs1_rob_idx_i,  // the index of the ROB where the result is found
    input   logic                   fp_regstat_rs2_busy_i,     // rs1 value is in the ROB or has to be computed
    input   rob_idx_t               fp_regstat_rs2_rob_idx_i,  // the index of the ROB where the result is found
    output  logic [REG_IDX_LEN-1:0] fp_regstat_rd_idx_o,       // destination register of the issuing instruction
    output  rob_idx_t               fp_regstat_rob_idx_o,//ROB index where the instruction is being allocated(tail pointer of the ROB)
    output  logic [REG_IDX_LEN-1:0] fp_regstat_rs1_idx_o,      // first source register index
    output  logic [REG_IDX_LEN-1:0] fp_regstat_rs2_idx_o,      // second source register index

    // Floating-point register file data
    input   logic [XLEN-1:0]        fprf_rs1_value_i,       // value of the first operand
    input   logic [XLEN-1:0]        fprf_rs2_value_i,       // value of the second operand
    output  logic [REG_IDX_LEN-1:0] fprf_rs1_idx_o,         // RF address of the first operand 
    output  logic [REG_IDX_LEN-1:0] fprf_rs2_idx_o,         // RF address of the second operand    
`endif /* LEN5_FP_EN */

	// Execution pipeline
    input   logic                   ex_ready_i [0:EU_N-1],  // ready signal from each reservation station
    output  logic                   ex_valid_o [0:EU_N-1],  // valid signal to each reservation station
    output  eu_ctl_t                ex_eu_ctl_o,            // controls for the associated EU
    output  op_data_t               ex_rs1_o,
    output  op_data_t               ex_rs2_o,
    output  logic [XLEN-1:0]        ex_imm_value_o, // the value of the immediate field (for st and branches)                   
    output  rob_idx_t               ex_rob_idx_o,           // the location of the ROB assigned to the instruction
    output  logic [XLEN-1:0]        ex_curr_pc_o,              // the PC of the current issuing instr (branches only)
    output  logic [XLEN-1:0]        ex_pred_target_o,  // the predicted target of the current issuing instr (branches only)
    output  logic                   ex_pred_taken_o,   // the predicted taken bit of the current issuing instr (branches only)

    // Commit stage
    input   logic                   comm_ready_i,       // the ROB has an empty entry available
    output  logic                   comm_valid_o,       // a new instruction can be issued
    input   logic                   comm_resume_i,      // resume after stall
    input   rob_idx_t               comm_tail_idx_i,    // the entry of the ROB allocated for the new instr
    output  rob_entry_t             comm_data_o,        // data to the ROB
    output  logic                   comm_jb_instr_o,    // the issuing instruction is a jump/branch
    output  rob_idx_t               comm_rs1_rob_idx_o,
    input   logic                   comm_rs1_ready_i,
    input   logic [XLEN-1:0]        comm_rs1_value_i,
    output  rob_idx_t               comm_rs2_rob_idx_o,
    input   logic                   comm_rs2_ready_i,
    input   logic [XLEN-1:0]        comm_rs2_value_i,

    // CSRs
    input   csr_priv_t              csr_priv_mode_i     // current privilege mode
);

    // INTERNAL SIGNALS

    // Instruction data 
    logic [REG_IDX_LEN-1:0]             instr_rs1_idx, instr_rs2_idx, instr_rd_idx;
    logic [XLEN-1:0]                    instr_imm_i_value;
    logic [XLEN-1:0]                    instr_imm_s_value;
    logic [XLEN-1:0]                    instr_imm_b_value;
    logic [XLEN-1:0]                    instr_imm_u_value;
    logic [XLEN-1:0]                    instr_imm_j_value;
    logic [XLEN-1:0]                    instr_imm_rs1_value;    // for CSR immediate instr.
    logic [XLEN-1:0]                    imm_value;              // selected immediate

    // Fetch stage <--> issue queue 
    iq_entry_t          new_instr;

    // Issue queue <--> issuing instruction register
    iq_entry_t          iq_data_out;

    // Issuing instruction registers
    logic               cu_ireg_en;
    issue_reg_t         ireg_data_in, ireg_data_out;

    // Issue decoderc <--> issue stage
    issue_type_t        id_cu_issue_type;
    except_code_t       id_except_code;
    logic               id_skip_eu;
    issue_eu_t          id_assigned_eu;
    eu_ctl_t            id_eu_ctl;
    logic               id_rs1_req;
    logic               id_rs1_is_pc;
    logic               id_rs2_req;
    logic               id_rs2_is_imm;
`ifdef LEN5_FP_EN
    logic               id_rs3_req;
`endif /* LEN5_FP_EN */
    imm_format_t        id_imm_format;

    // Issue queue <--> issue logic
    logic               cu_iq_ready;
    logic [XLEN-1:0]    iq_il_curr_pc;
    logic [ILEN-1:0]    iq_il_instr;
    logic [XLEN-1:0]    iq_il_pred_target;
    logic               iq_il_pred_taken;
    logic               iq_cu_except_raised;
    except_code_t       iq_il_except_code;

    // Issue logic <--> CU
    logic               iq_cu_valid;
    logic               cu_il_res_ready;
    logic               cu_il_res_sel_rs1;
    logic               cu_il_sel_fetch_except;
    logic               cu_il_ex_valid;
    logic               il_cu_ex_ready;

    // CU <--> execution stage
    logic               ex_valid[0:EU_N-1];

    // Operand fetch
    rob_idx_t           rs1_rob_idx, rs2_rob_idx;
    logic               rs1_ready, rs2_ready;
    logic [XLEN-1:0]    rs1_value, rs2_value;

    // -------
    // MODULES
    // -------
    //                              /  ISSUE REGISTER  \
    // fetch stage > ISSUE QUEUE > {   ISSUE DECODER    } > execution/commit stage
    //                              \     ISSUE CU     /
    //                               \ OPERANDS FETCH /

    // ISSUE FIFO QUEUE
    // ----------------
    // Assemble new queue entry with the data from the fetch unit
    assign new_instr.curr_pc        = fetch_curr_pc_i;
    assign new_instr.instruction    = fetch_instr_i;
    assign new_instr.pred_target    = fetch_pred_target_i;
    assign new_instr.pred_taken     = fetch_pred_taken_i;
    assign new_instr.except_raised  = fetch_except_raised_i;
    assign new_instr.except_code    = fetch_except_code_i;

    fifo #(
        .DATA_T (iq_entry_t ),
        .DEPTH  (IQ_DEPTH   )
    )
    u_issue_fifo (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .flush_i (flush_i       ),
        .valid_i (fetch_valid_i ),
        .ready_i (cu_iq_ready   ),
        .valid_o (iq_cu_valid   ),
        .ready_o (fetch_ready_o ),
        .data_i  (new_instr     ),
        .data_o  (iq_data_out   )
    );

    assign  iq_cu_except_raised = iq_data_out.except_raised;

    // ISSUE DECODER
    // -------------
    // Main instruction decoder
    issue_decoder u_issue_decoder(
    	.instruction_i (iq_data_out.instruction ),
        .priv_mode_i   (csr_priv_mode_i          ),
        .issue_type_o  (id_cu_issue_type         ),
        .except_code_o (id_except_code           ),
        .skip_eu_o     (id_skip_eu               ),
        .assigned_eu_o (id_assigned_eu           ),
        .eu_ctl_o      (id_eu_ctl                ),
        .rs1_req_o     (id_rs1_req               ),
        .rs1_is_pc_o   (id_rs1_is_pc             ),
        .rs2_req_o     (id_rs2_req               ),
        .rs2_is_imm_o  (id_rs2_is_imm            ),
    `ifdef LEN5_FP_EN
        .rs3_req_o     (id_rs3_req               ),
    `endif /* LEN5_FP_EN */
        .imm_format_o  (id_imm_format            )
    );

    // Instruction fields extraction
    assign  instr_rs1_idx       = iq_data_out.instruction.r.rs1;
    assign  instr_rs2_idx       = iq_data_out.instruction.r.rs2;
    assign  instr_rd_idx        = iq_data_out.instruction.r.rd;
    assign  instr_imm_i_value   = { {52{iq_data_out.instruction.i.imm11[31]}}, iq_data_out.instruction.i.imm11 };
    assign  instr_imm_s_value   = { {52{iq_data_out.instruction.s.imm11[31]}}, iq_data_out.instruction.s.imm11, iq_data_out.instruction.s.imm4 };
    assign  instr_imm_b_value   = { {51{iq_data_out.instruction.b.imm12}},  iq_data_out.instruction.b.imm12, iq_data_out.instruction.b.imm11, iq_data_out.instruction.b.imm10, iq_data_out.instruction.b.imm4, 1'b0 };
    assign  instr_imm_u_value   = { {32{iq_data_out.instruction.u.imm31[31]}},  iq_data_out.instruction.u.imm31, 12'b0 };
    assign  instr_imm_j_value   = { {43{iq_data_out.instruction.j.imm20}}, iq_data_out.instruction.j.imm20, iq_data_out.instruction.j.imm19, iq_data_out.instruction.j.imm11, iq_data_out.instruction.j.imm10, 1'b0 };
    assign  instr_imm_rs1_value = { 54'h0, iq_data_out.instruction.r.rs1 };

    // Immediate MUX
    always_comb begin : imm_mux
        unique case (id_imm_format)
            IMM_TYPE_S:     imm_value   = instr_imm_s_value;
            IMM_TYPE_B:     imm_value   = instr_imm_b_value;
            IMM_TYPE_U:     imm_value   = instr_imm_u_value;    
            IMM_TYPE_J:     imm_value   = instr_imm_j_value;
            IMM_TYPE_RS1:   imm_value   = instr_imm_rs1_value;
            default:        imm_value   = instr_imm_i_value;
        endcase
    end

    // ISSUING INSTRUCTION REGISTER
    // ----------------------------
    // Input data from issue queue and decoder
    assign  ireg_data_in.curr_pc        = iq_data_out.curr_pc;
    assign  ireg_data_in.instr          = iq_data_out.instruction;
    assign  ireg_data_in.skip_eu        = id_skip_eu;
    assign  ireg_data_in.assigned_eu    = id_assigned_eu;
    assign  ireg_data_in.rs1_req        = id_rs1_req;
    assign  ireg_data_in.rs1_idx        = instr_rs1_idx;
    assign  ireg_data_in.rs1_is_pc      = id_rs1_is_pc;
    assign  ireg_data_in.rs2_req        = id_rs2_req;
    assign  ireg_data_in.rs2_idx        = instr_rs2_idx;
    assign  ireg_data_in.rs2_is_imm     = id_rs2_is_imm;
    assign  ireg_data_in.imm_value      = imm_value;
    assign  ireg_data_in.rd_idx         = instr_rd_idx;
    assign  ireg_data_in.eu_ctl         = id_eu_ctl;
    assign  ireg_data_in.pred_taken     = iq_data_out.pred_taken;
    assign  ireg_data_in.pred_target    = iq_data_out.pred_target;
    assign  ireg_data_in.except_raised  = iq_data_out.except_raised | (id_cu_issue_type == ISSUE_TYPE_EXCEPT);
    assign  ireg_data_in.except_code    = (iq_data_out.except_raised) ? iq_data_out.except_code : id_except_code;

    // Issue register
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : issue_reg
        if (!rst_n_i) begin
            ireg_data_out  <= '0;
        end else if (flush_i) begin
            ireg_data_out  <= '0;
        end else if (cu_ireg_en) begin
            ireg_data_out  <= ireg_data_in;
        end
    end

    // ISSUE CU
    // --------
    // Handshaking signals arbiter
    assign  il_cu_ex_ready  = ex_ready_i[id_assigned_eu] | ireg_data_in.skip_eu;

    // CU
    issue_cu u_issue_cu(
    	.clk_i                (clk_i                  ),
        .rst_n_i              (rst_n_i                ),
        .flush_i              (flush_i                ),
        .iq_valid_i           (iq_cu_valid            ),
        .iq_ready_o           (cu_iq_ready            ),
        .iq_except_raised_i   (iq_cu_except_raised    ),
        .issue_type_i         (id_cu_issue_type       ),
        .issue_rs1_ready_i    (rs1_ready              ),
        .issue_reg_en_o       (cu_ireg_en             ),
        .issue_res_ready_o    (cu_il_res_ready        ),
        .issue_res_sel_rs1_o  (cu_il_res_sel_rs1      ),
        .issue_fetch_except_o (cu_il_sel_fetch_except ),
        .ex_ready_i           (il_cu_ex_ready         ),
        .ex_valid_o           (cu_il_ex_valid         ),
        .int_regstat_valid_o  (int_regstat_valid_o    ),
    `ifdef LEN5_FP_EN
        .fp_regstat_valid_o   (fp_regstat_valid_o     ),
    `endif /* LEN5_FP_EN */
        .comm_ready_i         (comm_ready_i           ),
        .comm_valid_o         (comm_valid_o           ),
        .comm_resume_i        (comm_resume_i          ),
        .comm_jb_instr_o      (comm_jb_instr_o        )
    );

    // Execution stage valid encoding
    always_comb begin : ex_valid_enc
        foreach (ex_valid[i])   ex_valid[i] = 1'b0;
        ex_valid[ireg_data_out.assigned_eu] = cu_il_ex_valid;
    end

    // OPERANDS FETCH
    // --------------
    // NOTE: if an operand is required, look for it in the following order:
    // 1) special cases (e.g., the first operand is the current PC)
    // 2) CDB -- most recent
    // 3) ROB
    // 4) Commit stage buffer 0 (spill register)
    // 5) Commit stage buffer 1
    // 6) Commit stage committing instruction buffer
    // 7) Register file(s) -- oldest

    // Select the correct integer/floating point register status register
    `ifdef LEN5_FP_EN
    assign  rs1_rob_idx     = (fp_regstat_valid_o) ? fp_regstat_rs1_rob_idx_i : int_regstat_rs1_rob_idx_i;
    assign  rs2_rob_idx     = (fp_regstat_valid_o) ? fp_regstat_rs2_rob_idx_i : int_regstat_rs2_rob_idx_i;
    `else
    assign  rs1_rob_idx     = int_regstat_rs1_rob_idx_i;
    assign  rs2_rob_idx     = int_regstat_rs2_rob_idx_i;
    `endif /* LEN5_FP_EN */

    always_comb begin: operand_fetch_logic
        // Default values 
        rs1_ready                   = 1'b0;
        rs2_ready                   = 1'b0;
        rs1_value                   = '0;
        rs2_value                   = '0;

        /* INTEGER OPERANDS */
        `ifdef LEN5_FP_EN
        if (id_cu_issue_type != ISSUE_TYPE_FP) begin
        `endif /* LEN5_FP_EN */
            
            // Fetch rs1
            if (ireg_data_out.rs1_is_pc) begin
                rs1_ready       = 1'b1;
                rs1_value       = ireg_data_out.curr_pc;
            end else if (ireg_data_out.rs1_req) begin               // rs1 value is required
                if (int_regstat_rs1_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (comm_rs1_ready_i) begin // forward the operand from commit stage (CDB, ROB, etc.)
                        rs1_ready   = 1'b1;
                        rs1_value   = comm_rs1_value_i;
                    end else begin /* mark as not ready */
                        rs1_ready   = 1'b0;
                        rs1_value   = '0;
                    end
                end else begin                  // the operand is available in the register file 
                    rs1_ready           = 1'b1;
                    rs1_value           = intrf_rs1_value_i;
                end
            end else rs1_ready = ~ireg_data_out.rs1_req;

            // Fetch rs2
            if (ireg_data_out.rs2_is_imm) begin
                rs2_ready       = 1'b1;
                rs2_value       = ireg_data_out.imm_value; 
            end else if (ireg_data_out.rs2_req) begin               // rs2 value is required
                if (int_regstat_rs2_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (comm_rs2_ready_i) begin // forward the operand from commit stage (CDB, ROB, etc.)
                        rs2_ready   = 1'b1;
                        rs2_value   = comm_rs2_value_i;
				    end else begin /* mark as not ready */
                        rs2_ready   = 1'b0;
                        rs2_value   = 0;
                    end
                end else begin                  // the operand is available in the register file 
                    rs2_ready           = 1'b1;
                    rs2_value           = intrf_rs2_value_i;
                end
            end else rs2_ready = ~ireg_data_out.rs2_req;

        /* FLOATING-POINT OPERANDS */
        `ifdef LEN5_FP_EN
        end else begin  
            
            // Fetch rs1
            if (ireg_data_out.rs1_req) begin               // rs1 value is required
                if (fp_regstat_rs1_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (comm_rs1_ready_i) begin // forward the operand from commit stage (CDB, ROB, etc.)
                        rs1_ready   = 1'b1;
                        rs1_value   = comm_rs1_value_i;
                    end else begin /* mark as not ready */
                        rs1_ready   = 1'b0;
                        rs1_value   = 0;
                    end
                end else begin                  // the operand is available in the register file 
                    rs1_ready           = 1'b1;
                    rs1_value           = fprf_rs1_value_i;
                end
            end else rs1_ready = ~ireg_data_out.rs1_req;

            // Fetch rs2
            if (ireg_data_out.rs2_req) begin               // rs2 value is required
                if (fp_regstat_rs2_busy_i) begin   // the operand is provided by an in-flight instr.
                    if (comm_rs2_ready_i) begin // forward the operand from commit stage (CDB, ROB, etc.)
                        rs2_ready   = 1'b1;
                        rs2_value   = comm_rs2_value_i;
                    end else begin /* mark as not ready */
                        rs2_ready   = 1'b0;
                        rs2_value   = 0;
                    end
                end else begin                  // the operand is available in the register file 
                    rs2_ready           = 1'b1;
                    rs2_value           = fprf_rs2_value_i;
                end
            end else rs2_ready = ~ireg_data_out.rs2_req;

            // Fetch rs3
            // ADD RS3 TO FP RF AND RS
        end
        `endif /* LEN5_FP_EN */
    end

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    // Data to integer register status register
    assign  int_regstat_rd_idx_o    = ireg_data_out.rd_idx;
    assign  int_regstat_rob_idx_o   = comm_tail_idx_i;
    assign  int_regstat_rs1_idx_o   = ireg_data_out.rs1_idx;
    assign  int_regstat_rs2_idx_o   = ireg_data_out.rs2_idx;

    // Data to the integer register file
    assign  intrf_rs1_idx_o         = ireg_data_out.rs1_idx;
    assign  intrf_rs2_idx_o         = ireg_data_out.rs2_idx;

    `ifdef LEN5_FP_EN
    // Data to the floating-point register status register
    assign  fp_regstat_rs1_idx_o    = ireg_data_out.rs1_idx;
    assign  fp_regstat_rs2_idx_o    = ireg_data_out.rs2_idx; 
    assign  fp_regstat_rd_idx_o     = ireg_data_out.rd_idx;
    assign  fp_regstat_rob_idx_o    = comm_tail_idx_i;

    // Data to the floating-point register file
    assign  fprf_rs1_idx_o          = ireg_data_out.rs1_idx;
    assign  fprf_rs2_idx_o          = ireg_data_out.rs2_idx;
    `endif /* LEN5_FP_EN */

    // Data to the execution pipeline
    assign  ex_valid_o              = ex_valid;
    assign  ex_eu_ctl_o             = ireg_data_out.eu_ctl;
    assign  ex_rs1_o.ready          = rs1_ready;
    assign  ex_rs1_o.rob_idx        = rs1_rob_idx;
    assign  ex_rs1_o.value          = rs1_value;
    assign  ex_rs2_o.ready          = rs2_ready;
    assign  ex_rs2_o.rob_idx        = rs2_rob_idx;
    assign  ex_rs2_o.value          = rs2_value;
    assign  ex_imm_value_o          = ireg_data_out.imm_value;
    assign  ex_rob_idx_o            = comm_tail_idx_i;
    assign  ex_curr_pc_o            = ireg_data_out.curr_pc;
    assign  ex_pred_target_o        = ireg_data_out.pred_target;
    assign  ex_pred_taken_o         = ireg_data_out.pred_taken;

    // Data to commit stage
    assign  comm_data_o.instruction     = ireg_data_out.instr;
    assign  comm_data_o.instr_pc        = ireg_data_out.curr_pc;
    assign  comm_data_o.res_ready       = cu_il_res_ready;
    assign  comm_data_o.res_value       = (cu_il_res_sel_rs1) ? rs1_value : ireg_data_out.imm_value;
    assign  comm_data_o.res_aux         = '0;
    assign  comm_data_o.rd_idx          = ireg_data_out.rd_idx;
    assign  comm_data_o.except_raised   = ireg_data_out.except_raised;
    assign  comm_data_o.except_code     = ireg_data_out.except_code;
    assign  comm_rs1_rob_idx_o          = rs1_rob_idx;
    assign  comm_rs2_rob_idx_o          = rs2_rob_idx;

    // ----------
    // DEBUG CODE
    // ----------
    `ifndef SYNTHESIS
    always @(posedge clk_i) begin
        if (comm_valid_o && comm_ready_i) begin
            `uvm_info("ISSUE", $sformatf("Issuing instruction: %h", comm_data_o.instruction.raw), UVM_DEBUG);
        end
    end
    // Instruction sent to at most one execution unit
    property p_ex_valid;
        @(posedge clk_i) disable iff (!rst_n_i)
        comm_valid_o |->
            $onehot0(ex_valid_o);
    endproperty
    a_ex_valid: assert property (p_ex_valid);
    `endif /* SYNTHESIS */

endmodule