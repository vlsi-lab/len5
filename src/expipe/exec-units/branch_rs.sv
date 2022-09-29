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
// File: branch_rs.sv
// Author: Michele Caon
// Date: 08/11/2019

// Import UVM report macros
`ifndef SYNTHESIS
`include "uvm_macros.svh"
import uvm_pkg::*;
`endif

import len5_pkg::*;
import expipe_pkg::*;

module branch_rs 
#(
    parameter   DEPTH = 4,  // must be a power of 2
    localparam  RS_IDX_LEN = $clog2(DEPTH)
)
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,
	
    /* Issue Stage */
    input   logic                   issue_valid_i,
    output  logic                   issue_ready_o,
    input   branch_ctl_t           issue_branch_type_i,
    input   op_data_t               issue_rs1_i,
    input   op_data_t               issue_rs2_i,
    input   logic [XLEN-1:0]        issue_imm_value_i,
    input   rob_idx_t               issue_dest_rob_idx_i,
    input   logic [XLEN-1:0]        issue_curr_pc_i,
    input   logic [XLEN-1:0]        issue_pred_target_i,
    input   logic                   issue_pred_taken_i,

    /* Common Data Bus (CDB) */
    input   logic                   cdb_ready_i,
    input   logic                   cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic                   cdb_valid_o,
    input   cdb_data_t              cdb_data_i,
    output  cdb_data_t              cdb_data_o,

    /* Branch unit */
    input   logic                   bu_valid_i,
    input   logic                   bu_ready_i,
    output  logic                   bu_valid_o,
    output  logic                   bu_ready_o,
    input   logic [RS_IDX_LEN-1:0]  bu_entry_idx_i,
    input   logic                   bu_res_mis_i,   // mispredcition result
    input   logic                   bu_res_taken_i, // branch outcome
    input   logic [XLEN-1:0]        bu_res_target_i, // computed branch target address
`ifndef LEN5_C_EN
    input   logic                   bu_except_raised_i,
`endif /* LEN5_C_EN */
    output  logic [RS_IDX_LEN-1:0]  bu_entry_idx_o,
    output  logic [XLEN-1:0]        bu_rs1_o,
    output  logic [XLEN-1:0]        bu_rs2_o,
    output  logic [XLEN-1:0]        bu_imm_o,
    output  logic [XLEN-1:0]        bu_curr_pc_o,
    output  logic [XLEN-1:0]        bu_pred_target_o,
    output  logic                   bu_pred_taken_o,
    output  branch_ctl_t           bu_branch_type_o
);
    // INTERNAL SIGNALS
    // ----------------

    // New, execution, and CDB write pointers
    logic [RS_IDX_LEN-1:0]  new_idx, ex_idx, cdb_idx;
    logic                   new_idx_valid, ex_idx_valid, cdb_idx_valid;
    logic                   empty[DEPTH], ready_ex[DEPTH], ready_cdb[DEPTH];
    
    // Branch reservation station data
    bu_data_t               data[DEPTH];
    bu_state_t              curr_state[DEPTH], next_state[DEPTH];

    // Reservation station control
    logic                   insert, remove, save_rs, ex_accepted, save_res;
    logic                   match_rs1[DEPTH], match_rs2[DEPTH];
    bu_op_t                 bu_op[DEPTH];

    // Ready signals for the selectors
    always_comb begin : p_enc_signals
        foreach (curr_state[i]) begin
            empty[i]        = curr_state[i] == BU_S_EMPTY;
            ready_ex[i]     = curr_state[i] == BU_S_EX_REQ;
            ready_cdb[i]    = curr_state[i] == BU_S_COMPLETED;
        end        
    end

    // -------------------------------
    // BRANCH UNIT BUFFER CONTROL UNIT
    // -------------------------------

    // Control signals
    assign  insert      = issue_valid_i & issue_ready_o;
    assign  remove      = cdb_valid_o & cdb_ready_i;
    assign  save_rs     = cdb_valid_i;
    assign  ex_accepted = bu_valid_o & bu_ready_i;
    assign  save_res    = bu_valid_i & bu_ready_o;

    // Matching operands tags
    always_comb begin : p_match_rs
        foreach (data[i]) begin
            match_rs1[i]    = (cdb_data_i.rob_idx == data[i].rs1_rob_idx);
            match_rs2[i]    = (cdb_data_i.rob_idx == data[i].rs2_rob_idx);
        end
    end

    // State progression
    // NOTE: Mealy to avoid resampling data
    always_comb begin : p_state_prog
        // Default operation (no operation)
        foreach (bu_op[i])  bu_op[i] = BU_OP_NONE;

        foreach (curr_state[i]) begin
            case (curr_state[i])
                BU_S_EMPTY: begin // insert a new instruction
                    if (insert && new_idx == i) begin
                        bu_op[i]        = BU_OP_INSERT;
                        if (issue_rs1_i.ready && issue_rs2_i.ready)
                            next_state[i]   = BU_S_EX_REQ;
                        else if (!issue_rs1_i.ready && issue_rs2_i.ready)
                            next_state[i]   = BU_S_RS1_PENDING;
                        else if (issue_rs1_i.ready && !issue_rs2_i.ready)
                            next_state[i]   = BU_S_RS2_PENDING;
                        else
                            next_state[i]   = BU_S_RS12_PENDING;
                    end else 
                        next_state[i] = BU_S_EMPTY; 
                end
                BU_S_RS12_PENDING: begin // save rs1 and/or rs2 value from CDB
                    if (save_rs) begin
                        if (match_rs1[i] && match_rs2[i]) begin
                            bu_op[i]        = BU_OP_SAVE_RS12;
                            next_state[i]   = BU_S_EX_REQ;
                        end else if (match_rs1[i]) begin
                            bu_op[i]        = BU_OP_SAVE_RS1;
                            next_state[i]   = BU_S_RS2_PENDING;
                        end else if (match_rs2[i]) begin
                            bu_op[i]        = BU_OP_SAVE_RS2;
                            next_state[i]   = BU_S_RS1_PENDING;
                        end else 
                            next_state[i]   = BU_S_RS12_PENDING;
                    end else 
                        next_state[i]   = BU_S_RS12_PENDING;
                end
                BU_S_RS1_PENDING: begin // save rs2 value from CDB
                    if (save_rs && match_rs1[i]) begin
                        bu_op[i]        = BU_OP_SAVE_RS1;
                        next_state[i]   = BU_S_EX_REQ;
                    end else
                        next_state[i]   = BU_S_RS1_PENDING;
                end
                BU_S_RS2_PENDING: begin // save rs2 value from CDB
                    if (save_rs && match_rs2[i]) begin
                        bu_op[i]        = BU_OP_SAVE_RS2;
                        next_state[i]   = BU_S_EX_REQ;
                    end else
                        next_state[i]   = BU_S_RS2_PENDING;
                end
                BU_S_EX_REQ: begin // request branch resolution to branch logic
                    if (save_res && bu_entry_idx_i == i) begin
                        bu_op[i]        = BU_OP_SAVE_RES;
                        next_state[i]   = BU_S_COMPLETED;
                    end else if (ex_accepted && ex_idx == i)
                        next_state[i]   = BU_S_EX_WAIT;
                    else
                        next_state[i]   = BU_S_EX_REQ;
                end
                BU_S_EX_WAIT: begin // wait for execution completion
                    if (save_res && bu_entry_idx_i == i) begin
                        bu_op[i]        = BU_OP_SAVE_RES;
                        next_state[i]   = BU_S_COMPLETED;
                    end else
                        next_state[i]   = BU_S_EX_WAIT;
                end
                BU_S_COMPLETED: begin
                    if (remove && cdb_idx == i)
                        next_state[i]   = BU_S_EMPTY;
                    else 
                        next_state[i]   = BU_S_COMPLETED;
                end
                default: next_state[i]  = BU_S_HALT;
            endcase
        end
    end

    // State update
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : p_state_update
        if (!rst_n_i) foreach (curr_state[i]) curr_state[i] <= BU_S_EMPTY;
        else if (flush_i) foreach (curr_state[i]) curr_state[i] <= BU_S_EMPTY;
        else curr_state <= next_state;
    end

    // ------------------
    // BRANCH UNIT BUFFER
    // ------------------
    // NOTE: operations priority:
    // 1) insert a new instruction
    // 2) remove a completed instruction
    // 3) update the result
    // 4) update rs1 and/or rs2
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : p_bu_update
        if (!rst_n_i) begin
            foreach (data[i]) begin
                data[i]         <= '0;
            end
        end else begin
            /* Performed the required action for each instruction */
            foreach (bu_op[i]) begin
                case (bu_op[i])
                    BU_OP_INSERT: begin
                        data[i].branch_type         <= issue_branch_type_i;
                        data[i].curr_pc             <= issue_curr_pc_i;
                        data[i].rs1_rob_idx         <= issue_rs1_i.rob_idx;
                        data[i].rs1_value           <= issue_rs1_i.value;
                        data[i].rs2_rob_idx         <= issue_rs2_i.rob_idx;
                        data[i].rs2_value           <= issue_rs2_i.value;
                        data[i].imm_value           <= issue_imm_value_i;
                        data[i].dest_rob_idx        <= issue_dest_rob_idx_i;
                        data[i].target              <= issue_pred_target_i;
                        data[i].taken               <= issue_pred_taken_i;
                    end
                    BU_OP_SAVE_RS12: begin
                        data[i].rs1_value           <= cdb_data_i.res_value;
                        data[i].rs2_value           <= cdb_data_i.res_value;
                    end
                    BU_OP_SAVE_RS1: begin
                        data[i].rs1_value           <= cdb_data_i.res_value;
                    end
                    BU_OP_SAVE_RS2: begin
                        data[i].rs2_value           <= cdb_data_i.res_value;
                    end
                    BU_OP_SAVE_RES: begin
                        data[i].target              <= bu_res_target_i;
                        data[i].taken               <= bu_res_taken_i;
                        data[i].mispredicted        <= bu_res_mis_i;
                    `ifndef LEN5_C_EN
                        data[i].except_raised       <= bu_except_raised_i;
                    `endif /* LEN5_C_EN */
                    end
                    default:;
                endcase
            end
        end
    end

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    /* Issue Stage */
    assign  issue_ready_o   = curr_state[new_idx] == BU_S_EMPTY;

    /* CDB */
    assign  cdb_valid_o                         = curr_state[cdb_idx] == BU_S_COMPLETED;
    assign  cdb_data_o.rob_idx                  = data[cdb_idx].dest_rob_idx;
    assign  cdb_data_o.res_value                = data[cdb_idx].target;
    assign  cdb_data_o.res_aux.jb.mispredicted  = data[cdb_idx].mispredicted;
    assign  cdb_data_o.res_aux.jb.taken         = data[cdb_idx].taken;
`ifndef LEN5_C_EN
    assign  cdb_data_o.except_raised            = data[cdb_idx].except_raised;
`else
    assign  cdb_data_o.except_raised            = 1'b0;
`endif /* LEN5_C_EN */
    assign  cdb_data_o.except_code              = E_I_ADDR_MISALIGNED;

    /* Branch Unit logic */
    assign  bu_valid_o       = curr_state[ex_idx] == BU_S_EX_REQ;
    assign  bu_ready_o       = 1'b1;
    assign  bu_rs1_o         = data[ex_idx].rs1_value;
    assign  bu_rs2_o         = data[ex_idx].rs2_value;
    assign  bu_imm_o         = data[ex_idx].imm_value;
    assign  bu_curr_pc_o     = data[ex_idx].curr_pc;
    assign  bu_pred_target_o = data[ex_idx].target;
    assign  bu_pred_taken_o  = data[ex_idx].taken;
    assign  bu_branch_type_o = data[ex_idx].branch_type;
    assign  bu_entry_idx_o   = ex_idx;

    // ---------------
    // ENTRY SELECTORS
    // ---------------

    // New entry
    prio_enc #(.N(DEPTH)) new_sel
    (
        .lines_i    (empty         ),
        .enc_o      (new_idx       ),
        .valid_o    ()
    );

    // Execution
    prio_enc #(.N(DEPTH)) ex_sel
    (
        .lines_i    (ready_ex      ),
        .enc_o      (ex_idx        ),
        .valid_o    ()
    );

    // CDB access
    prio_enc #(.N(DEPTH)) cdb_sel
    (
        .lines_i    (ready_cdb     ),
        .enc_o      (cdb_idx       ),
        .valid_o    ()
    );

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    always @(posedge clk_i) begin
        foreach (curr_state[i]) begin
            assert property (@(posedge clk_i) disable iff (!rst_n_i) curr_state[i] == BU_S_HALT |-> ##1 curr_state[i] != BU_S_HALT);
        end
    end
    `endif /* SYNTHESIS */
endmodule
