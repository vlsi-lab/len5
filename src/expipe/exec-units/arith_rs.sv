// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: arith_rs.sv
// Author: Michele Caon
// Date: 19/08/2022

// LEN5 compilation switches
`include "len5_config.svh"

// Import UVM report macros
`include "uvm_macros.svh"
import uvm_pkg::*;

import len5_pkg::*;
import expipe_pkg::*;

module arith_rs 
#(
    parameter   DEPTH = 4,  // must be a power of 2
    parameter   EU_CTL_LEN = 4,
    localparam  RS_IDX_LEN = $clog2(DEPTH)
)
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,
	

    /* Issue Stage */
    input   logic                   issue_valid_i,
    output  logic                   issue_ready_o,
    input   logic [EU_CTL_LEN-1:0]  issue_eu_ctl_i,
    input   op_data_t               issue_rs1_i,
    input   op_data_t               issue_rs2_i,
    input   rob_idx_t               issue_dest_rob_idx_i,

    /* CDB */
    input   logic                   cdb_ready_i,
    input   logic                   cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic                   cdb_valid_o,
    input   cdb_data_t              cdb_data_i,
    output  cdb_data_t              cdb_data_o,

    /* Execution unit */
    input   logic                   eu_ready_i,
    input   logic                   eu_valid_i,
    output  logic                   eu_valid_o,
    output  logic                   eu_ready_o,
    input   logic [RS_IDX_LEN-1:0]  eu_entry_idx_i,
    input   logic [XLEN-1:0]        eu_result_i,
    input   logic                   eu_except_raised_i,
    input   except_code_t           eu_except_code_i,
    output  logic [EU_CTL_LEN-1:0]  eu_ctl_o,
    output  logic [XLEN-1:0]        eu_rs1_o,
    output  logic [XLEN-1:0]        eu_rs2_o,
    output  logic [RS_IDX_LEN-1:0]  eu_entry_idx_o
);
    // INTERNAL SIGNALS
    // ----------------

    // Generic arithmetic reservation station content 
    typedef struct packed {
        logic [EU_CTL_LEN-1:0]  eu_ctl;         // Control signals for the EU
        rob_idx_t               rs1_rob_idx;    // The entry of the rob that will contain the required operand.
        logic [XLEN-1:0]        rs1_value;      // The value of the first operand
        rob_idx_t               rs2_rob_idx;    // The entry of the rob that will contain the required operand.
        logic [XLEN-1:0]        rs2_value;      // The value of the second operand
        rob_idx_t               dest_rob_idx;   // The entry of the ROB where the result will be stored
        logic [XLEN-1:0]        res_value;
        logic                   except_raised;
        except_code_t           except_code;
    } arith_rs_data_t;

    // New, execution, and CDB write pointers
    logic [RS_IDX_LEN-1:0]  new_idx, ex_idx, cdb_idx;
    logic                   new_idx_valid, ex_idx_valid, cdb_idx_valid;
    logic                   empty[DEPTH], ready_ex[DEPTH], ready_cdb[DEPTH];
    
    // Arithmetic reservation station data
    arith_rs_data_t         data[DEPTH];
    arith_state_t           curr_state[DEPTH], next_state[DEPTH];

    // Reservation station control
    logic                   insert, remove, save_rs, ex_accepted, save_res;
    logic                   match_rs1[DEPTH], match_rs2[DEPTH];
    arith_op_t              arith_op[DEPTH];

    // Ready signals for the selectors
    always_comb begin : p_enc_signals
        foreach (curr_state[i]) begin
            empty[i]        = curr_state[i] == ARITH_S_EMPTY;
            ready_ex[i]     = curr_state[i] == ARITH_S_EX_REQ;
            ready_cdb[i]    = curr_state[i] == ARITH_S_COMPLETED;
        end        
    end

    // -------------------------------------------
    // ARITHMETIC RESERVATION STATION CONTROL UNIT
    // -------------------------------------------

    // Control signals
    assign  insert      = issue_valid_i & issue_ready_o;
    assign  remove      = cdb_valid_o & cdb_ready_i;
    assign  save_rs     = cdb_valid_i;
    assign  ex_accepted = eu_valid_o & eu_ready_i;
    assign  save_res    = eu_valid_i & eu_ready_o;

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
        foreach (arith_op[i])  arith_op[i] = ARITH_OP_NONE;

        foreach (curr_state[i]) begin
            case (curr_state[i])
                ARITH_S_EMPTY: begin // insert a new instruction
                    if (insert && new_idx == i) begin
                        arith_op[i]        = ARITH_OP_INSERT;
                        if (issue_rs1_i.ready && issue_rs2_i.ready)
                            next_state[i]   = ARITH_S_EX_REQ;
                        else if (!issue_rs1_i.ready && issue_rs2_i.ready)
                            next_state[i]   = ARITH_S_RS1_PENDING;
                        else if (issue_rs1_i.ready && !issue_rs2_i.ready)
                            next_state[i]   = ARITH_S_RS2_PENDING;
                        else
                            next_state[i]   = ARITH_S_RS12_PENDING;
                    end else 
                        next_state[i] = ARITH_S_EMPTY; 
                end
                ARITH_S_RS12_PENDING: begin // save rs1 and/or rs2 value from CDB
                    if (save_rs) begin
                        if (match_rs1[i] && match_rs2[i]) begin
                            arith_op[i]     = ARITH_OP_SAVE_RS12;
                            next_state[i]   = ARITH_S_EX_REQ;
                        end else if (match_rs1[i]) begin
                            arith_op[i]     = ARITH_OP_SAVE_RS1;
                            next_state[i]   = ARITH_S_RS2_PENDING;
                        end else if (match_rs2[i]) begin
                            arith_op[i]     = ARITH_OP_SAVE_RS2;
                            next_state[i]   = ARITH_S_RS1_PENDING;
                        end else 
                            next_state[i]   = ARITH_S_RS12_PENDING;
                    end else 
                        next_state[i]   = ARITH_S_RS12_PENDING;
                end
                ARITH_S_RS1_PENDING: begin // save rs2 value from CDB
                    if (save_rs && match_rs1[i]) begin
                        arith_op[i]     = ARITH_OP_SAVE_RS1;
                        next_state[i]   = ARITH_S_EX_REQ;
                    end else
                        next_state[i]   = ARITH_S_RS1_PENDING;
                end
                ARITH_S_RS2_PENDING: begin // save rs2 value from CDB
                    if (save_rs && match_rs2[i]) begin
                        arith_op[i]     = ARITH_OP_SAVE_RS2;
                        next_state[i]   = ARITH_S_EX_REQ;
                    end else
                        next_state[i]   = ARITH_S_RS2_PENDING;
                end
                ARITH_S_EX_REQ: begin // request branch resolution to branch logic
                    if (save_res && eu_entry_idx_i == i) begin
                        arith_op[i]     = ARITH_OP_SAVE_RES;
                        next_state[i]   = ARITH_S_COMPLETED;
                    end else if (ex_accepted && ex_idx == i)
                        next_state[i]   = ARITH_S_EX_WAIT;
                    else
                        next_state[i]   = ARITH_S_EX_REQ;
                end
                ARITH_S_EX_WAIT: begin // wait for execution completion
                    if (save_res && eu_entry_idx_i == i) begin
                        arith_op[i]     = ARITH_OP_SAVE_RES;
                        next_state[i]   = ARITH_S_COMPLETED;
                    end else
                        next_state[i]   = ARITH_S_EX_WAIT;
                end
                ARITH_S_COMPLETED: begin
                    if (remove && cdb_idx == i)
                        next_state[i]   = ARITH_S_EMPTY;
                    else 
                        next_state[i]   = ARITH_S_COMPLETED;
                end
                default: next_state[i]  = ARITH_S_HALT;
            endcase
        end
    end

    // State update
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : p_state_update
        if (!rst_n_i) foreach (curr_state[i]) curr_state[i] <= ARITH_S_EMPTY;
        else if (flush_i) foreach (curr_state[i]) curr_state[i] <= ARITH_S_EMPTY;
        else curr_state <= next_state;
    end

    // ------------------
    // ARITH UNIT BUFFER
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
            foreach (arith_op[i]) begin
                case (arith_op[i])
                    ARITH_OP_INSERT: begin
                        data[i].eu_ctl              <= issue_eu_ctl_i;
                        data[i].rs1_rob_idx         <= issue_rs1_i.rob_idx;
                        data[i].rs1_value           <= issue_rs1_i.value;
                        data[i].rs2_rob_idx         <= issue_rs2_i.rob_idx;
                        data[i].rs2_value           <= issue_rs2_i.value;
                        data[i].dest_rob_idx        <= issue_dest_rob_idx_i;
                    end
                    ARITH_OP_SAVE_RS12: begin
                        data[i].rs1_value           <= cdb_data_i.res_value;
                        data[i].rs2_value           <= cdb_data_i.res_value;
                    end
                    ARITH_OP_SAVE_RS1: begin
                        data[i].rs1_value           <= cdb_data_i.res_value;
                    end
                    ARITH_OP_SAVE_RS2: begin
                        data[i].rs2_value           <= cdb_data_i.res_value;
                    end
                    ARITH_OP_SAVE_RES: begin
                        data[i].res_value           <= eu_result_i;
                        data[i].except_raised       <= eu_except_raised_i;
                        data[i].except_code         <= eu_except_code_i;
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
    assign  issue_ready_o   = curr_state[new_idx] == ARITH_S_EMPTY;

    /* CDB */
    assign  cdb_valid_o                         = curr_state[cdb_idx] == ARITH_S_COMPLETED;
    assign  cdb_data_o.rob_idx                  = data[cdb_idx].dest_rob_idx;
    assign  cdb_data_o.res_value                = data[cdb_idx].res_value;
    assign  cdb_data_o.res_aux                  = '0;
    assign  cdb_data_o.except_raised            = data[cdb_idx].except_raised;
    assign  cdb_data_o.except_code              = data[cdb_idx].except_code;

    /* Execution unit */
    assign  eu_valid_o      = curr_state[ex_idx] == ARITH_S_EX_REQ;
    assign  eu_ready_o      = 1'b1;
    assign  eu_ctl_o        = data[ex_idx].eu_ctl;
    assign  eu_rs1_o        = data[ex_idx].rs1_value;
    assign  eu_rs2_o        = data[ex_idx].rs2_value;
    assign  eu_entry_idx_o  = ex_idx;

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
            assert property (@(posedge clk_i) disable iff (!rst_n_i) curr_state[i] == ARITH_S_HALT |-> ##1 curr_state[i] != ARITH_S_HALT);
        end
    end
    `endif /* SYNTHESIS */

endmodule