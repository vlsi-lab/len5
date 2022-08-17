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
`include "uvm_macros.svh"
import uvm_pkg::*;

import len5_pkg::*;
import expipe_pkg::*;

module branch_rs 
#(
    RS_DEPTH = 4  // must be a power of 2
)
(
    // Clock, reset, and flush
    input   logic                           clk_i,
    input   logic                           rst_n_i,
    input   logic                           flush_i,
	
    // Handshake from/to issue arbiter
    input   logic                           issue_valid_i,
    output  logic                           issue_ready_o,

    // Data from the decode stage
    input   logic [BU_CTL_LEN-1:0]          branch_type_i,
    input   logic                           rs1_ready_i,
    input   rob_idx_t                       rs1_idx_i,
    input   logic [XLEN-1:0]                rs1_value_i,
    input   logic                           rs2_ready_i,
    input   rob_idx_t                       rs2_idx_i,
    input   logic [XLEN-1:0]                rs2_value_i,
    input   logic [XLEN-1:0]                imm_value_i,
    input   rob_idx_t                       dest_idx_i,
    input   logic [XLEN-1:0]                curr_pc_i,
    input   logic [XLEN-1:0]                pred_target_i,
    input   logic                           pred_taken_i,

    // Handshake from/to the branch unit
    input   logic                           bu_ready_i,
    input   logic                           bu_valid_i,
    output  logic                           bu_valid_o,
    output  logic                           bu_ready_o,

    // Data from/to the execution unit
    input   logic [$clog2(RS_DEPTH)-1:0]    bu_entry_idx_i,
    input   logic                           bu_res_mis_i,   // mispredcition result
    input   logic                           bu_res_taken_i, // branch outcome
    input   logic [XLEN-1:0]                bu_res_target_i, // computed branch target address
    output  logic [$clog2(RS_DEPTH)-1:0]    bu_entry_idx_o,
    output  logic [XLEN-1:0]                bu_rs1_o,
    output  logic [XLEN-1:0]                bu_rs2_o,
    output  logic [XLEN-1:0]                bu_imm_o,
    output  logic [XLEN-1:0]                bu_curr_pc_o,
    output  logic [XLEN-1:0]                bu_pred_target_o,
    output  logic                           bu_pred_taken_o,
    output  logic [BU_CTL_LEN-1:0]          bu_branch_type_o,

    // Hanshake from/to the CDB 
    input   logic                           cdb_ready_i,
    input   logic                           cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic                           cdb_valid_o,

    // Data from/to the CDB
    input   cdb_data_t                      cdb_data_i,
    output  cdb_data_t                      cdb_data_o
);

    // DEFINITIONS

    localparam RS_IDX_LEN = $clog2(RS_DEPTH); //3 reservation station address width

    // Reservation station pointers
    logic [RS_IDX_LEN-1:0]      new_idx, ex_idx, cdb_idx;// next free entry, entry chosen for execution and entry chosen for CDB access
    logic                       new_idx_valid, ex_idx_valid, cdb_idx_valid;
    
    // The actual reservation station data structure
    bu_rs_entry_t               rs_data[0:RS_DEPTH-1];

    // Status signals
    logic   [RS_DEPTH-1:0]      valid_a, busy_a; // valid entries, empty entries
    logic   [RS_DEPTH-1:0]      ex_ready_a, res_ready_a; // Ready operands / ready result entries 
    `ifdef ENABLE_AGE_BASED_SELECTOR
    rob_idx_t                   entry_age_a [0:RS_DEPTH-1];
    `endif /* ENABLE_AGE_BASED_SELECTOR */

    // RS control signals
    logic                       rs_insert, rs_ex, rs_pop, rs_wr_res;

    // --------------
    // STATUS SIGNALS
    // --------------
    // These are required because name selection after indexing is not supported
    always_comb begin
        for (int i = 0; i < RS_DEPTH; i++) begin
            // Valid array
            valid_a[i]      = rs_data[i].valid; 
            
            // Busy array
            busy_a[i]       = rs_data[i].busy;

            `ifdef ENABLE_AGE_BASED_SELECTOR
            // Entry age
            entry_age_a[i]  = rs_data[i].entry_age;
            `endif
            
// Execution ready entries: an entry is a valid candidate for ex. (ready) when both its operands are available and the entry is valid
            ex_ready_a[i]   = rs_data[i].rs1_ready & rs_data[i].rs2_ready & rs_data[i].valid;
            
            // Result ready entries
            res_ready_a[i]  = rs_data[i].res_ready & rs_data[i].valid;
        end
    end

    // ----------------
    // RS CONTROL LOGIC
    // ----------------
    always_comb begin: rs_control_logic
        // Default values
        rs_ex           = 'b0;
        rs_insert       = 'b0;
        rs_pop          = 'b0;
        rs_wr_res       = 'b0;
        bu_valid_o      = 'b0;
        issue_ready_o   = 'b0;
        cdb_valid_o     = 'b0;
        bu_ready_o      = 'b1;  // Always true since the entry has already been allocated during issue 

        // Send selected instr. to EU
        if (ex_ready_a[ex_idx] && ex_idx_valid) begin
            bu_valid_o  = 'b1;  // If the selected entry is valid, notice the EU a new instr is ready for execution 
            if (bu_ready_i) rs_ex = 'b1; 
        end

        // Insert new instruction
        if (!rs_data[new_idx].valid && new_idx_valid) begin
            issue_ready_o = 'b1; // the RS can accept a new instruction being issued if the entry pointed by the new entry selector is free (i.e. valid = 0).
            if (issue_valid_i) rs_insert = 'b1;
        end

        // Send selected instruction to CDB
        if (res_ready_a[cdb_idx] && cdb_idx_valid) begin
            cdb_valid_o = 'b1; // If the selected entry has a valid result, notice the CDB
            if (cdb_ready_i) rs_pop = 'b1;
        end

        // Save result from EU
        if (bu_valid_i) begin
            rs_wr_res   = 'b1;
        end
    end

    // -------------------------------
    // RESERVATION STATION DATA UPDATE
    // -------------------------------
    always_ff @(posedge clk_i or negedge rst_n_i) begin: rs_data_update
        if (!rst_n_i) begin // Asynchronous reset
            foreach (rs_data[i]) begin
                rs_data[i]                  <= 0;
            end
        end else if (flush_i) begin // Synchronous flush: clearing valid is enough
            foreach (rs_data[i]) begin
                rs_data[i].valid            <= 1'b0;
            end
        end else begin // Normal update
            
            // Send entry selected for execution to EU
            if (rs_ex) rs_data[ex_idx].busy <= 'b1; // Mark the current instr. as busy so it is not choosen again
            
            // Insert new instruction 
            if (rs_insert) begin // WRITE PORT 1
                rs_data[new_idx].valid          <= issue_valid_i;
                rs_data[new_idx].busy           <= 'b0;
                `ifdef ENABLE_AGE_BASED_SELECTOR
                rs_data[new_idx].entry_age      <= 0;
                `endif
                rs_data[new_idx].branch_type    <= branch_type_i;
                rs_data[new_idx].rs1_ready      <= rs1_ready_i;
                rs_data[new_idx].rs1_idx        <= rs1_idx_i;
                rs_data[new_idx].rs1_value      <= rs1_value_i;
                rs_data[new_idx].rs2_ready      <= rs2_ready_i;
                rs_data[new_idx].rs2_idx        <= rs2_idx_i;
                rs_data[new_idx].rs2_value      <= rs2_value_i;
                rs_data[new_idx].imm_value      <= imm_value_i;
                rs_data[new_idx].curr_pc        <= curr_pc_i;
                rs_data[new_idx].res_ready      <= 'b0;
                rs_data[new_idx].res_idx        <= dest_idx_i;
                rs_data[new_idx].target         <= pred_target_i;
                rs_data[new_idx].taken          <= pred_taken_i;

                `ifdef ENABLE_AGE_BASED_SELECTOR
                // Update the age of all the entries
                foreach (rs_data[i]) begin
                    if (new_idx != i[RS_IDX_LEN-1:0] && rs_data[i].valid) rs_data[i].entry_age <= rs_data[i].entry_age + 1;
                end
                `endif
            end
            
            // Pop the entry sent to the CDB
            if (rs_pop) rs_data[cdb_idx].valid      <= 'b0;
            
            // Save result from EU (WRITE PORT 2)
            if (rs_wr_res) begin
                rs_data[bu_entry_idx_i].res_ready      <= 'b1;
                rs_data[bu_entry_idx_i].mispredicted   <= bu_res_mis_i;
                rs_data[bu_entry_idx_i].taken          <= bu_res_taken_i;
                rs_data[bu_entry_idx_i].target         <= bu_res_target_i;
            end

            // Retrieve operands from CDB (PARALLEL WRITE PORT 1)
            foreach (rs_data[i]) begin
                if (rs_data[i].valid && !ex_ready_a[i]) begin // Following logic is masked if the entry is not valid
                    if (!rs_data[i].rs1_ready) begin
                        if (cdb_valid_i && !cdb_data_i.except_raised && (rs_data[i].rs1_idx == cdb_data_i.rob_idx)) begin
                            rs_data[i].rs1_ready    <= 'b1;
                            rs_data[i].rs1_value    <= cdb_data_i.res_value;
                        end
                    end
                    if (!rs_data[i].rs2_ready) begin
                        if (cdb_valid_i && !cdb_data_i.except_raised && (rs_data[i].rs2_idx == cdb_data_i.rob_idx)) begin
                            rs_data[i].rs2_ready    <= 'b1;
                            rs_data[i].rs2_value    <= cdb_data_i.res_value;
                        end
                    end
                end
            end
        end
    end

    // ------------------
    // NEW ENTRY SELECTOR
    // ------------------
    // The entry where the next instruction will be allocated is the first free one (i.e. not valid) in the structure, so the selector is a priority encoder
    prio_enc #(.N(RS_DEPTH)) new_entry_prio_enc
    (
        .lines_i    (~valid_a),
        .enc_o      (new_idx),
        .valid_o    (new_idx_valid)
    );
    
    // ------------------
    // EXECUTION SELECTOR
    // ------------------
    `ifdef ENABLE_AGE_BASED_SELECTOR
    age_based_sel #(.N(RS_DEPTH), .AGE_LEN(ROB_IDX_LEN)) ex_selector
    (
        .lines_i    (valid_a & ~busy_a & ~res_ready_a),
        .ages_i     (entry_age_a),
        .enc_o      (ex_idx),
        .valid_o    (ex_idx_valid)
    );

    `else
    // Simple priority encoder
    prio_enc #(.N(RS_DEPTH)) ex_sel_prio_enc
    (
        .lines_i    (valid_a & ~busy_a & ~res_ready_a),
        .enc_o      (ex_idx),
        .valid_o    (ex_idx_valid)
    );
    `endif

    // ------------
    // CDB SELECTOR
    // ------------
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // The selector is mostly equal to the execution selector. The only difference is that here the candidates are choosen among the entries whose result is ready (i.e. it has already been written back by the EU)
    age_based_sel #(.N(RS_DEPTH), .AGE_LEN(ROB_IDX_LEN)) cdb_selector
    (
        .lines_i    (res_ready_a),
        .ages_i     (entry_age_a),
        .enc_o      (cdb_idx),
        .valid_o    (cdb_idx_valid)
    );
    
    `else
    // Simple priority encoder
    prio_enc #(.N(RS_DEPTH)) cdb_sel_prio_enc
    (
        .lines_i    (res_ready_a),
        .enc_o      (cdb_idx),
        .valid_o    (cdb_idx_valid)
    );
    `endif

    // -----------------
    // OUTPUT EVALUATION
    // -----------------
    
    // To branch logic (READ PORT 1)
    assign bu_rs1_o                = rs_data[ex_idx].rs1_value;
    assign bu_rs2_o                = rs_data[ex_idx].rs2_value;
    assign bu_imm_o                = rs_data[ex_idx].imm_value;
    assign bu_curr_pc_o            = rs_data[ex_idx].curr_pc;
    assign bu_pred_target_o        = rs_data[ex_idx].target;
    assign bu_pred_taken_o         = rs_data[ex_idx].taken;
    assign bu_branch_type_o        = rs_data[ex_idx].branch_type;
    assign bu_entry_idx_o          = ex_idx;

    // To CDB (READ PORT 2: reads different fields from READ PORT 1)
    assign cdb_data_o.rob_idx                 = rs_data[cdb_idx].res_idx;
    assign cdb_data_o.res_value               = rs_data[cdb_idx].target;
    assign cdb_data_o.res_aux.jb.mispredicted = rs_data[cdb_idx].mispredicted;
    assign cdb_data_o.res_aux.jb.taken        = rs_data[cdb_idx].taken;
    assign cdb_data_o.except_raised           = 1'b0;
    assign cdb_data_o.except_code             = E_UNKNOWN;

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    always @(negedge clk_i) begin
        // Notice when the reservation station is full
        assert (valid_a !== '1) else `uvm_info("BUFFSIZE", $sformatf("Generic RS full (%0d entries): you might want to increase its depth", RS_DEPTH), UVM_HIGH)
        foreach (rs_data[i]) begin
            // Check if the correct order of operations is respected
            assert (!(res_ready_a[i] && !ex_ready_a[i])) else `uvm_error("HAZARD", $sformatf("RS entry %4d has ready result before having ready operands. This should be impossible", i))
             `ifdef ENABLE_AGE_BASED_SELECTOR
            assert (rs_data[i].entry_age < 1<<ROB_IDX_LEN) else `uvm_error("OTHER", "RS entry %4d is reaching head overflow. This should be impossible.", i)
            `endif
        end
    end
    `endif

endmodule
