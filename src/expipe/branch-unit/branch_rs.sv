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

import len5_pkg::XLEN;
import len5_pkg::ILEN;
import len5_pkg::branch_type_t;
import len5_pkg::BEQ;
import len5_pkg::BNE;
import len5_pkg::BLT;
import len5_pkg::BGE;
import len5_pkg::BLTU;
import len5_pkg::BGEU;

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
    input   rob_idx_t         rs1_idx_i,
    input   logic [XLEN-1:0]                rs1_value_i,
    input   logic                           rs2_ready_i,
    input   rob_idx_t         rs2_idx_i,
    input   logic [XLEN-1:0]                rs2_value_i,
    input   logic [XLEN-1:0]                imm_value_i,
    input   rob_idx_t         dest_idx_i,
    input   logic [XLEN-1:0]                pred_pc_i,
    input   logic [XLEN-1:0]                pred_target_i,
    input   logic                           pred_taken_i,

    // Handshake from/to the branch unit
    input   logic                           bu_ready_i,
    input   logic                           bu_valid_i,
    output  logic                           bu_valid_o,
    output  logic                           bu_ready_o,

    // Data from/to the execution unit
    input   logic                           mispredict_i, // mispredcition result
    output  logic [XLEN-1:0]                bu_rs1_o,
    output  logic [XLEN-1:0]                bu_rs2_o,
    output  logic [XLEN-1:0]                bu_imm_o,
    output  logic [XLEN-1:0]                bu_pred_pc_o,
    output  logic [XLEN-1:0]                bu_pred_target_o,
    output  logic                           bu_pred_taken_o,
    output  logic [BU_CTL_LEN-1:0]          bu_branch_type_o,

    // Hanshake from/to the CDB 
    input   logic                           cdb_ready_i,
    input   logic                           cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic                           cdb_valid_o,

    // Data from/to the CDB
    input cdb_data_t                      cdb_data_i,
    output  cdb_data_t                      cdb_data_o
);

    // DEFINITIONS

    localparam RS_IDX_LEN = $clog2(RS_DEPTH); //3 reservation station address width

    // Reservation station entry 
    typedef struct packed {
        logic                   valid;      // The entry contains a valid instruction
        logic                   busy;       // The instruction is being executed in the assigned EU
        logic [BU_CTL_LEN-1:0]  branch_type;// Branch type for the branch unit
        logic                   rs1_ready;  // The first operand value is available in 'rs1_value'
        rob_idx_t rs1_idx;    // The entry of the rob that will contain the required operand. This can be fetched as soon as it appears on the CDB (when the EU produces it).
        logic [XLEN-1:0]        rs1_value;  // The value of the first operand
        logic                   rs2_ready;  // The second operand value is available in 'rs2_value'
        rob_idx_t rs2_idx;    // The entry of the rob that will contain the required operand. This can be fetched as soon as it appears on the CDB (when the EU produces it).
        logic [XLEN-1:0]        rs2_value;  // The value of the second operand
        logic [XLEN-1:0]        imm_value;  // Immediate value
        logic [XLEN-1:0]        pred_pc;    // Program counter of the current instruction (from the fetch stage)
        logic [XLEN-1:0]        pred_target;// Predicted target program counter (from the fetch stage)
        logic                   pred_taken; // Branch outcome prediction (from the fetch stage)
        rob_idx_t res_idx;    // The entry of the ROB where the result will be stored
        logic                   mispredicted;// the branch was mispredicted
        logic                   res_ready;  // The value of the result is available in 'mispredicted'"
    } rs_entry_t;

    // Reservation station pointers
    logic [RS_IDX_LEN-1:0]      tail_idx, ex_idx, head_idx, wr_res_idx; 

    // Head, ex and tail counters
    logic                       head_cnt_en, head_cnt_clr, ex_cnt_en, ex_cnt_clr, tail_cnt_en, tail_cnt_clr,wr_res_cnt_en, wr_res_cnt_clr;

    // The actual reservation station data structure
    rs_entry_t  rs_data[0:RS_DEPTH-1];
    
    // Status signals
    logic   valid_a[0:RS_DEPTH-1], busy_a[0:RS_DEPTH-1]; // valid entries, empty entries
    logic   ex_ready_a[0:RS_DEPTH-1], res_ready_a[0:RS_DEPTH-1]; // Ready operands / ready result entries 

    // RS control signals
    logic                       rs_push, rs_ex, rs_pop, rs_wr_res;

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
            
            // Execution ready entries: an entry is a valid candidate for ex. (ready) when both its operands are available, is valid and not busy
            ex_ready_a[i]   = rs_data[i].rs1_ready & rs_data[i].rs2_ready & rs_data[i].valid & !rs_data[i].busy;
            
            // Result ready entries
            res_ready_a[i]  = rs_data[i].res_ready & rs_data[i].valid;
        end
    end

    // ----------------
    // RS CONTROL LOGIC
    // ----------------
    always_comb begin: rs_control_logic
        // DEFAULT VALUES:

        // Head/tail pointers control
        head_cnt_en         = 1'b0;
        head_cnt_clr        = flush_i;
        ex_cnt_en           = 1'b0;
        ex_cnt_clr          = flush_i;
        tail_cnt_en         = 1'b0;
        tail_cnt_clr        = flush_i;
        wr_res_cnt_en       = 1'b0;
        wr_res_cnt_clr      = flush_i;

        // Operation control
        rs_push             = 1'b0;
        rs_ex               = 1'b0;
        rs_pop              = 1'b0;
        rs_wr_res           = 1'b0;

        // Handshake control 
        issue_ready_o       = 1'b0;
        bu_ready_o          = 1'b1; // Always ready for the branch unit
        bu_valid_o          = 1'b0;
        cdb_valid_o         = 1'b0;

        // OPERATION CONTROL

        // PUSH NEW INSTRUCTION
        if (!rs_data[tail_idx].valid) begin
            issue_ready_o        = 1'b1;
            if (issue_valid_i) begin
                rs_push            = 1'b1; // if a new instruction is available, push it
                tail_cnt_en        = 1'b1; // increment tail pointer
            end
        end

        // EXECUTE INSTRUCTION
        if (ex_ready_a[ex_idx]) begin
            bu_valid_o             = 1'b1;
            if (bu_ready_i) begin
                rs_ex              = 1'b1; // the branch unit can accept the instruction
                ex_cnt_en          = 1'b1; // increment the execution pointer
            end
        end

        // WRITE HEAD RESULT ON THE CDB AND POP THE INSTRUCTION
        if (res_ready_a[head_idx]) begin
            cdb_valid_o            = 1'b1;
            if (cdb_ready_i) begin
                rs_pop             = 1'b1; // if the CDB can accept outcoming data, 
                head_cnt_en        = 1'b1;
            end
        end

        // WRITE RESULT FROM THE BRANCH UNIT 
        if (bu_valid_i && busy_a[wr_res_idx]) begin
            rs_wr_res              = 1'b1;
            wr_res_cnt_en          = 1'b1;
        end
    end

    // -------------------------------
    // RESERVATION STATION FIFO UPDATE
    // -------------------------------
    always_ff @(posedge clk_i or negedge rst_n_i) begin: rs_fifo_update
        if (!rst_n_i) begin // Asynchronous reset
            foreach (rs_data[i]) begin
                rs_data[i]                  <= 0;
            end
        end else if (flush_i) begin // Synchronous flush: clearing status info is enough
            foreach (rs_data[i]) begin
                rs_data[i].valid            <= 'b0;
                rs_data[i].busy             <= 'b0;
                rs_data[i].rs1_ready        <= 'b0;
                rs_data[i].rs2_ready        <= 'b0;
                rs_data[i].res_ready        <= 'b0;
            end
		
        end else begin // Normal update

            // -------------------
            // PARALLEL OPERATIONS
            // -------------------
            // Retrieve operands from CDB (PARALLEL WRITE PORT 1)
            foreach (rs_data[i]) begin
                if (rs_data[i].valid && !ex_ready_a[i]) begin // Following logic is masked if the entry is not valid
                    if (!rs_data[i].rs1_ready) begin
                        if (cdb_valid_i && !cdb_data_i.except_raised && (rs_data[i].rs1_idx == cdb_data_i.rob_idx)) begin
                            rs_data[i].rs1_ready    <= 'b1;
                            rs_data[i].rs1_value    <= cdb_data_i.value;
                        end
                    end
                    if (!rs_data[i].rs2_ready) begin
                        if (cdb_valid_i && !cdb_data_i.except_raised && (rs_data[i].rs2_idx == cdb_data_i.rob_idx)) begin
                            rs_data[i].rs2_ready    <= 'b1;
                            rs_data[i].rs2_value    <= cdb_data_i.value;
                        end
                    end
                end
            end

            // ---------------------
            // CONTROLLED OPERATIONS
            // ---------------------
            
            // Push a new instruction into the reservation station
            if (rs_push) begin
                rs_data[tail_idx].valid             <= issue_valid_i;
                rs_data[tail_idx].busy              <= 1'b0;
                rs_data[tail_idx].branch_type       <= branch_type_i;
                rs_data[tail_idx].rs1_ready         <= rs1_ready_i;
                rs_data[tail_idx].rs1_idx           <= rs1_idx_i;
                rs_data[tail_idx].rs1_value         <= rs1_value_i;
                rs_data[tail_idx].rs2_ready         <= rs2_ready_i;
                rs_data[tail_idx].rs2_idx           <= rs2_idx_i;
                rs_data[tail_idx].rs2_value         <= rs2_value_i;
                rs_data[tail_idx].imm_value         <= imm_value_i;
                rs_data[tail_idx].pred_pc           <= pred_pc_i;
                rs_data[tail_idx].pred_target       <= pred_target_i;
                rs_data[tail_idx].pred_taken        <= pred_taken_i;
                rs_data[tail_idx].res_idx           <= dest_idx_i;
                rs_data[tail_idx].res_ready         <= 1'b0;
            end

            // Send an instruction to the branch unit
            if (rs_ex) begin
                rs_data[ex_idx].busy                <= 1'b1; // mark the entry as busy so it's not selected again
            end

            // Save the result from the branch unit
            if (rs_wr_res) begin
                rs_data[wr_res_idx]                 <= 1'b0; // clear the busy bit
                rs_data[wr_res_idx].res_ready       <= 1'b1; // mark the entry as completed
                rs_data[wr_res_idx].mispredicted    <= mispredict_i; // misprediction info from the branch unit
            end

            // Send a result to the CDB
            if (rs_pop) begin
                rs_data[head_idx].valid             <= 1'b0; // clear valid bit, so the entry can be used fot new instructions
            end

        end 
    end

    // --------------------------
    // HEAD, EX AND TAIL POINTERS
    // --------------------------
    modn_counter #(.N(RS_DEPTH)) head_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (head_cnt_en),
        .clr_i      (head_cnt_clr),
        .count_o    (head_idx),
        .tc_o       ()              // Not needed
    );

    modn_counter #(.N(RS_DEPTH)) ex_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (ex_cnt_en),
        .clr_i      (ex_cnt_clr),
        .count_o    (ex_idx),
        .tc_o       ()              // Not needed
    );

    modn_counter #(.N(RS_DEPTH)) tail_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (tail_cnt_en),
        .clr_i      (tail_cnt_clr),
        .count_o    (tail_idx),
        .tc_o       ()              // Not needed
    );

    modn_counter #(.N(RS_DEPTH)) wr_res_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (wr_res_cnt_en),
        .clr_i      (wr_res_cnt_clr),
        .count_o    (wr_res_idx),
        .tc_o       ()              // Not needed
    );

    // -----------------
    // OUTPUT GENERATION
    // -----------------
    
    // To the branch unit
    assign bu_rs1_o                 = rs_data[ex_idx].rs1_value;
    assign bu_rs2_o                 = rs_data[ex_idx].rs2_value;
    assign bu_imm_o                 = rs_data[ex_idx].imm_value;
    assign bu_pred_pc_o             = rs_data[ex_idx].pred_pc;
    assign bu_pred_target_o         = rs_data[ex_idx].pred_target;
    assign bu_pred_taken_o          = rs_data[ex_idx].pred_taken;
    assign bu_branch_type_o         = rs_data[ex_idx].branch_type;

    // To the CDB
    assign cdb_data_o.rob_idx       = rs_data[head_idx].res_idx;
    assign cdb_data_o.value         = { {(XLEN-1){1'b0}}, rs_data[head_idx].mispredicted }; // store the misprediction information in the value field of the CDB (result field of the ROB)
    assign cdb_data_o.except_raised = 1'b0; // no exception can be raised  (Wrong, First check the Missp if ok then cheeck address misaglined)
    assign cdb_data_o.except_code   = E_UNKNOWN;

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    always @(negedge clk_i) begin
        // Notice when the reservation station is full
        //assert (valid_a == ((1 << RS_DEPTH) - 1)) else $warning("Generic RS full: you might want to increase its depth");
        foreach (rs_data[i]) begin
            // Check if the correct order of operations is respected
            assert (!(res_ready_a[i] && !ex_ready_a[i])) else `uvm_error("HAZARD", $sformatf("RS entry %4d has ready result before having ready operands. This should be impossible", i))
        end
    end
    `endif

endmodule
