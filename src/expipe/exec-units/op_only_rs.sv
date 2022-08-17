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
// File: op_only_rs.sv
// Author: Michele Caon
// Date: 17/11/2021

// Import UVM report macros
`include "uvm_macros.svh"
import uvm_pkg::*;

import len5_pkg::*;
import expipe_pkg::*;

module op_only_rs
#(
    RS_DEPTH = 4,   // must be a power of 2

    // EU-specific parameters
    EU_CTL_LEN = 2
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
    // input   logic [OP_ONLY_CTL_LEN-1:0]    ctl_i,
    input   logic                           rs1_ready_i,
    input   rob_idx_t         rs1_idx_i,
    input   logic [XLEN-1:0]                rs1_value_i,
    input   rob_idx_t         dest_idx_i,

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

    // Reservation station entry 
    typedef struct packed {
        logic                   valid;      // The entry contains a valid instruction
        logic                   rs1_ready;  // The first operand value is available in 'rs1_value'
        rob_idx_t rs1_idx;    // The entry of the rob that will contain the required operand. This can be fetched as soon as it appears on the CDB (when the EU produces it).
        logic [XLEN-1:0]        rs1_value;  // The value of the first operand
        rob_idx_t dest_idx;   // The entry of the ROB assigned to the current instruction
    } rs_entry_t;

    // Reservation station pointers
    logic [RS_IDX_LEN-1:0]      tail_idx, ex_idx, head_idx, wr_res_idx; 

    // Head, ex and tail counters
    logic                       head_cnt_en, head_cnt_clr, tail_cnt_en, tail_cnt_clr;

    // The actual reservation station data structure
    rs_entry_t  rs_data[0:RS_DEPTH-1];
    
    // Status signals
    logic   valid_a[0:RS_DEPTH-1]; // valid entries, empty entries
    logic   res_ready_a[0:RS_DEPTH-1]; // Ready operands / ready result entries 

    // RS control signals
    logic                       rs_push, rs_pop;

    // --------------
    // STATUS SIGNALS
    // --------------
    // These are required because name selection after indexing is not supported
    always_comb begin
        for (int i = 0; i < RS_DEPTH; i++) begin
            // Valid array
            valid_a[i]      = rs_data[i].valid;
            
            // Result ready entries
            res_ready_a[i]  = rs_data[i].rs1_ready & rs_data[i].valid;
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
        tail_cnt_en         = 1'b0;
        tail_cnt_clr        = flush_i;

        // Operation control
        rs_push             = 1'b0;
        rs_pop              = 1'b0;

        // Handshake control 
        issue_ready_o       = 1'b0;
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

        // WRITE HEAD RESULT ON THE CDB AND POP THE INSTRUCTION
        if (res_ready_a[head_idx]) begin
            cdb_valid_o            = 1'b1;
            if (cdb_ready_i) begin
                rs_pop             = 1'b1; // if the CDB can accept outcoming data, 
                head_cnt_en        = 1'b1;
            end
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
                rs_data[i].rs1_ready        <= 'b0;
            end
        end else begin // Normal update

            // -------------------
            // PARALLEL OPERATIONS
            // -------------------
            // Retrieve operands from CDB (PARALLEL WRITE PORT 1)
            foreach (rs_data[i]) begin
                if (rs_data[i].valid && !res_ready_a[i]) begin // Following logic is masked if the entry is not valid
                    if (!rs_data[i].rs1_ready) begin
                        if (cdb_valid_i && !cdb_data_i.except_raised && (rs_data[i].rs1_idx == cdb_data_i.rob_idx)) begin
                            rs_data[i].rs1_ready    <= 'b1;
                            rs_data[i].rs1_value    <= cdb_data_i.value;
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
                rs_data[tail_idx].rs1_ready         <= rs1_ready_i;
                rs_data[tail_idx].rs1_idx           <= rs1_idx_i;
                rs_data[tail_idx].rs1_value         <= rs1_value_i;
                rs_data[tail_idx].dest_idx          <= dest_idx_i;
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

    // To the CDB
    assign cdb_data_o.rob_idx       = rs_data[head_idx].dest_idx;
    assign cdb_data_o.res_value     = rs_data[head_idx].rs1_value; // for CSR instructions
    assign cdb_data_o.res_aux       = '0;
    assign cdb_data_o.except_raised = 1'b0; // no exception can be raised  (Wrong, First check the Missp if ok then cheeck address misaglined)
    assign cdb_data_o.except_code   = E_UNKNOWN;

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    // Check that assigned instructions are missing their operand
    property p_op_not_ready;
        @(posedge clk_i) disable iff (!rst_n_i)
        issue_valid_i |-> !rs1_ready_i;
    endproperty
    a_op_not_ready: assert property (p_op_not_ready);
    `endif

endmodule
