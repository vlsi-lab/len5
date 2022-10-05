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
// File: int_regstat.sv
// Author: Michele Caon
// Date: 12/11/2019

/* Include UVM macros */
`ifndef SYNTHESIS
`include "uvm_macros.svh"
import uvm_pkg::*;
`endif

import expipe_pkg::*;

module int_regstat #( 
    REG_NUM = 32,                               // power of 2
    localparam  REG_IDX_LEN = $clog2(REG_NUM)   // not exposed
) (
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,

    // Issue Logic
    input   logic                   issue_valid_i,
    input   logic [REG_IDX_LEN-1:0] issue_rd_idx_i,         // destination register of the issuing instruction
    input   rob_idx_t               issue_rob_idx_i,  // ROB index where the instruction is being allocated (tail pointer of the ROB)
    input   logic [REG_IDX_LEN-1:0] issue_rs1_idx_i,        // first source register index
    input   logic [REG_IDX_LEN-1:0] issue_rs2_idx_i,        // second source register index
    output  logic                   issue_rs1_busy_o,       // rs1 value is in the ROB or has to be computed
    output  rob_idx_t               issue_rs1_rob_idx_o,    // the index of the ROB where the result is found
    output  logic                   issue_rs2_busy_o,       // rs1 value is in the ROB or has to be computed
    output  rob_idx_t               issue_rs2_rob_idx_o,    // the index of the ROB where the result is found

    // Commit Logic
    input   logic                   comm_valid_i,
    input   logic [REG_IDX_LEN-1:0] comm_rd_idx_i,          // destination register of the committing instr.
    input   rob_idx_t               comm_head_idx_i         // head entry of the ROB
);

    // INTERNAL SIGNALS
    // ----------------
    logic                       busy_rob_idx_upd;
    rob_idx_t                   busy_rob_idx[1:REG_NUM-1]; // newest ROB entry that is going to write rd
    logic                       busy_cnt_en[1:REG_NUM-1], busy_cnt_up[1:REG_NUM-1]; 
    logic                       busy_cnt_clr;
    logic [REGSTAT_CNT_W-1:0]   busy_cnt[1:REG_NUM-1];      // number of in-flight instructions writing rd
    logic                       skip_cnt_upd;

    // -----------------------------
    // REGISTER STATUS CONTROL LOGIC
    // -----------------------------
    assign  busy_rob_idx_upd    = issue_valid_i;
    assign  busy_cnt_clr        = flush_i;
    assign  skip_cnt_upd        = issue_valid_i && comm_valid_i && issue_rd_idx_i == comm_rd_idx_i;

    always_comb begin : busy_cnt_control
        foreach (busy_cnt[i]) begin
            busy_cnt_en[i]  = 1'b0;
            busy_cnt_up[i]  = 1'b0;
        end    

        // Only update the counters pointed by issue_rob_idx_i and 
        // comm_head_idx_i, and only if those signals differ
        if (!skip_cnt_upd) begin
            if (issue_valid_i) begin
                busy_cnt_en[issue_rd_idx_i] = 1'b1;
                busy_cnt_up[issue_rd_idx_i] = issue_valid_i;
            end 
            if (comm_valid_i) begin
                busy_cnt_en[comm_rd_idx_i]  = comm_valid_i;
            end
        end
    end

    // ---------------------------
    // REGISTER STATUS DATA UPDATE
    // ---------------------------
    always_ff @(posedge clk_i or negedge rst_n_i) begin: rs_data_update
        if (!rst_n_i) begin // Asynchronous reset
            foreach (busy_rob_idx[i]) begin
                busy_rob_idx[i] <= 0;
            end
        end else if (flush_i) begin // Normal update 
            foreach (busy_rob_idx[i]) begin
                busy_rob_idx[i] <= 0;
            end
        end else if (busy_rob_idx_upd) begin
            if (|issue_rd_idx_i) busy_rob_idx[issue_rd_idx_i] <= issue_rob_idx_i;
        end
    end

    // BUSY COUNTERS
    // -------------
    generate
        for (genvar i = 1; i < REG_NUM; i++) begin: l_busy_counters
            updown_counter #(
                .W (REGSTAT_CNT_W )
            ) u_rob_cnt (
            	.clk_i   (clk_i          ),
                .rst_n_i (rst_n_i        ),
                .en_i    (busy_cnt_en[i] ),
                .clr_i   (busy_cnt_clr   ),
                .up_dn_i (busy_cnt_up[i] ),
                .count_o (busy_cnt[i]    ),
                .tc_o    () // Not needed
            );
        end
    endgenerate

    // --------------------------
    // REGISTER STATUS READ PORTS
    // --------------------------
    always_comb begin : int_rs_out
        // rs1 status (READ PORT 1)
        if (|issue_rs1_idx_i) begin
            issue_rs1_busy_o    = |busy_cnt[issue_rs1_idx_i];
            issue_rs1_rob_idx_o = busy_rob_idx[issue_rs1_idx_i];
        end else begin
            issue_rs1_busy_o    = 1'b0;
            issue_rs1_rob_idx_o = '0;
        end

        // rs2 status (READ PORT 2)
        if (|issue_rs2_idx_i) begin
            issue_rs2_busy_o    = |busy_cnt[issue_rs2_idx_i];
            issue_rs2_rob_idx_o = busy_rob_idx[issue_rs2_idx_i];
        end else begin
            issue_rs2_busy_o    = 1'b0;
            issue_rs2_rob_idx_o = '0;
        end
    end

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    // The counter should never overflow
    property p_busy_cnt_overflow(i, en, cnt);
        @(posedge clk_i) disable iff (!rst_n_i)
        en && &cnt |-> ##1
        |cnt;
    endproperty
    generate
        for (genvar i=1; i < REG_NUM-1; i++) begin: l_assertion_gen
            a_busy_cnt_overflow: assert property (p_busy_cnt_overflow(i, busy_cnt_en[i], busy_cnt[i]))
            else `uvm_error("INT REGSTAT", $sformatf("busy count %0d overflow", i));
        end
    endgenerate
    `endif /* SYNTHESIS */
endmodule
