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
// File: rob.sv
// Author: Michele Caon
// Date: 03/11/2019

// LEN5 compilation switches
`include "len5_config.svh"

import len5_pkg::XLEN;
import len5_pkg::ILEN;
import len5_pkg::REG_IDX_LEN;
import len5_pkg::ROB_DEPTH;
import len5_pkg::instr_t;
import expipe_pkg::*;

module rob 
(
    input   logic                       clk_i,
    input   logic                       rst_n_i,
    input   logic                       flush_i,

    // Handhsake from/to the issue stage
    input   logic                       issue_valid_i,
    output  logic                       issue_ready_o,

    // Data from/to the issue stage
    output  logic                       issue_rs1_ready_o,      // the result is ready
    input   logic [ROB_IDX_LEN-1:0]     issue_rs1_idx_i,        // ROB entry containing rs1 value 
    output  logic [XLEN-1:0]            issue_rs1_value_o,      // the value of the first operand
    output  logic                       issue_rs2_ready_o,      // the result is ready
    input   logic [ROB_IDX_LEN-1:0]     issue_rs2_idx_i,        // ROB entry containing rs2 value
    output  logic [XLEN-1:0]            issue_rs2_value_o,      // the value of the second operand

    input   instr_t                     issue_instr_i,         // to identify the instruction
    input   logic [XLEN-1:0]            issue_pc_i,             // the PC of the instruction being issued, needed for exception handling
    input   logic [REG_IDX_LEN-1:0]     issue_rd_idx_i,         // the destination register index (rd)
    input   logic                       issue_except_raised_i,  // an exception has been raised
    input   logic [ROB_EXCEPT_LEN-1:0]  issue_except_code_i,    // the exception code
    input   logic [XLEN-1:0]            issue_except_aux_i,     // exception auxilliary data (e.g. offending virtual address)
    input   logic                       issue_res_ready_i,      // to force result ready in special cases that are ready to commit from the issue phase
    input   logic [XLEN-1:0]            issue_res_value_i,

    output  logic [ROB_IDX_LEN-1:0]     issue_tail_idx_o,       // the ROB entry where the new instruction is being allocated

    // Handhsake from the CDB
    input   logic                       cdb_valid_i,
    output  logic                       cdb_ready_o,

    // Data from the CDB
    input cdb_data_t                    cdb_data_i,

    // Handshake from/to the committing logic
    input   logic                       comm_ready_i,
    output  logic                       comm_valid_o,

    // Data to the commit logic
    output  instr_t                     comm_instr_o,
    output  logic [XLEN-1:0]            comm_pc_o,
    output  logic [REG_IDX_LEN-1:0]     comm_rd_idx_o,          // the destination register (rd)
    output  logic [XLEN-1:0]            comm_value_o,           // the result of the instruction
    output  logic                       comm_except_raised_o,
	output  except_code_t               comm_except_code_o,
    output  logic [ROB_IDX_LEN-1:0]     comm_head_idx_o,        // ROB head idx to update register status

    // Data from/to the store buffer
    output  logic [ROB_IDX_LEN-1:0]     sb_head_idx_o           // the head index of the ROB
);

    // DEFINITIONS
    
    // Head and tail pointers
    logic [ROB_IDX_LEN-1:0]             rob_head_idx, rob_tail_idx;
    logic                               rob_tail_en1, rob_head_en, rob_head_clr, rob_tail_en, rob_tail_clr;

    // Operation control
    logic                               rob_push, rob_pop, rob_wr_res;

    // ROB data structure 
    rob_entry_t                         rob_data [0:ROB_DEPTH-1]; 

    // Status signals
    logic [0:ROB_DEPTH-1]               valid_a, res_ready_a;
    logic [ROB_EXCEPT_LEN-1:0]          comm_except_code_test;

    // --------------
    // STATUS SIGNALS
    // --------------
    // These are required because name selection after indexing is not supported
    always_comb begin: status_signals_gen
        for (int i = 0; i < ROB_DEPTH; i++) begin
            valid_a[i]          = rob_data[i].valid;
            res_ready_a[i]      = rob_data[i].res_ready;
        end
    end

    // -----------------
    // ROB CONTROL LOGIC
    // -----------------
    always_comb begin: rob_control_logic
        // DEFAULT VALUES
        // Operation control
        rob_push            = 1'b0;
        rob_pop             = 1'b0;
        rob_wr_res          = 1'b0;

        // Hanshake control
        issue_ready_o       = 1'b0;
        cdb_ready_o         = 1'b1; // Always ready to accept data from the CDB
        comm_valid_o        = 1'b0;

        // Head and tail counters control
        rob_head_en         = 1'b0; 
        rob_head_clr        = flush_i;     
        rob_tail_en         = 1'b0; 
        rob_tail_clr        = flush_i;    

        // --------------
        // ROB OPERATIONS
        // --------------
        
        // PUSH A NEW INSTRUCTION IN THE QUEUE
        if (!rob_data[rob_tail_idx].valid) begin
            issue_ready_o               = 1'b1; // tell the issue logic that an entry is valid
            if (issue_valid_i) begin
                rob_push                = 1'b1; // push the new instruction in
                rob_tail_en            = 1'b1; // increment the tail pointer
                //rob_tail_en             = rob_tail_en1;
            end
        end

        // WRITE THE DATA FROM THE CDB  
        if (cdb_valid_i) begin
            rob_wr_res                  = 1'b1; 
        end

        // POP THE HEAD ENTRY WHEN IT'S READY TO COMMIT
        if (rob_data[rob_head_idx].valid && rob_data[rob_head_idx].res_ready) begin
            comm_valid_o                = 1'b1; // tell the commit logic that an instruction is ready to commit
            if (comm_ready_i) begin
               rob_pop                  = 1'b1; // if the commit logic can accept the instruction, pop it
               rob_head_en              = 1'b1; // increment the head pointer 
            end
        end
    end
    
    // ---------------
    // ROB DATA UPDATE
    // ---------------
    always_ff @(posedge clk_i or negedge rst_n_i) begin: rob_data_update
        if (!rst_n_i) begin
            foreach (rob_data[i]) begin
                rob_data[i]                 <= 0;
            end
        end else if (flush_i) begin
            foreach (rob_data[i]) begin // clearing status bits is enough
                rob_data[i].valid           <= 1'b0;
                rob_data[i].res_ready       <= 1'b0;
                rob_data[i].except_raised   <= 1'b0;
            end
        end else begin // Normal operation
            
            // PUSH NEW INSTRUCTION INTO THE ROB (WRITE PORT 1)
            if (rob_push) begin
                rob_data[rob_tail_idx].valid            <= 1'b1;
                rob_data[rob_tail_idx].instruction      <= issue_instr_i;
                rob_data[rob_tail_idx].instr_pc         <= issue_pc_i;
                rob_data[rob_tail_idx].rd_idx           <= issue_rd_idx_i;
                rob_data[rob_tail_idx].except_raised    <= issue_except_raised_i;
                if (issue_except_raised_i) begin
                    rob_data[rob_tail_idx].res_value    <= issue_except_aux_i;  // copy auxiliary data in result field so they can be used at commit to handle the exception or special instr. tha don't have to wait for a result
                    rob_data[rob_tail_idx].except_code  <= issue_except_code_i;
                    rob_data[rob_tail_idx].res_ready    <= 1'b1;
                end else if (issue_res_ready_i) begin
                    rob_data[rob_tail_idx].res_value    <= issue_res_value_i;
                    rob_data[rob_tail_idx].res_ready    <= 1'b1;
                end else begin
                    rob_data[rob_tail_idx].res_ready    <= 1'b0;
                end
            end

            // WRITE THE DATA FROM THE CDB (WRITE PORT 2)
            if (rob_wr_res) begin
                rob_data[cdb_data_i.rob_idx].res_ready      <= 1'b1;
                rob_data[cdb_data_i.rob_idx].res_value      <= cdb_data_i.value;
                rob_data[cdb_data_i.rob_idx].except_raised  <= cdb_data_i.except_raised;
                rob_data[cdb_data_i.rob_idx].except_code    <= cdb_data_i.except_code;
            end

            // POP COMMITTED ENTRY
            if (rob_pop) rob_data[rob_head_idx].valid       <= 1'b0;

        end
    end

    // ----------------------
    // HEAD AND TAIL POINTERS
    // ----------------------
    modn_counter #(.N(ROB_DEPTH)) head_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (rob_head_en),
        .clr_i      (rob_head_clr),
        .count_o    (rob_head_idx),
        .tc_o       ()              // Not needed
    );

    modn_counter #(.N(ROB_DEPTH)) tail_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (rob_tail_en),
        .clr_i      (rob_tail_clr),
        .count_o    (rob_tail_idx),
        .tc_o       ()              // Not needed
    );

    // -------------------------------
    // ISSUE STAGE OPERANDS READ PORTS
    // -------------------------------
    // During issue, if the register status register reports that the result 
    // rs1 port
    assign issue_rs1_ready_o    = rob_data[issue_rs1_idx_i].res_ready;
    assign issue_rs1_value_o    = rob_data[issue_rs1_idx_i].res_value; // READ PORT 1 (res_value)
    // rs2 port
    assign issue_rs2_ready_o    = rob_data[issue_rs2_idx_i].res_ready;
    assign issue_rs2_value_o    = rob_data[issue_rs2_idx_i].res_value; // READ PORT 2 (res_value)

    // -----------------
    // OUTPUT EVALUATION
    // -----------------
    
    // To the store buffer
    assign sb_head_idx_o        = rob_head_idx;

    // To the issue stage
    assign issue_tail_idx_o     = rob_tail_idx;

    // To the commit logic
    assign comm_instr_o         = rob_data[rob_head_idx].instruction;
    assign comm_pc_o            = rob_data[rob_head_idx].instr_pc;
    assign comm_rd_idx_o        = rob_data[rob_head_idx].rd_idx;
    assign comm_value_o         = rob_data[rob_head_idx].res_value;
    assign comm_except_raised_o = rob_data[rob_head_idx].except_raised;
    assign comm_head_idx_o      = rob_head_idx;

	// Exception assignment
  always_comb begin
    case (comm_except_code_test)
      4'h0: 		comm_except_code_o = E_I_ADDR_MISALIGNED;
      4'h1:    		comm_except_code_o = E_I_ACCESS_FAULT;
      4'h2:      	comm_except_code_o = E_ILLEGAL_INSTRUCTION;
	  4'h3: 		comm_except_code_o = E_BREAKPOINT;
      4'h4:    		comm_except_code_o = E_LD_ADDR_MISALIGNED;
      4'h5:      	comm_except_code_o = E_LD_ACCESS_FAULT;
	  4'h6: 		comm_except_code_o = E_ST_ADDR_MISALIGNED;
      4'h7:    		comm_except_code_o = E_ST_ACCESS_FAULT;
      4'h8:      	comm_except_code_o = E_ENV_CALL_UMODE;
	  4'h9: 		comm_except_code_o = E_ENV_CALL_SMODE;
	  4'ha:      	comm_except_code_o = E_UNKNOWN;
      4'hb:    		comm_except_code_o = E_ENV_CALL_MMODE;
      4'hc:      	comm_except_code_o = E_INSTR_PAGE_FAULT;
	  4'hd: 		comm_except_code_o = E_LD_PAGE_FAULT;
      4'hf:    		comm_except_code_o = E_ST_PAGE_FAULT;
      default:    	comm_except_code_o = E_UNKNOWN;
    endcase
  end

endmodule
