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
// File: issue_queue.sv
// Author: Michele Caon
// Date: 17/10/2019

`ifndef SYNTHESIS
// Include packages
`include "len5_pkg.sv"
`include "expipe_pkg.sv"
`endif

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/util/modn_counter.sv"
`include "0_issue_queue_fifo.sv"
//`include "issue_queue_fifo.sv"

import len5_pkg::XLEN;
import len5_pkg::ILEN;
import len5_pkg::IQ_DEPTH;

import expipe_pkg::*;

module issue_queue (
    input   logic               clk_i,
    input   logic               rst_n_i,
    input   logic               flush_i,
	//input   logic					stall,

    // Handshake from/to fetch unit
    input   logic               fetch_valid_i,
    output  logic               fetch_ready_o,

    // Data from fetch unit
    input   logic [XLEN-1:0]    curr_pc_i,
    input   logic [ILEN-1:0]    instruction_i,
    input   logic [XLEN-1:0]    pred_target_i,
    input   logic               pred_taken_i,
    input   logic               except_raised_i,
    input   except_code_t       except_code_i,

    // Handshake from/to the issue logic
    input   logic               issue_ready_i,
    output  logic               issue_valid_o,

    // Data to the execution pipeline
    output  logic [XLEN-1:0]    curr_pc_o,
    output  logic [ILEN-1:0]    instruction_o,
    output  logic [XLEN-1:0]    pred_target_o,
    output  logic               pred_taken_o,
    output  logic               except_raised_o,
    output  except_code_t       except_code_o
);

    // DEFINITIONS
    // Head and tail pointers 
    logic [IQ_IDX_LEN-1:0]      head_idx, tail_idx;

    // New instruction 
    iq_entry_t                  new_entry, issued_instr;

    // Pointers control
    logic                       head_cnt_en, tail_cnt_en;
    logic                       head_cnt_clr, tail_cnt_clr;

    //----------------------------------\\
    //----- HEAD AND TAIL POINTERS -----\\
    //----------------------------------\\
    
    modn_counter #(.N(IQ_DEPTH)) head_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (head_cnt_en),
        .clr_i      (head_cnt_clr),
        .count_o    (head_idx),
        .tc_o       () // Not needed
    );

    modn_counter #(.N(IQ_DEPTH)) tail_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (tail_cnt_en),
        .clr_i      (tail_cnt_clr),
        .count_o    (tail_idx),
        .tc_o       () // Not needed
    );

    //----------------------------\\
    //----- ISSUE QUEUE FIFO -----\\
    //----------------------------\\
    // Assemble new queue entry with the data from the fetch unit
    assign new_entry.valid          = fetch_valid_i;
    assign new_entry.curr_pc        = curr_pc_i;
    assign new_entry.instruction    = instruction_i;
    assign new_entry.pred_target    = pred_target_i;
    assign new_entry.pred_taken     = pred_taken_i;
    assign new_entry.except_raised  = except_raised_i;
    assign new_entry.except_code    = except_code_i;

    issue_queue_fifo u_issue_queue_fifo 
    (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .flush_i        (flush_i),
		//.stall			(stall),

        .fetch_valid_i  (fetch_valid_i),
        .fetch_ready_o  (fetch_ready_o),

        .issue_ready_i  (issue_ready_i),
        .issue_valid_o  (issue_valid_o),

        .new_entry      (new_entry),
        .issued_instr   (issued_instr),

        .head_idx       (head_idx),
        .tail_idx       (tail_idx),
        .head_cnt_en    (head_cnt_en),
        .tail_cnt_en    (tail_cnt_en),
        .head_cnt_clr   (head_cnt_clr),
        .tail_cnt_clr   (tail_cnt_clr)
    );

    // Unpack issued instruction for the ex. pipeline
    assign curr_pc_o        = issued_instr.curr_pc;
    assign instruction_o    = issued_instr.instruction; 
    assign pred_target_o    = issued_instr.pred_target;
    assign pred_taken_o     = issued_instr.pred_taken;
    assign except_raised_o  = issued_instr.except_raised;
    assign except_code_o    = issued_instr.except_code;

endmodule

