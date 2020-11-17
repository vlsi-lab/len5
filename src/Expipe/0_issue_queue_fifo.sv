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
// File: issue_queue_fifo.sv
// Author: Michele Caon
// Date: 19/10/2019

`ifndef SYNTHESIS
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/len5_pkg.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/expipe_pkg.sv"
`endif

import len5_pkg::IQ_DEPTH;
import expipe_pkg::*;

module issue_queue_fifo (
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,
	//input   logic					stall,

    // Handshake from/to fetch unit
    input   logic                   fetch_valid_i,
    output  logic                   fetch_ready_o,

    // Handshake from/to the execution pipeline
    input   logic                   issue_ready_i,
    output  logic                   issue_valid_o,

    // New entry data (from fetch unit)
    input   iq_entry_t              new_entry,

    // Issued entry
    output  iq_entry_t              issued_instr,

    // Issue queue internal signals
    input   logic [IQ_IDX_LEN-1:0]  head_idx,
    input   logic [IQ_IDX_LEN-1:0]  tail_idx,
    output  logic                   head_cnt_en,
    output  logic                   tail_cnt_en,
    output  logic                   head_cnt_clr,
    output  logic                   tail_cnt_clr
);

    // DEFINITIONS 
    logic                       fifo_push, fifo_pop;
    logic                       fifo_full;
    logic [0:IQ_DEPTH-1]        valid_a;

    iq_entry_t [0: IQ_DEPTH-1]  iq_fifo; // The actual fifo

    // full and empty fifo signals
    always_comb begin
        // This is required because fifo_full = &iq_fifo[0:IQ_DEPTH-1].valid is not accepted
        foreach (iq_fifo[i]) valid_a[i] = iq_fifo[i].valid; 
    end
    assign fifo_full = &valid_a; // 1 if all entries are valid
    
    //----------------------------\\
    //----- POINTERS CONTROL -----\\
    //----------------------------\\
    always_comb begin: idx_control_logic
        // Default values
        head_cnt_en     = 'b0;
        tail_cnt_en     = 'b0;
        
        head_cnt_clr    = flush_i;
        tail_cnt_clr    = flush_i;
        
        if (issue_valid_o && issue_ready_i /* && !(stall)*/) begin
            head_cnt_en = 'b1; // Pop
        end
        if (fetch_valid_i && fetch_ready_o /* && !(stall)*/) begin
            tail_cnt_en = 'b1; // Push
        end
    end

    //------------------------\\
    //----- FIFO CONTROL -----\\
    //------------------------\\
    always_comb begin: fifo_control_logic
        // Default values
        fifo_push           = 'b0;
        fifo_pop            = 'b0;
        issue_valid_o       = 'b0;
        fetch_ready_o       = 'b0;

        if (iq_fifo[head_idx].valid) begin
            // If the head entry is valid, notice the execution pipeline
            issue_valid_o      = 'b1;
            // If the execution pipeline can accept the issued instruction, then pop it
            if (issue_ready_i) fifo_pop = 'b1;
        end
        
        if ((!fifo_full) || (iq_fifo[head_idx].valid && issue_ready_i)) begin
            // If the issue queue has empty entries or if it's full and an instruction is being issued and popped, then tell the fetch unit that a new instruction can be pushed in the issue queue
            fetch_ready_o   = 'b1;
            // If the data from the fetch unit is valid, then push the new instruction in the queue
            if (fetch_valid_i) fifo_push = 'b1;
        end
    end

    //-----------------------\\
    //----- FIFO UPDATE -----\\
    //-----------------------\\
    always_ff @(posedge clk_i or negedge rst_n_i) begin: fifo_update
        if (!rst_n_i) begin // Asynchronous reset
            foreach (iq_fifo[i]) begin
                iq_fifo[i]          <= 0;
            end
        end else if (flush_i) begin // Synchronous flush
            foreach (iq_fifo[i]) begin
                iq_fifo[i].valid    <= 'b0; // clearing the valid field is necessary and sufficient
            end
		//end else if (stall) begin
			//;
        end else begin // Normal update (pop and/or push an instruction)
            if (fifo_pop) iq_fifo[head_idx].valid   <= 'b0; // Pop the fetched entry
            if (fifo_push) iq_fifo[tail_idx]        <= new_entry; // Push new instruction WRITE PORT 1
        end
    end 

    //----------------------------------\\
    //----- OUTPUT DATA EVALUATION -----\\
    //----------------------------------\\ 
    // Issued instruction (to execution pipeline)
    assign issued_instr     = iq_fifo[head_idx]; // READ PORT 1

    //---------------------\\
    //----- ASSERTION -----\\
    //---------------------\\
    `ifndef SYNTHESIS
    always @(negedge clk_i) begin
        // Notice when the issue queue is full
        assert (fifo_full !== 'b1) else $warning("The issue queue is full. You might want to increase its size");
    end
    `endif

endmodule
