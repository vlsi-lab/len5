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
// File: main_cu.sv
// Author: WALID
// Date: 07/10/2019

/* Include instruction definitions */
`include "instr_macros.svh"

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module main_cu
(
	// From :TB
  	input   logic             	clk_i,
  	input   logic             	rst_n_i,

	// From fontend
	input   logic [ILEN-1:0] 	fe_ins_i,
  	input   logic             	fe_except_raised_i,
	// From backend
  	input  	logic             	be_stall_i,
  	input  	logic             	be_resume_i,
	input 	logic 				be_flush_i,

	// To others
	output  logic 				stall_o,
	output 	logic 				flush_o,

	// To memory
	input  	logic 				mem_l2c_update_done,
	output 	logic				mem_flush_o,
	output 	logic 				mem_abort_o,
	output 	logic 				mem_clr_l1tlb_mshr,
	output 	logic 				mem_clr_l2tlb_mshr,
	output 	logic 				mem_clear_dmshr_dregs,
	output 	logic 				mem_synch_l1dc_l2c,
	output 	tlb_flush_e 		mem_L1TLB_flush_type,
	output 	tlb_flush_e 		mem_L2TLB_flush_type,
	output 	asid_t 				mem_flush_asid,
	output 	vpn_t 				mem_flush_page
);

	logic [OPCODE_LEN -1:0]        instr_opcode;
    logic [FUNCT3_LEN -1:0]        instr_funct3;

	assign instr_opcode     = 	fe_ins_i[OPCODE_LEN-1 : 0];
    assign instr_funct3     = 	fe_ins_i[14 -: FUNCT3_LEN];

	typedef enum logic [2:0] { RESET, OP_STATE, EXCEPT_I_MEM_STAGE, EXCEPT_RAISE_STAGE, STALL_STAGE } state_t;
  	state_t present_state, next_state;

  // State transition
  	always_ff @ (posedge clk_i or negedge rst_n_i) begin
    // Async reset
    	if (!rst_n_i) begin
      		present_state 	<= 	RESET;
    	//end else begin
    	//if (flush_i) begin
        	//present_state 	<= 	OP_STATE;
    	end else begin
        	present_state 	<= 	next_state;
    	end
    	//end
  	end

  	// State update
  	always_comb begin
    // Defaults
    	next_state 	= 	RESET;

    case (present_state)
      	RESET: begin
        	next_state 	= 	OP_STATE;
      	end

      	OP_STATE: begin  // Fix these are just states move it to output
			if 		((/*!except_i ||*/ !fe_except_raised_i) && (instr_opcode == `OPCODE_BEQ || instr_opcode == `OPCODE_LB || instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA)) begin
            		next_state 	= 	OP_STATE;
    		end
			//else if (except_i) begin
            	//	next_state 	= 	EXCEPT_I_MEM_STAGE;
    		//end
			else if (fe_except_raised_i) begin
            		next_state 	= 	EXCEPT_RAISE_STAGE;
    		end
			else  begin
            		next_state 	= 	OP_STATE;
    		end
      	end

      	EXCEPT_I_MEM_STAGE: begin
        if 		((/*!except_i ||*/ !fe_except_raised_i) && (instr_opcode == `OPCODE_BEQ || instr_opcode == `OPCODE_LB || instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA)) begin
            		next_state 	= 	OP_STATE;
    		end
			/*else if (except_i) begin
            		next_state 	= 	EXCEPT_I_MEM_STAGE;
    		end*/
			else if (fe_except_raised_i) begin
            		next_state 	= 	EXCEPT_RAISE_STAGE;
    		end
			else  begin
            		next_state 	= 	OP_STATE;
    		end
      	end

      	EXCEPT_RAISE_STAGE: begin
        	if 		((/*!except_i ||*/ !fe_except_raised_i) && (instr_opcode == `OPCODE_BEQ || instr_opcode == `OPCODE_LB || instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA)) begin
            		next_state 	= 	OP_STATE;
    		end
			/*else if (except_i) begin
            		next_state 	= 	EXCEPT_I_MEM_STAGE;
    		end*/
			else if (fe_except_raised_i) begin
            		next_state 	= 	EXCEPT_RAISE_STAGE;
    		end
			else  begin
            		next_state 	= 	OP_STATE;
    		end
      	end
    	endcase
  	end
	// Output update
  	always_comb begin
		stall_o	 				= 	0;

    case (present_state)
      	RESET: begin
        	//flush_i 				= 	1;
			stall_o	 				= 	0;//should it be 1 ?
      	end

      	OP_STATE: begin  
			if ((instr_opcode == `OPCODE_FENCE) && (instr_funct3 == `FUNCT3_FENCE_I)) begin
            	
    		end
			else if ((instr_opcode == `OPCODE_SFENCE_VMA) && (instr_funct3 == `FUNCT3_SFENCE_VMA) /*&& (!l2c_update_done_o)*/) begin//Fix
            		
    		end
			else  begin
   
    		end
      	end

      	EXCEPT_I_MEM_STAGE: begin
       	 			stall_o	 				= 	1;
      	end

      	EXCEPT_RAISE_STAGE: begin
	
      	end

      	//STALL_STAGE: begin
      	//end
    	endcase
  	end

	// TODO: properly handle flush signals
	assign 	flush_o		= be_flush_i;

	// TODO: properly handle memory control
	assign 	mem_flush_o				= 1'b0;
	assign 	mem_abort_o				= 1'b0;
	assign 	mem_clr_l1tlb_mshr		= 1'b0;
	assign 	mem_clr_l2tlb_mshr		= 1'b0;
	assign 	mem_clear_dmshr_dregs	= 1'b0;
	assign 	mem_synch_l1dc_l2c		= 1'b0;
	assign 	mem_L1TLB_flush_type	= NoFlush;
	assign 	mem_L2TLB_flush_type    = NoFlush;
	assign 	mem_flush_asid          = 'h0;
	assign 	mem_flush_page          = 'h0;

//-----

endmodule
