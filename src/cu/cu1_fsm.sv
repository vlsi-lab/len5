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
// File: cu1_fsm.sv
// Author: WALID
// Date: 07/10/2019

/* Include instruction definitions */
`include "instr_macros.svh"

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module cu1_fsm
(
	// From :TB
  	input   logic             	clk_i,
  	input   logic             	rst_n_i,
	// To all
  	output  logic             	flush_i,

	// For back end :CU
  	output  satp_mode_t       	vm_mode_i,

	// To the main control :CU 
  	input  	logic             	main_cu_stall_o,
	input   logic [ILEN-1:0] 	ins_in,
	output  logic 				stall,
	//input 	logic 				commit_possible,
	//output 	logic 				commit_ready,
	// Data for execution unit :CU
    output  branch_type_t     	branch_type_i,
  	output  ldst_type_t       	ldst_type_i,

  	// From/to i-cache  :I$
 	input  	logic             	data_ready_o,
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	//input   logic             	except_i,
  	//input   logic [XLEN-1:0]  	except_pc_i,

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	input   logic             	except_raised_i,
  	input   except_code_t     	except_code_i,

	//input   logic 				commit_head_cnt,
	input   logic [ROB_IDX_LEN-1:0]	commit_head_cnt,

	// From main unit
   	output  logic               abort_i,
   	output  logic               clr_l1tlb_mshr_i,
   	output  logic               clr_l2tlb_mshr_i,
   	output  logic               clear_dmshr_dregs_i, 

	// Update Block <-> d-Cache Updating Unit
  	output  logic               synch_l1dc_l2c_i,
  	input   logic               l2c_update_done_o,

 	 // System -> TLBs/PTW
  	output  logic               vmem_on_i,
  	output  logic               sum_bit_i,
  	output  logic               mxr_bit_i,
 	output  priv_e              priv_mode_i,
  	output  priv_e              priv_mode_ls_i,
  	output  asid_t              base_asid_i,
  	output  logic [PPN_LEN-1:0] csr_root_ppn_i,
  	output  tlb_flush_e         L1TLB_flush_type_i,
  	output  tlb_flush_e         L2TLB_flush_type_i,
  	output  asid_t              flush_asid_i,
 	output  vpn_t               flush_page_i,
	
	// LSQ <-> d-TLB
  	input 	logic               dtlb_lsq_req_rdy_o,

  	// LSQ <-> d-Cache
 	input 	logic               l1dc_lsq_req_rdy_o,
 
  	// L2 Cache Arbiter <-> L2 Cache Emulator
	//output 	l2arb_l2c_req_t     l2arb_l2c_req_o,
  	input   logic               l2c_l2arb_req_rdy_i,
  	input   var l2c_l2arb_ans_t     l2c_l2arb_ans_i//,
  	//output 	logic               l2arb_l2c_ans_rdy_o 
);

	logic [OPCODE_LEN -1:0]        instr_opcode;
    logic [FUNCT3_LEN -1:0]        instr_funct3;

	assign 	vm_mode_i		= 	SV39;
	assign instr_opcode     = 	ins_in[OPCODE_LEN-1 : 0];
    assign instr_funct3     = 	ins_in[14 -: FUNCT3_LEN];

	assign vmem_on_i  		= 	0;		// Virtual memory is on
	assign sum_bit_i  		= 	1;		// For user mode 
  	assign mxr_bit_i  		= 	0;		// Only readible
 	assign priv_mode_i  	= 	U;		// User
  	assign priv_mode_ls_i  	= 	U;		// User
	assign base_asid_i  	= 	'd0;	// Root page address
  	assign csr_root_ppn_i  	= 	'd0;	// Root physical address

	typedef enum logic [3:0] { RESET, RESUME_STATE, JUMP_STATE, LD_ST_STATE, BRANCH_STATE, FENCE_STATE, WAIT_STATE, S_STATE, M_STATE, U_STATE, E_BREAK_STATE } state_t;
  	state_t present_state, next_state;

  // State transition
  	always_ff @ (posedge clk_i or negedge rst_n_i) begin
    // Async reset
    	if (!rst_n_i) begin
      		present_state 	<= 	RESET;
    	//end else begin
    	//if (flush_i) begin
        	//present_state 	<= 	RESUME_STATE;
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
        	next_state 	= 	RESUME_STATE;
      	end

      	RESUME_STATE: begin  // Fix these are just states move it to output
			//if 		((!except_i || !except_raised_i) && (instr_opcode == `OPCODE_BEQ || instr_opcode == `OPCODE_LB || instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA)) begin
            	//	next_state 	= 	RESUME_STATE;
    		//end
			if 		((/*!except_i ||*/ !except_raised_i) && (instr_opcode == `OPCODE_BEQ || instr_opcode == `OPCODE_LB || instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA)) begin
            		next_state 	= 	RESUME_STATE;
    		end
			else if (except_raised_i && instr_opcode == `OPCODE_JAL) begin
            		next_state 	= 	JUMP_STATE;
    		end
			else if (except_raised_i && instr_opcode == `OPCODE_LB) begin
            		next_state 	= 	LD_ST_STATE;
    		end
			else if (instr_opcode == `OPCODE_BEQ && except_raised_i) begin//misprediction) begin// WALID fix it how misprediction is detected, for now use exception
            		next_state 	= 	BRANCH_STATE;
    		end
			else if (instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA) begin
            		next_state 	= 	FENCE_STATE;
    		end
			//else if (wait_move && (!l2c_update_done_o)) begin
            	//	next_state 	= 	WAIT_STATE;
    		//end
			else if (instr_opcode == `OPCODE_ECALL && instr_funct3 == `FUNCT3_ECALL) begin//Fix for E-CALL_S see how
            		next_state 	= 	S_STATE;
    		end
			else if (instr_opcode == `OPCODE_ECALL && instr_funct3 == `FUNCT3_ECALL) begin
            		next_state 	= 	M_STATE;
    		end
			else if (instr_opcode == `OPCODE_ECALL && instr_funct3 == `FUNCT3_ECALL) begin
            		next_state 	= 	U_STATE;
    		end
			else if (instr_opcode == `OPCODE_EBREAK) begin
            		next_state 	= 	E_BREAK_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end

      	JUMP_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	JUMP_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end

      	LD_ST_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	LD_ST_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end
	
		BRANCH_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	BRANCH_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end

		FENCE_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	WAIT_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end

      	S_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	S_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end
	
		M_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	M_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end

		U_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	U_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end
	
		E_BREAK_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	E_BREAK_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end

		WAIT_STATE: begin
        	if (except_raised_i) begin
            		next_state 	= 	WAIT_STATE;
    		end
			else  begin
            		next_state 	= 	RESUME_STATE;
    		end
      	end
    	endcase
  	end
	// Output update
  	always_comb begin
    // Defaults
    	branch_type_i			=	BEQ;
		ldst_type_i				=	LS_WORD;
		flush_i 				= 	0;
		stall	 				= 	0;
		abort_i  				= 	0;
   		clr_l1tlb_mshr_i  		= 	0;
   		clr_l2tlb_mshr_i  		= 	0;
   		clear_dmshr_dregs_i 	= 	0; 
		synch_l1dc_l2c_i  		= 	0;
		L1TLB_flush_type_i		= 	NoFlush;
  		L2TLB_flush_type_i  	= 	NoFlush;
  		flush_asid_i  			= 	'd0;
 		flush_page_i  			= 	'd0;

    case (present_state)
      	RESET: begin
        	flush_i 				= 	1;
			stall	 				= 	0;//should it be 1 ?
			abort_i  				= 	0;
   			clr_l1tlb_mshr_i  		= 	1;
   			clr_l2tlb_mshr_i  		= 	1;
   			clear_dmshr_dregs_i 	= 	1; 
			synch_l1dc_l2c_i  		= 	0;
			L1TLB_flush_type_i		= 	FlushAll;//NoFlush;
  			L2TLB_flush_type_i  	= 	FlushAll;//NoFlush;
  			flush_asid_i  			= 	'd0;
 			flush_page_i  			= 	'd0;
      	end

      	RESUME_STATE: begin  
			if 		(instr_opcode == `OPCODE_BEQ) begin
      
    		end
			else if (instr_opcode == `OPCODE_LB) begin
            	
    		end
			else if ((instr_opcode == `OPCODE_FENCE) && (instr_funct3 == `FUNCT3_FENCE_I)) begin
            		clr_l1tlb_mshr_i  		= 	1;
					clr_l2tlb_mshr_i  		= 	1;
    		end
			else if ((instr_opcode == `OPCODE_SFENCE_VMA) && (instr_funct3 == `FUNCT3_SFENCE_VMA) && (!l2c_update_done_o)) begin//Fix
            		clr_l1tlb_mshr_i  		= 	1;
					clr_l2tlb_mshr_i  		= 	1;
					clear_dmshr_dregs_i 	= 	1;
					synch_l1dc_l2c_i  		= 	1;
    		end
			else  begin
            		abort_i  				= 	0;////Just this
   					clr_l1tlb_mshr_i  		= 	0;
   					clr_l2tlb_mshr_i  		= 	0;
   					clear_dmshr_dregs_i 	= 	0; 
					synch_l1dc_l2c_i  		= 	0;
					//ldst_type_i			=	LS_WORD;
					//branch_type_i			=	beq;
    		end
      	end

      	JUMP_STATE: begin//Flush pipe and abort and disable the commit  reg 
       	 			stall	 				= 	1;
					L1TLB_flush_type_i		= 	FlushASID;
					L2TLB_flush_type_i		= 	FlushASID;
					flush_asid_i  			= 	'd0;
      	end

      	LD_ST_STATE: begin //Flush pipe and abort and disable the commit  reg
			if (commit_head_cnt == 3'b111) begin
					flush_i 				= 	1;
			end else begin
					flush_i 				= 	0;
			end
			case (except_code_i)
				E_INSTR_PAGE_FAULT,E_I_ADDR_MISALIGNED,E_I_ACCESS_FAULT: begin 
					clr_l1tlb_mshr_i  		= 	1;
					clr_l2tlb_mshr_i  		= 	1;
				end
				E_LD_PAGE_FAULT,E_LD_ADDR_MISALIGNED,E_LD_ACCESS_FAULT,E_ST_PAGE_FAULT,E_ST_ADDR_MISALIGNED,E_ST_ACCESS_FAULT: begin 
					clear_dmshr_dregs_i 	= 	1;
				end	
        		E_ILLEGAL_INSTRUCTION: begin 
					abort_i  				= 	1;
					//stall	 				= 	1;
				end
				E_ENV_CALL_SMODE,E_ENV_CALL_MMODE: begin //Remove
					if (!l2c_update_done_o) begin
						synch_l1dc_l2c_i  		= 	1;
					end else begin
						synch_l1dc_l2c_i  		= 	0;
					end
					//stall	 				= 	1;
				end
				default: begin
					//stall	 				= 	0;
					//flush_i	 			= 	0; 
					abort_i  				= 	0;
   					clr_l1tlb_mshr_i  		= 	0;
   					clr_l2tlb_mshr_i  		= 	0;
   					clear_dmshr_dregs_i 	= 	0; 
					synch_l1dc_l2c_i  		= 	0;
				end
      		endcase
		end

		BRANCH_STATE: begin
       	 			stall	 				= 	1;//Flush pipe and abort
					L1TLB_flush_type_i		= 	FlushASID;
					L2TLB_flush_type_i		= 	FlushASID;
					flush_asid_i  			= 	'd0;
      	end

		FENCE_STATE: begin//Stall and Flush pipe and memory
       	 			stall	 				= 	1;
					L1TLB_flush_type_i		= 	FlushASID;
					L2TLB_flush_type_i		= 	FlushASID;
					flush_asid_i  			= 	'd0;
      	end

		S_STATE: begin //Enble commit reg
       	 			stall	 				= 	1;
					L1TLB_flush_type_i		= 	FlushASID;
					L2TLB_flush_type_i		= 	FlushASID;
					flush_asid_i  			= 	'd0;
      	end

		M_STATE: begin //Enble commit reg
       	 			stall	 				= 	1;
					L1TLB_flush_type_i		= 	FlushASID;
					L2TLB_flush_type_i		= 	FlushASID;
					flush_asid_i  			= 	'd0;
      	end

		U_STATE: begin
       	 			stall	 				= 	1;
					L1TLB_flush_type_i		= 	FlushASID;
					L2TLB_flush_type_i		= 	FlushASID;
					flush_asid_i  			= 	'd0;
      	end

		E_BREAK_STATE: begin
       	 			stall	 				= 	1;
					L1TLB_flush_type_i		= 	FlushASID;
					L2TLB_flush_type_i		= 	FlushASID;
					flush_asid_i  			= 	'd0;
      	end

		WAIT_STATE: begin
       	 			stall	 				= 	1;
					L1TLB_flush_type_i		= 	FlushASID;
					L2TLB_flush_type_i		= 	FlushASID;
					flush_asid_i  			= 	'd0;
      	end

      	//BRANCH_STATE: begin
      	//end
    	endcase
  	end

//-----

endmodule
