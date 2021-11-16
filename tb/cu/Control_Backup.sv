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
// File: fetch_stage.sv
// Author: Marco Andorno
// Date: 07/10/2019

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module Control
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

  	// From/to i-cache  :I$
 	input  	logic             	data_ready_o,
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	input   logic             	except_i,
  	input   logic [XLEN-1:0]  	except_pc_i,

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	input   logic             	except_raised_i,
  	input   except_code_t     	except_code_i,

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
	output 	l2arb_l2c_req_t     l2arb_l2c_req_o,
  	input   logic               l2c_l2arb_req_rdy_i,
  	input   l2c_l2arb_ans_t     l2c_l2arb_ans_i,
  	output 	logic               l2arb_l2c_ans_rdy_o 
);

	logic [OPCODE_LEN -1:0]        instr_opcode;
    logic [FUNCT3_LEN -1:0]        instr_funct3;

	assign 	vm_mode_i		= 	SV39;
	assign instr_opcode     = 	ins_in[OPCODE_LEN-1 : 0];
    assign instr_funct3     = 	ins_in[14 -: FUNCT3_LEN];

	assign vmem_on_i  		= 	1;		// Virtual memory is on
	assign sum_bit_i  		= 	1;		// For user mode 
  	assign mxr_bit_i  		= 	0;		// Only readible
 	assign priv_mode_i  	= 	U;		// User
  	assign priv_mode_ls_i  	= 	U;		// User
	assign base_asid_i  	= 	'd0;	// Root page address
  	assign csr_root_ppn_i  	= 	'd0;	// Root physical address

	// Flush_Pipeline logic
	always_ff @(posedge clk_i or negedge rst_n_i) begin: flush_PIPE_update

	if (!rst_n_i) begin // Asynchronous reset     
        	flush_i 			= 	0;
			stall	 			= 	0;
    end
	else if (main_cu_stall_o) begin
   			stall	 			= 	1;
    end
	else if (except_i) begin
			stall	 			= 	1;
    end
	else if (except_rasied_i /* && (commit_head_cnt)*/) begin
			flush_i 			= 	1;
			//stall	 			= 	1;
    end
	else  begin
            flush_i 			= 	0;
			stall	 			= 	0;
    end
	end

       // E_BREAKPOINT          = 4'h3,	// Not used, find there use
       // E_ENV_CALL_UMODE      = 4'h8,
       // E_UNKNOWN             = 4'ha    // reserved code 10, used for debugging
	// Abort and Clear logic
	always_ff @(posedge clk_i or negedge rst_n_i) begin: Abort_update

	if (!rst_n_i) begin // Asynchronous reset     
        	abort_i  				= 	0;
   			clr_l1tlb_mshr_i  		= 	0;
   			clr_l2tlb_mshr_i  		= 	0;
   			clear_dmshr_dregs_i 	= 	0; 
			synch_l1dc_l2c_i  		= 	0;
    end
	else if (except_rasied_i && ( (except_code_i == E_INSTR_PAGE_FAULT) || (except_code_i == E_I_ADDR_MISALIGNED)|| (except_code_i == E_I_ACCESS_FAULT))) begin
   			clr_l1tlb_mshr_i  		= 	1;
			clr_l2tlb_mshr_i  		= 	1;
    end
	else if (except_rasied_i && ( (except_code_i == E_LD_PAGE_FAULT) || (except_code_i == E_ST_PAGE_FAULT) || (except_code_i == E_LD_ADDR_MISALIGNED)|| (except_code_i == E_LD_ACCESS_FAULT)|| (except_code_i == E_ST_ADDR_MISALIGNED)|| (except_code_i == E_ST_ACCESS_FAULT )))) begin
			clear_dmshr_dregs_i 	= 	1;
    end
	else if (except_rasied_i && ( (except_code_i == E_ILLEGAL_INSTRUCTION) )) begin
			abort_i  				= 	1;
    end
	else if (except_rasied_i && (!l2c_update_done_o) && ( (except_code_i == E_ENV_CALL_SMODE) || (E_ENV_CALL_MMODE) ))) begin
			synch_l1dc_l2c_i  		= 	1;
    end
	else  begin
            abort_i  				= 	0;
   			clr_l1tlb_mshr_i  		= 	0;
   			clr_l2tlb_mshr_i  		= 	0;
   			clear_dmshr_dregs_i 	= 	0; 
			synch_l1dc_l2c_i  		= 	0;
    end
	end 

	// Flush logic
	always_ff @(posedge clk_i or negedge rst_n_i) begin: flush_update

	if (!rst_n_i) begin // Asynchronous reset     
        	L1TLB_flush_type_i		= 	NoFlush;
  			L2TLB_flush_type_i  	= 	NoFlush;
  			flush_asid_i  			= 	'd0;
 			flush_page_i  			= 	'd0;
    end
	else if (except_i) begin			// Think about this ?
            L1TLB_flush_type_i		= 	FlushASID;
			L2TLB_flush_type_i		= 	FlushASID;
			flush_asid_i  			= 	'd0;
    end
	else if (except_rasied_i && ( (except_code_i == E_INSTR_PAGE_FAULT) || (except_code_i == E_LD_PAGE_FAULT) || (except_code_i == E_ST_PAGE_FAULT) ))) begin
			L1TLB_flush_type_i		= 	FlushPage;
            L2TLB_flush_type_i		= 	FlushPage;
			flush_page_i  			= 	'd0;
    end
	else if (except_rasied_i) begin
			L1TLB_flush_type_i		= 	FlushAll;
            L2TLB_flush_type_i		= 	FlushAll;
			flush_asid_i  			= 	'd0;
			flush_page_i  			= 	'd0;
    end
	else  begin
            L1TLB_flush_type_i		= 	NoFlush;
  			L2TLB_flush_type_i  	= 	NoFlush;
  			flush_asid_i  			= 	'd0;
 			flush_page_i  			= 	'd0;
    end
	end

//-----

endmodule
