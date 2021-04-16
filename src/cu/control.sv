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
//
// File: fetch_stage.sv
// Author: Marco Andorno
// Date: 07/10/2019
//
`include "len5_pkg.sv"
`include "expipe_pkg.sv"
`include "control_pkg.sv"
`include "memory_pkg.sv"
`include "csr_pkg.sv"
import len5_pkg::*;
import control_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

//`include "/Data_path.sv"
//`include "/Memory/K_memory_system_with_ssram.sv"

module control
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
	input   logic [ILEN-1:0] 	pc_in,
	output  logic 				stall,

	// Data for execution unit :CU
    output  branch_type_t     	branch_type_i,
  	output  ldst_type_t       	ldst_type_i,

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
//Perform a similar solution to this
	flush_i 				= 	0;
	if (main_cu_stall_o) begin	// Put it inside an always block
		flush_i 			= 	1;
	end
	vm_mode_i				=	SV39;	//Use assign
	branch_type_i			=	beq;
	ldst_type_i				=	LS_WORD;

	vmem_on_i  				= 	0;
  	sum_bit_i  				= 	0;
  	mxr_bit_i  				= 	0;
 	priv_mode_i  			= 	U;
  	priv_mode_ls_i  		= 	U;
  	base_asid_i  			= 	'd0;
  	csr_root_ppn_i  		= 	'd0;
  	L1TLB_flush_type_i		= 	NoFlush;
  	L2TLB_flush_type_i  	= 	NoFlush;
  	flush_asid_i  			= 	'd0;
 	flush_page_i  			= 	'd0;

	abort_i  				= 	0;
   	clr_l1tlb_mshr_i  		= 	0;
   	clr_l2tlb_mshr_i  		= 	0;
   	clear_dmshr_dregs_i 	= 	0; 
	synch_l1dc_l2c_i  		= 	0;

    assign 	data_i.pc 		= 	icache_frontend_ans_o.vaddr;
	assign 	data_i.line 	= 	icache_frontend_ans_o.line;

endmodule
