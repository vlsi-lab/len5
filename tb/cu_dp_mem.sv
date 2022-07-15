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
// Author: WALID
// Date: 07/10/2019

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*; 
import csr_pkg::*;

module cu_dp_mem
#(
	parameter [XLEN-1:0] BOOT_PC = 'h0
) (
	// From :TB
  	input   logic             clk_i,
  	input   logic             rst_n_i,
	output  logic             flush_i,  
 
  	// L2 Cache Arbiter <-> L2 Cache Emulator
	output l2arb_l2c_req_t       l2arb_l2c_req_o,
  	input  logic                 l2c_l2arb_req_rdy_i,
  	input l2c_l2arb_ans_t       l2c_l2arb_ans_i,
  	output logic                 l2arb_l2c_ans_rdy_o 
);

	logic             flush_it;
	
	satp_mode_t       vm_mode_i;

	// To the main control :CU 
  	logic             main_cu_stall_o;
	logic [ILEN-1:0] 	ins_in;
	logic 				stall;
	logic 				stall1;
	logic 				stall2;

  	// From/to i-cache  :I$
 	logic             data_ready_o;
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	//logic             except_i;
  	//logic [XLEN-1:0]  except_pc_i;

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	//logic             except_raised_i;
  	//except_code_t     except_code_i;

	logic                       except_raised_o;
    //except_code_t  except_code_o;
    except_code_t  except_code_o;

	// From main unit
   	logic                 abort_i;
   	logic                 clr_l1tlb_mshr_i;
   	logic                 clr_l2tlb_mshr_i;
   	logic                 clear_dmshr_dregs_i; 

	// Update Block <-> d-Cache Updating Unit
  	logic                 synch_l1dc_l2c_i;
  	logic                 l2c_update_done_o;

 	 // System -> TLBs/PTW
  	logic                 vmem_on_i;
  	logic                 sum_bit_i;
  	logic                 mxr_bit_i;
 	csr_priv_t            priv_mode_i;
  	csr_priv_t            priv_mode_ls_i;
  	asid_t                base_asid_i;
  	logic [PPN_LEN-1:0]   csr_root_ppn_i;
  	tlb_flush_e           L1TLB_flush_type_i;
  	tlb_flush_e           L2TLB_flush_type_i;
  	asid_t                flush_asid_i;
 	vpn_t                 flush_page_i;
	
	// LSQ <-> d-TLB
  	logic                 dtlb_lsq_req_rdy_o;

  	// LSQ <-> d-Cache
 	logic                 l1dc_lsq_req_rdy_o;
	rob_idx_t rob_head_idx_o;

	//l2arb_l2c_req_t       l2arb_l2c_req_o;
  	//logic                 l2c_l2arb_req_rdy_i;
  	//l2c_l2arb_ans_t       l2c_l2arb_ans_i;
  	//logic                 l2arb_l2c_ans_rdy_o; 

	assign stall = stall1 && stall2;
	assign flush_i = flush_it;

data_path_memory #(.BOOT_PC(BOOT_PC)) U_Data_path_memory
(
	// From :CU
  	.clk_i    (clk_i),
    .rst_n_i  (rst_n_i),
    .flush_i  (flush_it),
	.ins_in(ins_in),
	

	// For back end :CU
  	.vm_mode_i(vm_mode_i),

	// To the main control :CU 
  	.main_cu_stall_o(main_cu_stall_o),

  	// From/to i-cache  :I$
 	.data_ready_o(data_ready_o),
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	//.except_i(except_i),
  	//.except_pc_i(except_pc_i),

	.except_raised_o(except_raised_o),
	.except_code_o(except_code_o),
	.rob_head_idx_o		(rob_head_idx_o),

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	//.except_raised_i(except_raised_i),
  	//.except_code_i(except_code_i),

	// From main unit
   	.abort_i(abort_i),
   	.clr_l1tlb_mshr_i(clr_l1tlb_mshr_i),
   	.clr_l2tlb_mshr_i(clr_l2tlb_mshr_i),
   	.clear_dmshr_dregs_i(clear_dmshr_dregs_i), 

	// Update Block <-> d-Cache Updating Unit
  	.synch_l1dc_l2c_i(synch_l1dc_l2c_i),
  	.l2c_update_done_o(l2c_update_done_o),

 	 // System -> TLBs/PTW
  	.vmem_on_i(vmem_on_i),
  	.sum_bit_i(sum_bit_i),
  	.mxr_bit_i(mxr_bit_i),
 	.priv_mode_i(priv_mode_i),
  	.priv_mode_ls_i(priv_mode_ls_i),
  	.base_asid_i(base_asid_i),
  	.csr_root_ppn_i(csr_root_ppn_i),
  	.L1TLB_flush_type_i(L1TLB_flush_type_i),
  	.L2TLB_flush_type_i(L2TLB_flush_type_i),
  	.flush_asid_i(flush_asid_i),
 	.flush_page_i(flush_page_i),
	
	// LSQ <-> d-TLB
  	.dtlb_lsq_req_rdy_o(dtlb_lsq_req_rdy_o),

  	// LSQ <-> d-Cache
 	.l1dc_lsq_req_rdy_o(l1dc_lsq_req_rdy_o),
 
  	// L2 Cache Arbiter <-> L2 Cache Emulator
	.l2arb_l2c_req_o(l2arb_l2c_req_o),
  	.l2c_l2arb_req_rdy_i(l2c_l2arb_req_rdy_i),
  	.l2c_l2arb_ans_i(l2c_l2arb_ans_i),
  	.l2arb_l2c_ans_rdy_o(l2arb_l2c_ans_rdy_o) 
);

cu1_fsm U_CU1_FSM
(
	// From :TB
  	.clk_i    (clk_i),
    .rst_n_i  (rst_n_i),
    .flush_i  (flush_it),

	// For back end :CU
  	.vm_mode_i(vm_mode_i),

	// To the main control :CU 
  	.main_cu_stall_o(main_cu_stall_o),
	.ins_in(ins_in),
	.stall(stall1),

  	// From/to i-cache  :I$
 	.data_ready_o(data_ready_o),
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	//.except_i(except_i),
  	//.except_pc_i(except_pc_i),

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	.except_raised_i(except_raised_o),
  	.except_code_i(except_code_o),

	//.except_raised_o(except_raised_o),
	//.except_code_o(except_code_o),

	.commit_head_cnt(rob_head_idx_o/*commit_head_cnt*/),

	// From main unit
   	.abort_i(abort_i),
   	.clr_l1tlb_mshr_i(clr_l1tlb_mshr_i),
   	.clr_l2tlb_mshr_i(clr_l2tlb_mshr_i),
   	.clear_dmshr_dregs_i(clear_dmshr_dregs_i), 

	// Update Block <-> d-Cache Updating Unit
  	.synch_l1dc_l2c_i(synch_l1dc_l2c_i),
  	.l2c_update_done_o(l2c_update_done_o),

 	 // System -> TLBs/PTW
  	.vmem_on_i(vmem_on_i),
  	.sum_bit_i(sum_bit_i),
  	.mxr_bit_i(mxr_bit_i),
 	.priv_mode_i(priv_mode_i),
  	.priv_mode_ls_i(priv_mode_ls_i),
  	.base_asid_i(base_asid_i),
  	.csr_root_ppn_i(csr_root_ppn_i),
  	.L1TLB_flush_type_i(L1TLB_flush_type_i),
  	.L2TLB_flush_type_i(L2TLB_flush_type_i),
  	.flush_asid_i(flush_asid_i),
 	.flush_page_i(flush_page_i),
	
	// LSQ <-> d-TLB
  	.dtlb_lsq_req_rdy_o(dtlb_lsq_req_rdy_o),

  	// LSQ <-> d-Cache
 	.l1dc_lsq_req_rdy_o(l1dc_lsq_req_rdy_o),
 
  	// L2 Cache Arbiter <-> L2 Cache Emulator
	//.l2arb_l2c_req_o(l2arb_l2c_req_o),
  	.l2c_l2arb_req_rdy_i(l2c_l2arb_req_rdy_i),
  	.l2c_l2arb_ans_i(l2c_l2arb_ans_i)//,
  	//.l2arb_l2c_ans_rdy_o(l2arb_l2c_ans_rdy_o) 
);

cu2_fsm  U_CU2_FSM
(
	// From :TB
  	.clk_i    (clk_i),
    .rst_n_i  (rst_n_i),

	// To the main control :CU 
  	.main_cu_stall_o(main_cu_stall_o),
	.ins_in(ins_in),
	.stall(stall2),
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	//.except_i(except_i),
  	//.except_pc_i(except_pc_i),

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	.except_raised_i(except_raised_o),
  	.except_code_i(except_code_o)
);

//cache_L2_system_emulator u_cache_L2_system_emulator
//(
  // Main
	//.clk_i    (clk_i),
    //.rst_ni  (rst_n_i),
	//.flush_i  (flush_i),
	//.l2arb_l2c_req_i(l2arb_l2c_req_o),
  	//.l2c_l2arb_req_rdy_o(l2c_l2arb_req_rdy_i),
  	//.l2c_l2arb_ans_o(l2c_l2arb_ans_i),
  	//.l2arb_l2c_ans_rdy_i(l2arb_l2c_ans_rdy_o) 
//);

endmodule
