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

module data_path_memory
(
	// From :CU
  	input   logic             clk_i,
  	input   logic             rst_n_i,
  	input   logic             flush_i,
	output  logic [ILEN-1:0]  ins_in,
	//input logic stall,

	// For back end :CU
  	input   satp_mode_t       vm_mode_i,

	// To the main control :CU 
  	output  logic             main_cu_stall_o,

	// Data for execution unit :CU
    input   branch_type_t     branch_type_i,
  	input   ldst_type_t       ldst_type_i,

  	// From/to i-cache  :I$
 	output  logic             data_ready_o,
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	//input   logic             except_i,
  	//input   logic [XLEN-1:0]  except_pc_i,

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	//input   logic             except_raised_i,
  	//input   except_code_t     except_code_i,

	output   logic                       except_raised_o,
    //output   logic [ROB_EXCEPT_LEN-1:0]  except_code_o,
	output   except_code_t  except_code_o,
	output logic [ROB_IDX_LEN-1:0] rob_head_idx_o,

	// From main unit
   	input  logic                 abort_i,
   	input  logic                 clr_l1tlb_mshr_i,
   	input  logic                 clr_l2tlb_mshr_i,
   	input  logic                 clear_dmshr_dregs_i, 

	// Update Block <-> d-Cache Updating Unit
  	input  logic                 synch_l1dc_l2c_i,
  	output logic                 l2c_update_done_o,

 	 // System -> TLBs/PTW
  	input  logic                 vmem_on_i,
  	input  logic                 sum_bit_i,
  	input  logic                 mxr_bit_i,
 	input  priv_e                priv_mode_i,
  	input  priv_e                priv_mode_ls_i,
  	input  asid_t                base_asid_i,
  	input  logic [PPN_LEN-1:0]   csr_root_ppn_i,
  	input  tlb_flush_e           L1TLB_flush_type_i,
  	input  tlb_flush_e           L2TLB_flush_type_i,
  	input  asid_t                flush_asid_i,
 	input  var vpn_t                 flush_page_i,
	
	// LSQ <-> d-TLB
  	output logic                 dtlb_lsq_req_rdy_o,

  	// LSQ <-> d-Cache
 	output logic                 l1dc_lsq_req_rdy_o,
 
  	// L2 Cache Arbiter <-> L2 Cache Emulator
	output l2arb_l2c_req_t       l2arb_l2c_req_o,
  	input  logic                 l2c_l2arb_req_rdy_i,
  	input  var l2c_l2arb_ans_t       l2c_l2arb_ans_i,
  	output logic                 l2arb_l2c_ans_rdy_o 
);

	frontend_icache_req_t frontend_icache_req_i;
  	logic                 icache_frontend_rdy_o;
  	icache_frontend_ans_t icache_frontend_ans_o;    
	icache_out_t      	  data_i;
	lsq_dtlb_req_t        lsq_dtlb_req_i;
  	dtlb_lsq_ans_t        dtlb_lsq_ans_o;
  	dtlb_lsq_wup_t        dtlb_lsq_wup_o;
	lsq_l1dc_req_t        lsq_l1dc_req_i;
  	l1dc_lsq_ans_t        l1dc_lsq_ans_o;
  	l1dc_lsq_wup_t        l1dc_lsq_wup_o;

    assign data_i.pc = icache_frontend_ans_o.vaddr;
	assign data_i.line = icache_frontend_ans_o.line;

data_path  u_Data_path
(
	.clk_i    (clk_i),
    .rst_n_i  (rst_n_i),
    .flush_i  (flush_i),
	.ins_in   (ins_in),
	//.stall(stall),
    .vm_mode_i(vm_mode_i),
	.main_cu_stall_o(main_cu_stall_o),
	.branch_type_i(branch_type_i),
	.ldst_type_i(ldst_type_i),
  	.addr_o(frontend_icache_req_i.vaddr),
  	.addr_valid_o(frontend_icache_req_i.valid),
 	.addr_ready_i(icache_frontend_rdy_o),
  	.data_i(data_i),
  	.data_valid_i(icache_frontend_ans_o.valid),
 	.data_ready_o(data_ready_o),
	.icache_frontend_ans_i(icache_frontend_ans_o),
  	//.except_i(except_i),
  	//.except_pc_i(except_pc_i),
	//.except_raised_i(except_raised_i),
  	//.except_code_i(except_code_i),
	.except_raised_o(except_raised_o),
	.except_code_o(except_code_o),
	.rob_head_idx_o		(rob_head_idx_o),
    .dtlb_ans_i(dtlb_lsq_ans_o),
    .dtlb_wup_i(dtlb_lsq_wup_o),
	.dtlb_ready_i(dtlb_lsq_req_rdy_o),
    .dtlb_req_o(lsq_dtlb_req_i),
    .dcache_ans_i(l1dc_lsq_ans_o),
    .dcache_wup_i(l1dc_lsq_wup_o),
	.dcache_ready_i(l1dc_lsq_req_rdy_o),
    .dcache_req_o(lsq_l1dc_req_i)  
);

memory_system_with_ssram u_memory_system_with_ssram
(
	.clk_i    (clk_i),
    .rst_ni  (rst_n_i),
    .flush_i  (flush_i),  
	.abort_i(abort_i),
  	.clr_l1tlb_mshr_i(clr_l1tlb_mshr_i),
 	.clr_l2tlb_mshr_i(clr_l2tlb_mshr_i),
  	.clear_dmshr_dregs_i(clear_dmshr_dregs_i),
  	.synch_l1dc_l2c_i(synch_l1dc_l2c_i),
  	.l2c_update_done_o(l2c_update_done_o),
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
  	.frontend_icache_req_i(frontend_icache_req_i),
  	.icache_frontend_rdy_o(icache_frontend_rdy_o),
  	.icache_frontend_ans_o(icache_frontend_ans_o),
  	.lsq_dtlb_req_i(lsq_dtlb_req_i),
  	.dtlb_lsq_req_rdy_o(dtlb_lsq_req_rdy_o),
  	.dtlb_lsq_ans_o(dtlb_lsq_ans_o),
  	.dtlb_lsq_wup_o(dtlb_lsq_wup_o),
	.lsq_l1dc_req_i(lsq_l1dc_req_i),
  	.l1dc_lsq_req_rdy_o(l1dc_lsq_req_rdy_o),
  	.l1dc_lsq_ans_o(l1dc_lsq_ans_o),
  	.l1dc_lsq_wup_o(l1dc_lsq_wup_o),
  	.l2arb_l2c_req_o(l2arb_l2c_req_o),
  	.l2c_l2arb_req_rdy_i(l2c_l2arb_req_rdy_i),
  	.l2c_l2arb_ans_i(l2c_l2arb_ans_i),
  	.l2arb_l2c_ans_rdy_o(l2arb_l2c_ans_rdy_o)
);

endmodule
