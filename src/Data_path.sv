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

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/len5_pkg.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/expipe_pkg.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/control_pkg.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/memory_pkg.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/csr_pkg.sv"
import len5_pkg::*;
import control_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Expipe/A_Back_end.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Frontend/B_Front_end.sv"

module Data_path
(
	// From :CU
  	input   logic             clk_i,
  	input   logic             rst_n_i,
  	input   logic             flush_i,
	//input logic stall,

	// For back end :CU
  	input   satp_mode_t       vm_mode_i,

	// To the main control :CU 
  	output  logic             main_cu_stall_o,

	// Data for execution unit :CU
    input   branch_type_t     branch_type_i,
  	input   ldst_type_t       ldst_type_i,

  	// From/to i-cache  :I$
  	output  logic [XLEN-1:0]  addr_o,
  	output  logic             addr_valid_o,
 	input   logic             addr_ready_i,
  	input   icache_out_t      data_i,
  	input   logic             data_valid_i,
 	output  logic             data_ready_o,
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	input   logic             except_i,
  	input   logic [XLEN-1:0]  except_pc_i,

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	input   logic             except_raised_i,
  	input   except_code_t     except_code_i,

	// Handshake and data from/to the TLB :DTLB
    input   dtlb_lsq_ans_t          dtlb_ans_i,
    input   dtlb_lsq_wup_t          dtlb_wup_i,
    output  lsq_dtlb_req_t          dtlb_req_o,

    // Handshake and data from/to the D$ :D$
    input   l1dc_lsq_ans_t          dcache_ans_i,
    input   l1dc_lsq_wup_t          dcache_wup_i,
    output  lsq_l1dc_req_t          dcache_req_o  
);

  	logic             issue_ready_i;
  	logic             issue_valid_o;
  	logic [ILEN-1:0]  instruction_o;
  	prediction_t      pred_o;
  	resolution_t      res_i;


Front_end #(.HLEN(4),.BTB_BITS(4)) u_Front_end_F
(
  	.clk_i    (clk_i),
    .rst_n_i  (rst_n_i),
    .flush_i  (flush_i),
	//.stall(stall),

  // From/to i-cache
  .addr_o			(addr_o),
  .addr_valid_o		(addr_valid_o),
  .addr_ready_i		(addr_ready_i),
  .data_i			(data_i),
  .data_valid_i		(data_valid_i),
  .data_ready_o		(data_ready_o),

  // From/to instruction decode
  .issue_ready_i	(issue_ready_i),
  .issue_valid_o	(issue_valid_o),
  .instruction_o	(instruction_o),
  .pred_o			(pred_o),

  // From branch unit (ex stage)
  .res_i			(res_i),

  // For pc_gen from or to back end
  .except_i			(except_i),
  .except_pc_i		(except_pc_i)   
);

Back_end u_Back_end_IQL
(
    // To the main control 
    .main_cu_stall_o(main_cu_stall_o),

    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),
	.vm_mode_i(vm_mode_i),

    // Handshake from/to fetch unit
    .fetch_valid_i (issue_valid_o),
    .fetch_ready_o (issue_ready_i),

    // Data from fetch unit
    .curr_pc_i (pred_o.pc),
    .instruction_i (instruction_o),
    .pred_target_i (pred_o.target),
    .pred_taken_i (pred_o.taken),
    .except_raised_i (except_raised_i),
    .except_code_i (except_code_i),

    // Data for execution unit
	.branch_type_i(branch_type_i),
	.ldst_type_i(ldst_type_i),

	// Data to the FE 
	.res_pc_o(res_i.pc),
  	.res_target_o(res_i.target),
  	.res_taken_o(res_i.taken),
	.res_mispredict_o(res_i.mispredict),

	// Handshake and data from/to the TLB
    .dtlb_ans_i(dtlb_ans_i),
    .dtlb_wup_i(dtlb_wup_i),
    .dtlb_req_o(dtlb_req_o),

    // Handshake and data from/to the D$
    .dcache_ans_i(dcache_ans_i),
    .dcache_wup_i(dcache_wup_i),
    .dcache_req_o(dcache_req_o)

);

endmodule
