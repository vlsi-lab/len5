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
// File: issue_IQL.sv
// Author: WALID WALID
// Date: 17/10/2020

// Include LEN5 configuration
`include "len5_config.svh"

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module back_end 
(
    input   logic               clk_i,
    input   logic               rst_n_i,
    input   logic               flush_i,
	
	input   satp_mode_t         vm_mode_i,

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

    // To the main control 
    output  logic                       main_cu_stall_o,

	// Data to the FE 
	output  logic [XLEN-1:0]  res_pc_o,
  	output  logic [XLEN-1:0]  res_target_o,
  	output  logic             res_taken_o,
	output  logic 			  res_mispredict_o,

	output   logic                       except_raised_o,
    //output   logic [ROB_EXCEPT_LEN-1:0]  except_code_o,
	output   except_code_t  except_code_o,

	output   logic                  except_o,
    output   logic [XLEN-1:0]  		except_pc_o,

	output logic [ROB_IDX_LEN-1:0] rob_head_idx_o,

	// Handshake and data from/to the TLB
    input dtlb_lsq_ans_t          dtlb_ans_i,
    input dtlb_lsq_wup_t          dtlb_wup_i,
    input   logic                       dtlb_ready_i,
    output  lsq_dtlb_req_t          dtlb_req_o,

    // Handshake and data from/to the D$
    input l1dc_lsq_ans_t          dcache_ans_i,
    input l1dc_lsq_wup_t          dcache_wup_i,
    input   logic                       dcache_ready_i,
    output  lsq_l1dc_req_t          dcache_req_o
);

    // DEFINITIONS
	// Handshake of issue from/to the integer register status register
    logic                       int_regstat_ready_i;        // should always be asserted
    logic                       int_regstat_valid_o;

	// Data of issue from/to the integer register status register
	logic                       int_regstat_rs1_busy_i;     
	logic [ROB_IDX_LEN-1:0]     int_regstat_rs1_rob_idx_i; 
	logic                       int_regstat_rs2_busy_i;     
	logic [ROB_IDX_LEN-1:0]     int_regstat_rs2_rob_idx_i;  
	logic [REG_IDX_LEN-1:0]     int_regstat_rd_idx_o;       
	logic [ROB_IDX_LEN-1:0]     int_regstat_rob_idx_o;     
	logic [REG_IDX_LEN-1:0]     int_regstat_rs1_idx_o;      
	logic [REG_IDX_LEN-1:0]     int_regstat_rs2_idx_o;  

`ifdef LEN5_FP_EN
	// Handshake of issue from/to the floating point register status register
	logic                       fp_regstat_ready_i;
	logic                       fp_regstat_valid_o;

	// Data of issue from/to the floating point register status register
	logic                       fp_regstat_rs1_busy_i;     
	logic [ROB_IDX_LEN-1:0]     fp_regstat_rs1_rob_idx_i;  
	logic                       fp_regstat_rs2_busy_i;     
	logic [ROB_IDX_LEN-1:0]     fp_regstat_rs2_rob_idx_i; 
	logic [REG_IDX_LEN-1:0]     fp_regstat_rd_idx_o;       
	logic [ROB_IDX_LEN-1:0]     fp_regstat_rob_idx_o;     
	logic [REG_IDX_LEN-1:0]     fp_regstat_rs1_idx_o;     
	logic [REG_IDX_LEN-1:0]     fp_regstat_rs2_idx_o; 
`endif /* LEN5_FP_EN */

    // Data of issue from/to the integer register file
    logic [XLEN-1:0]            intrf_rs1_value_i;      // value of the first operand
    logic [XLEN-1:0]            intrf_rs2_value_i;      // value of the second operand
    logic [REG_IDX_LEN-1:0]     intrf_rs1_idx_o;        // RF address of the first operand 
    logic [REG_IDX_LEN-1:0]     intrf_rs2_idx_o;        // RF address of the second operand

`ifdef LEN5_FP_EN
    // Data of issue from/to the floating point register file
    logic [XLEN-1:0]            fprf_rs1_value_i;       // value of the first operand
    logic [XLEN-1:0]            fprf_rs2_value_i;       // value of the second operand
    logic [REG_IDX_LEN-1:0]     fprf_rs1_idx_o;         // RF address of the first operand 
    logic [REG_IDX_LEN-1:0]     fprf_rs2_idx_o;         // RF address of the second operand  
`endif /* LEN5_FP_EN */

	// Handshake of issue from/to the execution pipeline
    logic [0:EU_N-1]            ex_ready_i;             // valid signal from each reservation station
    logic [0:EU_N-1]            ex_valid_o;             // ready signal to each reservation station

    // Data of issue to the execution pipeline reservation stations
    logic [MAX_EU_CTL_LEN-1:0]  ex_eu_ctl_o;        	// controls for the associated EU
    logic                       ex_rs1_ready_o;     	// first operand is ready at issue time (from the RF or the ROB)
    logic [ROB_IDX_LEN-1:0]     ex_rs1_idx_o;    		// the index of the ROB where the first operand can be found (if not ready
    logic [XLEN-1:0]            ex_rs1_value_o;     	// the value of the first operand (if ready)
    logic                       ex_rs2_ready_o;     	// second operand is ready at issue time (from the RF or the ROB)
    logic [ROB_IDX_LEN-1:0]     ex_rs2_idx_o;    		// the index of the ROB where the first operand can be found (if not ready)
    logic [XLEN-1:0]            ex_rs2_value_o;    		// the value of the first operand (if ready)
   
 	logic [I_IMM-1:0]           ex_imm_value_o; 		// the value of the immediate field (for st and branches)                   

    logic [ROB_IDX_LEN-1:0]     ex_rob_idx_o;       	// the location of the ROB assigned to the instruction
    logic [XLEN-1:0]            ex_pred_pc_o;       	// the PC of the current issuing instr (branches only)
    logic [XLEN-1:0]            ex_pred_target_o;  		// the predicted target of the current issuing instr (branches only)
    logic                       ex_pred_taken_o;  		// the predicted taken bit of the current issuing instr (branches only) 

	// Handshake of issue from/to the ROB
    logic                       rob_ready_i;            // the ROB has an empty entry available
    logic                       rob_valid_o;            // a new instruction can be issued

	// Data of issue from/to the ROB stage
	logic                       rob_rs1_ready_o;      // the result is ready
    logic [XLEN-1:0]            rob_rs1_value_o;      // the value of the first operand
    logic                       rob_rs2_ready_o;      // the result is ready
    logic [XLEN-1:0]            rob_rs2_value_o;      // the value of the second operand
	logic [ROB_IDX_LEN-1:0]     rob_tail_idx_o;

	logic [ROB_IDX_LEN-1:0]     rob_rs1_idx_i;        // ROB entry containing rs1 value 
    logic [ROB_IDX_LEN-1:0]     rob_rs2_idx_i;        // ROB entry containing rs2 value
	logic [ILEN-1:0]            rob_instr_o;
	logic [REG_IDX_LEN-1:0]     rob_rd_idx_i;
	logic                       rob_except_raised_i;
	logic [ROB_EXCEPT_LEN-1:0]  rob_except_code_i;
	logic [XLEN-1:0]            rob_except_aux_i;
	logic                       rob_res_ready_o;
    logic [XLEN-1:0]            rob_res_value;

	// Handshake int/fp regstate from/to the commit logic fp
	logic                   comm_valid_i;
    logic                   comm_ready_o;
	logic                   fp_comm_valid_i;
    logic                   fp_comm_ready_o;

    // Data int/fp regstate from the commit logic
    logic [REG_IDX_LEN-1:0] comm_rd_idx_i;          // destination register of the committing instr.
    logic [XLEN-1:0]        comm_rd_value_i;
`ifdef LEN5_FP_EN
	logic [REG_IDX_LEN-1:0] fp_comm_rd_idx_i;          // destination register of the committing instr.
	logic [XLEN-1:0]        fp_comm_rd_value_i;
`endif /* LEN5_FP_EN */

	// Handshake int/fp regfile from/to the commit logic
	logic                   rf_comm_valid_i;
    logic                   rf_comm_ready_o;
`ifdef LEN5_FP_EN
	logic                   fp_rf_comm_valid_i;
    logic                   fp_rf_comm_ready_o;
`endif /* LEN5_FP_EN */

	// Data int/fp regfile from/to the commit logic
	//logic [REG_IDX_LEN-1:0] comm_rf_rd_idx_i;          // destination register of the committing instr.
    //logic [XLEN-1:0]        comm_rf_rd_value_i;
	//logic [REG_IDX_LEN-1:0] fp_comm_rf_rd_idx_i;          // destination register of the committing instr.
	//logic [XLEN-1:0]        fp_comm_rf_rd_value_i;

	// Hanshake of Exec from/to the CDB 
    logic    [0:EU_N-1]               cdb_ready_i;
    //logic                   cdb_valid_i;        // to know if the CDB is carrying valid data
    logic    [0:EU_N-1]               cdb_valid_o;

    // Data of Exec from/to the CDB
	cdb_data_t  cdb_data_i [0:EU_N-1];
	cdb_data_t  cdb_data_o [0:EU_N-1];
    // cdb_data_t  [0:EU_N-1] cdb_data_i_low_prio;
    // cdb_data_t  [0:EU_N-1] cdb_data_o_low_prio;
    //logic [ROB_IDX_LEN-1:0] cdb_idx_i;
    //logic [XLEN-1:0]        cdb_data_i;
    //logic                   cdb_except_raised_i;
    //logic [ROB_IDX_LEN-1:0] cdb_idx_o;
    //logic [XLEN-1:0]        cdb_data_o;
    //logic                   cdb_except_raised_o;
    //logic [ROB_EXCEPT_LEN-1:0] cdb_except_o;

	// Control Exec from/to the ROB
    logic [ROB_IDX_LEN-1:0] rob_head_idx_i;
    logic                   rob_store_committing_o;
	//logic [ROB_IDX_LEN-1:0] comm_head_idx_i;
	//logic [ROB_IDX_LEN-1:0] fp_comm_head_idx_i;

	// Hanshake of Exec from/to the CDB 
    //logic                   cdb_lb_valid_i;
    //logic                   cdb_sb_valid_i;
    //logic                   cdb_lb_ready_i;
    //logic                   cdb_sb_ready_i;
    //logic                   lb_cdb_valid_o;
    //logic                   sb_cdb_valid_o;

    // Data of Exec from/to the CDB
    //cdb_data_t              cdb_lsb_data_i;
    //cdb_data_t              lb_cdb_data_o;
    //cdb_data_t              sb_cdb_data_o;

	// Data of commit from/to the ROB stage
    logic                   comm_valid_ROB_i;
    logic                   comm_ready_ROB_o;
    
    // Data of commit from the ROB
    logic [ILEN-1:0]            rob_instr_i;
    logic [XLEN-1:0]            rob_pc_i;
    logic [REG_IDX_LEN-1:0]     rob_rd_idx_o;
    logic [XLEN-1:0]            rob_value_i;
	//logic [REG_IDX_LEN-1:0]     fp_rob_rd_idx_i;
	logic [REG_IDX_LEN-1:0]     fp_rob_rd_idx_o;
    logic [XLEN-1:0]            fp_rob_value_i;
    logic                       rob_except_raised_o;
    //logic [ROB_EXCEPT_LEN-1:0]  rob_except_code_o;
	except_code_t  rob_except_code_o;

	// Hanshake of rob from/to the CDB 
    logic                   rob_cdb_ready_o;
    logic                   rob_cdb_valid_i;        // to know if the CDB is carrying valid data

	// Data of rob from cdb
	cdb_data_t                  cdb_data_in;

	logic [ROB_IDX_LEN-1:0]     sb_head_idx_o;

	//CDB
	//new added
	// Handshake from/to the cdb
	logic                       cdb_valid_i;
	logic                       cdb_ready_o;

	// Data from the cdb
	logic                       cdb_except_raised_i;
	logic [XLEN-1:0]            cdb_value_i;
	logic [ROB_IDX_LEN-1:0]		cdb_rob_idx_i;
//To here


// ---
// DUT
// ---

issue_q_l u_issue_q_l
(
	.clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),

    // Handshake from/to fetch unit
    .fetch_valid_i (fetch_valid_i),
    .fetch_ready_o (fetch_ready_o),

    // Data from fetch unit
    .curr_pc_i (curr_pc_i),
    .instruction_i (instruction_i),
    .pred_target_i (pred_target_i),
    .pred_taken_i (pred_taken_i),
    .except_raised_i (except_raised_i),
    .except_code_i (except_code_i),

	// To the main control 
    .main_cu_stall_o(main_cu_stall_o),

	// Handshake from/to the integer register status register
    .int_regstat_ready_i(int_regstat_ready_i),        
    .int_regstat_valid_o(int_regstat_valid_o),

    // Data from/to the integer register status register
    .int_regstat_rs1_busy_i(int_regstat_rs1_busy_i),     
    .int_regstat_rs1_rob_idx_i(int_regstat_rs1_rob_idx_i), 
    .int_regstat_rs2_busy_i(int_regstat_rs2_busy_i),     
    .int_regstat_rs2_rob_idx_i(int_regstat_rs2_rob_idx_i), 
    .int_regstat_rd_idx_o(int_regstat_rd_idx_o),       
    .int_regstat_rob_idx_o(int_regstat_rob_idx_o),   
    .int_regstat_rs1_idx_o(int_regstat_rs1_idx_o),      
    .int_regstat_rs2_idx_o(int_regstat_rs2_idx_o),     

`ifdef LEN5_FP_EN
    // Handshake from/to the floating point register status register
    .fp_regstat_ready_i(fp_regstat_ready_i),
    .fp_regstat_valid_o(fp_regstat_valid_o),

    // Data from/to the floating point register status register
    .fp_regstat_rs1_busy_i(fp_regstat_rs1_busy_i),    
    .fp_regstat_rs1_rob_idx_i(fp_regstat_rs1_rob_idx_i),  
    .fp_regstat_rs2_busy_i(fp_regstat_rs2_busy_i),     
    .fp_regstat_rs2_rob_idx_i(fp_regstat_rs2_rob_idx_i),  
    .fp_regstat_rd_idx_o(fp_regstat_rd_idx_o),     
    .fp_regstat_rob_idx_o(fp_regstat_rob_idx_o),    
    .fp_regstat_rs1_idx_o(fp_regstat_rs1_idx_o),    
    .fp_regstat_rs2_idx_o(fp_regstat_rs2_idx_o),
`endif /* LEN5_FP_EN */

    // Data from/to the integer register file
    .intrf_rs1_value_i(intrf_rs1_value_i),     
    .intrf_rs2_value_i(intrf_rs2_value_i),      
    .intrf_rs1_idx_o(intrf_rs1_idx_o), 
    .intrf_rs2_idx_o(intrf_rs2_idx_o),       

`ifdef LEN5_FP_EN
    // Data from/to the floating point register file
    .fprf_rs1_value_i(fprf_rs1_value_i),       
    .fprf_rs2_value_i(fprf_rs2_value_i),      
    .fprf_rs1_idx_o(fprf_rs1_idx_o),       
    .fprf_rs2_idx_o(fprf_rs2_idx_o), 
`endif /* LEN5_FP_EN */
  
    // Handshake from/to the execution pipeline
    .ex_ready_i(ex_ready_i),           
    .ex_valid_o(ex_valid_o),            

    // Data to the execution pipeline reservation stations
    .ex_eu_ctl_o(ex_eu_ctl_o),            
    .ex_rs1_ready_o(ex_rs1_ready_o),         
    .ex_rs1_idx_o(ex_rs1_idx_o),          
    .ex_rs1_value_o(ex_rs1_value_o),         
    .ex_rs2_ready_o(ex_rs2_ready_o),         
    .ex_rs2_idx_o(ex_rs2_idx_o),           
    .ex_rs2_value_o(ex_rs2_value_o),         
    .ex_imm_value_o(ex_imm_value_o),                           
    .ex_rob_idx_o(ex_rob_idx_o),          
    .ex_pred_pc_o(ex_pred_pc_o),              
    .ex_pred_target_o(ex_pred_target_o),         
    .ex_pred_taken_o(ex_pred_taken_o),
//New
	// Handshake from/to the cdb
	.cdb_valid_i(cdb_valid_i),
	.cdb_ready_o(cdb_ready_o),

	// Data from the cdb
	.cdb_except_raised_i(cdb_except_raised_i),
	.cdb_value_i(cdb_value_i),
	.cdb_rob_idx_i(cdb_rob_idx_i),

    // Handshake from/to the ROB
    .rob_ready_i(rob_ready_i),           
    .rob_valid_o(rob_valid_o),            

    // Data from/to the ROB
    .rob_rs1_ready_i(rob_rs1_ready_o),        
    .rob_rs1_value_i(rob_rs1_value_o),       
    .rob_rs2_ready_i(rob_rs2_ready_o),       
    .rob_rs2_value_i(rob_rs2_value_o),     
    .rob_tail_idx_i(rob_tail_idx_o),         
    
    .rob_rs1_idx_o(rob_rs1_idx_i),         
    .rob_rs2_idx_o(rob_rs2_idx_i),        
    .rob_instr_o(rob_instr_o),           
    .rob_rd_idx_o(rob_rd_idx_i),           
    .rob_except_raised_o(rob_except_raised_i),    
    .rob_except_code_o(rob_except_code_i),      
    .rob_except_aux_o(rob_except_aux_i),       
    .rob_res_ready_o(rob_res_ready_o),
    .rob_res_value_o(rob_res_value)
);

reg_status #(32) u_reg_status_int 
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),

    // Handshake from/to the issue logic
    .issuel_valid_i(int_regstat_valid_o),
    .issuel_ready_o(int_regstat_ready_i),

    // Data from/to the issue logic
    .issue_rd_idx_i(int_regstat_rd_idx_o),    
    .issue_rob_idx_i(int_regstat_rob_idx_o),     

    .issue_rs1_idx_i(int_regstat_rs1_idx_o),        // first source register index
    .issue_rs2_idx_i(int_regstat_rs2_idx_o),        // second source register index
    .issue_rs1_busy_o(int_regstat_rs1_busy_i),       // rs1 value is in the ROB or has to be computed
    .issue_rs1_rob_idx_o(int_regstat_rs1_rob_idx_i),    // the index of the ROB where the result is found
    .issue_rs2_busy_o(int_regstat_rs2_busy_i),       // rs1 value is in the ROB or has to be computed
    .issue_rs2_rob_idx_o(int_regstat_rs2_rob_idx_i),    // the index of the ROB where the result is found

    // Handshake from/to the commit logic
    .comm_valid_i(comm_ready_o),
    .comm_ready_o(comm_valid_i),

    // Data from the commit logic
    .comm_rd_idx_i(comm_rd_idx_i),          // destination register of the committing instr.
    .comm_head_idx_i(rob_head_idx_i)//(comm_head_idx_i)         // head entry of the ROB
);

`ifdef LEN5_FP_EN
reg_status # (32) u_reg_status_fp
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	//.stall(stall),

    // Handshake from/to the issue logic
    .issuel_valid_i(fp_regstat_valid_o),
    .issuel_ready_o(fp_regstat_ready_i),

    // Data from/to the issue logic
    .issue_rd_idx_i(fp_regstat_rd_idx_o),    
    .issue_rob_idx_i(fp_regstat_rob_idx_o),     

    .issue_rs1_idx_i(fp_regstat_rs1_idx_o),        // first source register index
    .issue_rs2_idx_i(fp_regstat_rs2_idx_o),        // second source register index
    .issue_rs1_busy_o(fp_regstat_rs1_busy_i),       // rs1 value is in the ROB or has to be computed
    .issue_rs1_rob_idx_o(fp_regstat_rs1_rob_idx_i),    // the index of the ROB where the result is found
    .issue_rs2_busy_o(fp_regstat_rs2_busy_i),       // rs1 value is in the ROB or has to be computed
    .issue_rs2_rob_idx_o(fp_regstat_rs2_rob_idx_i),    // the index of the ROB where the result is found

    // Handshake from/to the commit logic
    .comm_valid_i(fp_comm_ready_o),
    .comm_ready_o(fp_comm_valid_i),

    // Data from the commit logic
    .comm_rd_idx_i(fp_comm_rd_idx_i),          // destination register of the committing instr.
    .comm_head_idx_i(rob_head_idx_i)//(fp_comm_head_idx_i)         // head entry of the ROB
); 
`endif /* LEN5_FP_EN */

int_rf u_int_rf(
    .clk_i(clk_i),
    .rst_n_i(rst_n_i),
	//.stall(stall),

    // Handshake from the commit logic 
    .comm_valid_i(rf_comm_ready_o),
    .comm_ready_o(rf_comm_valid_i),

    // Data from the commit logic (result write port)
    .comm_rd_idx_i(comm_rd_idx_i),//(comm_rf_rd_idx_i),
    .comm_rd_value_i(comm_rd_value_i),//(comm_rf_rd_value_i),

    // Data to the issue stage (operands read ports)
    .issue_rs1_idx_i(intrf_rs1_idx_o),
    .issue_rs2_idx_i(intrf_rs2_idx_o),
    .issue_rs1_value_o(intrf_rs1_value_i),
    .issue_rs2_value_o(intrf_rs2_value_i)
);

`ifdef LEN5_FP_EN
fp_rf u_fp_rf(
    .clk_i(clk_i),
    .rst_n_i(rst_n_i),
	//.stall(stall),

    // Handshake from the commit logic 
    .comm_valid_i(fp_rf_comm_ready_o),
    .comm_ready_o(fp_rf_comm_valid_i),

    // Data from the commit logic (result write port)
    .comm_rd_idx_i(fp_comm_rd_idx_i),//(fp_comm_rf_rd_idx_i),
    .comm_rd_value_i(fp_comm_rd_value_i),//(fp_comm_rf_rd_value_i),

    // Data to the issue stage (operands read ports)
    .issue_rs1_idx_i(fprf_rs1_idx_o),
    .issue_rs2_idx_i(fprf_rs2_idx_o),
    .issue_rs1_value_o(fprf_rs1_value_i),
    .issue_rs2_value_o(fprf_rs2_value_i)
);
`endif /* LEN5_FP_EN */

exec_unit u_exec_unit(
    .clk_i(clk_i),
    .rst_n_i(rst_n_i),
    .flush_i(flush_i),
	//.stall(stall),
	.vm_mode_i(vm_mode_i),

    // Handshake from/to Back end
    .ex_ready_i(ex_valid_o),             
    .ex_valid_o(ex_ready_i),             

    // Data oto the Back end
    .ex_eu_ctl_i(ex_eu_ctl_o),    
    .ex_rs1_ready_i(ex_rs1_ready_o), 
    .ex_rs1_idx_i(ex_rs1_idx_o),   
    .ex_rs1_value_i(ex_rs1_value_o), 
    .ex_rs2_ready_i(ex_rs2_ready_o), 
    .ex_rs2_idx_i(ex_rs2_idx_o),   
    .ex_rs2_value_i(ex_rs2_value_o), 
   
 	.ex_imm_value_i(ex_imm_value_o),                  

    .ex_rob_idx_i(ex_rob_idx_o), 
    .ex_pred_pc_i(ex_pred_pc_o),   
    .ex_pred_target_i(ex_pred_target_o),
    .ex_pred_taken_i(ex_pred_taken_o),

	// Data to the FE 
	.res_pc_o(res_pc_o),
  	.res_target_o(res_target_o),
  	.res_taken_o(res_taken_o),
	.res_mispredict_o(res_mispredict_o),

	// Handshake and data from/to the TLB
    .dtlb_ans_i(dtlb_ans_i),
    .dtlb_wup_i(dtlb_wup_i),
    .dtlb_ready_i(dtlb_ready_i),
    .dtlb_req_o(dtlb_req_o),

    // Handshake and data from/to the D$
    .dcache_ans_i(dcache_ans_i),
    .dcache_wup_i(dcache_wup_i),
    .dcache_ready_i(dcache_ready_i),
    .dcache_req_o(dcache_req_o),

    // Hanshake from/to the CDB 
    .cdb_ready_i(cdb_ready_i),
    .cdb_valid_i(rob_cdb_valid_i),//cdb_valid_i),        // to know if the CDB is carrying valid data
    .cdb_valid_o(cdb_valid_o),

    // Data from/to the CDB
	.cdb_data_i(cdb_data_i),
	.cdb_data_o(cdb_data_o),
    //.cdb_idx_i(cdb_idx_i),
    //.cdb_data_i(cdb_data_i),
    //.cdb_except_raised_i(cdb_except_raised_i),
    //.cdb_idx_o(cdb_idx_o),
    //.cdb_data_o(cdb_data_o),
    //.cdb_except_raised_o(cdb_except_raised_o),
    //.cdb_except_o(cdb_except_o),

	// Control from/to the ROB
    .rob_head_idx_i(sb_head_idx_o),
    .rob_store_committing_o(rob_store_committing_o)

    // Hanshake from/to the CDB 
    //.cdb_lb_valid_i(cdb_lb_valid_i),
    //.cdb_sb_valid_i(cdb_sb_valid_i),
    //.cdb_lb_ready_i(cdb_lb_ready_i),
    //.cdb_sb_ready_i(cdb_sb_ready_i),
    //.lb_cdb_valid_o(lb_cdb_valid_o),
    //.sb_cdb_valid_o(sb_cdb_valid_o),

    // Data from/to the CDB
    //.cdb_lsb_data_i(cdb_lsb_data_i),
    //.lb_cdb_data_o(lb_cdb_data_o),
    //.sb_cdb_data_o(sb_cdb_data_o)
);

commit_logic u_commit_logic(
	.clk_i(clk_i),
    .rst_n_i(rst_n_i),
    // Control to the ROB
    .rob_valid_i(comm_valid_ROB_i),
    .rob_ready_o(comm_ready_ROB_o), 
	//.stall(stall),   

    // Data from the ROB
    .rob_instr_i(rob_instr_i),
    .rob_pc_i(rob_pc_i),
    .rob_rd_idx_i(rob_rd_idx_o),
    .rob_value_i(rob_value_i),
`ifdef LEN5_FP_EN
	.fp_rob_rd_idx_i(fp_rob_rd_idx_o),
	.fp_rob_value_i(fp_rob_value_i),
`endif /* LEN5_FP_EN */
    .rob_except_raised_i(rob_except_raised_o),
    .rob_except_code_i(rob_except_code_o),
    .rob_head_idx_i(rob_head_idx_i),

    // Conditions
    .sb_store_committing_i(rob_store_committing_o), // a store is ready to commit from the store buffer

	.rob_except_raised_o(except_raised_o),
	.rob_except_code_o(except_code_o),
	.except_new_o(except_o),
	.except_new_pc_o(except_pc_o),

	// HS from to the register status
    .int_rs_ready_i(comm_valid_i),
    .int_rs_valid_o(comm_ready_o),
`ifdef LEN5_FP_EN
    .fp_rs_ready_i(fp_comm_valid_i),
    .fp_rs_valid_o(fp_comm_ready_o),
`endif /* LEN5_FP_EN */

    // HS from to the register files
    .int_rf_ready_i(rf_comm_valid_i),
    .int_rf_valid_o(rf_comm_ready_o),
    
`ifdef LEN5_FP_EN
    .fp_rf_ready_i(fp_rf_comm_valid_i),
    .fp_rf_valid_o(fp_rf_comm_ready_o),
`endif /* LEN5_FP_EN */

    // Data to the register files
    .rf_rd_idx_o(comm_rd_idx_i),        // the index of the destination register (rd)
    .rf_value_o(comm_rd_value_i)        // the value to be stored in rd

`ifdef LEN5_FP_EN
,
	// Data to the fp register files
    .fp_rd_idx_o(fp_comm_rd_idx_i),        // the index of the destination register (rd)
    .fp_value_o(fp_comm_rd_value_i)          // the value to be stored in rd
`endif /* LEN5_FP_EN */
);

rob u_rob
(
    .clk_i                      (clk_i),
    .rst_n_i                    (rst_n_i),
    .flush_i                    (flush_i),
	//.stall(stall),
    .issue_valid_i              (rob_valid_o),
    .issue_ready_o              (rob_ready_i),
    .issue_rs1_idx_i            (rob_rs1_idx_i),        // ROB entry containing rs1 value 
    .issue_rs2_idx_i            (rob_rs2_idx_i),        // ROB entry containing rs2 value
    .issue_rs1_ready_o          (rob_rs1_ready_o),      // the result is ready
    .issue_rs1_value_o          (rob_rs1_value_o),      // the value of the first operand
    .issue_rs2_ready_o          (rob_rs2_ready_o),      // the result is ready
    .issue_rs2_value_o          (rob_rs2_value_o),  
    .issue_instr_i              (rob_instr_o),            // to identify the instruction
    .issue_pc_i                 (curr_pc_i),
    .issue_rd_idx_i             (rob_rd_idx_i),            // the destination register index (rd)
    .issue_except_raised_i      (rob_except_raised_i),     // an exception has been raised
    .issue_except_code_i        (rob_except_code_i),       // the exception code
    .issue_except_aux_i         (rob_except_aux_i),  
    .issue_res_ready_i          (rob_res_ready_o),
    .issue_res_value_i          (rob_res_value),
    .issue_tail_idx_o           (rob_tail_idx_o),
    .cdb_valid_i                (rob_cdb_valid_i),
    .cdb_ready_o                (rob_cdb_ready_o),
    .cdb_data_i                 (cdb_data_in),
    .comm_ready_i               (comm_ready_ROB_o),
    .comm_valid_o               (comm_valid_ROB_i),
    .comm_instr_o               (rob_instr_i),
    .comm_pc_o					(rob_pc_i),
    .comm_rd_idx_o              (rob_rd_idx_o),          // the destination register (rd)
    .comm_value_o               (rob_value_i),           // the result of the instruction
`ifdef LEN5_FP_EN
	.fp_comm_rd_idx_o           (fp_rob_rd_idx_o),          // the destination register (rd)
    .fp_comm_value_o            (fp_rob_value_i),           // the result of the instruction
`endif /* LEN5_FP_EN */
    .comm_except_raised_o       (rob_except_raised_o),
    .comm_except_code_o         (rob_except_code_o),
    .comm_head_idx_o            (rob_head_idx_i), //SOlve this 
    .sb_head_idx_o              (sb_head_idx_o)
); 

	assign 	rob_head_idx_o	=	rob_head_idx_i;    
    // assign  cdb_data_i_low_prio = cdb_data_i[1:EU_N-1];
    // assign  cdb_data_o_low_prio = cdb_data_o[1:EU_N-1];

cdb u_cdb(
    .clk_i(clk_i),
    .rst_n_i(rst_n_i),
    .flush_i(flush_i),
	//.stall(stall),

    // Handshake from/to the maximum priority EU
    .max_prio_valid_i(cdb_valid_o[0]),
    .max_prio_ready_o(cdb_ready_i[0]),

    // Data from the maximum priority EU
    .max_prio_data_i(cdb_data_o[0]),
	.max_prio_data_o(cdb_data_i[0]),

    // Handshake from/to the reservation stations
    .rs_valid_i(cdb_valid_o[1:EU_N-1]), 
    .rs_ready_o(cdb_ready_i[1:EU_N-1]),

    // Data from the reservation stations or issue queue.
    .rs_data_i(cdb_data_o[1:EU_N-1]),
	.rs_data_o(cdb_data_i[1:EU_N-1]),

	//New
	// Handshake from/to the cdb
	.cdb_valid_i(cdb_valid_i),
	.cdb_ready_o(cdb_ready_o),

	// Data from the cdb
	.cdb_except_raised_i(cdb_except_raised_i),
	.cdb_value_i(cdb_value_i),
	.cdb_rob_idx_i(cdb_rob_idx_i),

    // Handshake from/to the ROB
    .rob_ready_i(rob_cdb_ready_o),
    .rob_valid_o(rob_cdb_valid_i),

    // Data to the ROB
    .rob_data_o(cdb_data_in)
);      
    
endmodule

