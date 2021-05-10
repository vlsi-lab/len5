// TESTED AND WORKING
//`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Data_path_memory.sv"
//`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/CU_DP_MEM.sv"
//import mmm_pkg::*;

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/l2cache_emulator/cache_L2_system_emulator.sv"
import len5_pkg::*;
import expipe_pkg::*;
import control_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module CU_DP_M_tb;

// To the main control 
    //logic    main_cu_stall_o;

    logic clk_i;
	logic rst_n_i;
	logic             flush_i;
	
  	// L2 Cache Arbiter <-> L2 Cache Emulator
	l2arb_l2c_req_t       l2arb_l2c_req_o;
  	logic                 l2c_l2arb_req_rdy_i;
  	l2c_l2arb_ans_t       l2c_l2arb_ans_i;
  	logic                 l2arb_l2c_ans_rdy_o;

always #5 clk_i = ~clk_i;
//always #10 instruction_i = instruction_i + 1;

initial begin
    //$monitor("Time = %0t -- instruction = 0x%8x, fetch ready = %0b", $time, instruction_i, fetch_ready_o);
    clk_i = 1;
    rst_n_i = 1;
	//l2c_l2arb_req_rdy_i =0;
  	//l2c_l2arb_ans_t       
	//l2c_l2arb_ans_i='d0;

        // reset
    #2 rst_n_i = 0;
    #20 rst_n_i = 1;

    //#600 $finish;
end

//---------------\\
//----- DUT -----\\
//---------------\\

CU_DP_MEM u_CU_DP_MEM
(
	.clk_i (clk_i),
    .rst_n_i (rst_n_i),
	.flush_i  (flush_i),
 	.l2arb_l2c_req_o(l2arb_l2c_req_o),
  	.l2c_l2arb_req_rdy_i(l2c_l2arb_req_rdy_i),
  	.l2c_l2arb_ans_i(l2c_l2arb_ans_i),
  	.l2arb_l2c_ans_rdy_o(l2arb_l2c_ans_rdy_o) 
);

cache_L2_system_emulator u_cache_L2_system_emulator
(
  // Main
	.clk_i    (clk_i),
    .rst_ni  (rst_n_i),
	.flush_i  (flush_i),
	.l2arb_l2c_req_i(l2arb_l2c_req_o),
  	.l2c_l2arb_req_rdy_o(l2c_l2arb_req_rdy_i),
  	.l2c_l2arb_ans_o(l2c_l2arb_ans_i),
  	.l2arb_l2c_ans_rdy_i(l2arb_l2c_ans_rdy_o) 
);

    
endmodule
