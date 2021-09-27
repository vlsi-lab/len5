// TESTED AND WORKING
`include "A_Back_end.sv"
//import mmm_pkg::*;
import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module Back_end_tb; // comment

// To the main control 
    logic    main_cu_stall_o;

    logic clk_i;
	logic rst_n_i;
	logic flush_i;
	satp_mode_t         vm_mode_i;

	// Handshake from/to fetch unit
	logic fetch_valid_i;
	logic fetch_ready_o;

	// Data from fetch unit
	logic [XLEN-1:0] curr_pc_i;
	logic [ILEN-1:0] instruction_i;
	logic [XLEN-1:0] pred_target_i;
	logic            pred_taken_i;
	logic            except_raised_i;
	except_code_t    except_code_i;

    // Data for execution unit
	branch_type_t               branch_type_i;
	ldst_type_t             	ldst_type_i;

	// Data to the FE 
	logic [XLEN-1:0]  res_pc_o;
  	logic [XLEN-1:0]  res_target_o;
  	logic             res_taken_o;
	logic 			  res_mispredict_o;

	// Handshake and data from/to the TLB
    dtlb_lsq_ans_t          dtlb_ans_i;
    dtlb_lsq_wup_t          dtlb_wup_i;
    lsq_dtlb_req_t          dtlb_req_o;

    // Handshake and data from/to the D$
    l1dc_lsq_ans_t          dcache_ans_i;
    l1dc_lsq_wup_t          dcache_wup_i;
   	lsq_l1dc_req_t          dcache_req_o;
	line_addr_t				line;

always #5 clk_i = ~clk_i;
always #10 instruction_i = instruction_i + 1;

initial begin
    //$monitor("Time = %0t -- instruction = 0x%8x, fetch ready = %0b", $time, instruction_i, fetch_ready_o);
    clk_i = 1;
    rst_n_i = 1;
    flush_i = 0;
    fetch_valid_i = 0;

	vm_mode_i=SV39;
	branch_type_i=BEQ;
	ldst_type_i=LS_WORD;

	dtlb_ans_i.ppn='h0;
	dtlb_ans_i.exception=NoException;
	dtlb_ans_i.was_store=0;
	dtlb_ans_i.lsq_addr=2'b00;
	dtlb_ans_i.valid=0;

	dtlb_wup_i.vpn='h0;
	dtlb_wup_i.valid=0;

	dcache_ans_i.data = 'h0;
	dcache_ans_i.was_store = 0;
	dcache_ans_i.lsq_addr = 2'b00;
	dcache_ans_i.valid = 0;

	line.tag = 'h0;
	line.idx = 'h0; 
	dcache_wup_i.line_addr=line;
	dcache_wup_i.valid=0;

    instruction_i = 'h00000001;
    curr_pc_i = 'h0000000000000000;
    pred_target_i = 'h0000000000000000;
    pred_taken_i = 'b0;
    except_raised_i = 'b0;
    except_code_i = E_I_ACCESS_FAULT;

        // reset
    #2 rst_n_i = 0;
    #10 rst_n_i = 1;

    #10 fetch_valid_i = 1;
    #20 fetch_valid_i = 0;
    #30 fetch_valid_i = 1;
    #20 fetch_valid_i = 0;
    #30 flush_i = 1;
    #10 flush_i = 0;
    #10 curr_pc_i = 'h0000000000000002;

    #600 $finish;
end

//---------------\\
//----- DUT -----\\
//---------------\\

back_end Back_end_IQL
(
    // To the main control 
    .main_cu_stall_o(main_cu_stall_o),

    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	.vm_mode_i(vm_mode_i),

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

    // Data for execution unit
	.branch_type_i(branch_type_i),
	.ldst_type_i(ldst_type_i),

	// Data to the FE 
	.res_pc_o(res_pc_o),
  	.res_target_o(res_target_o),
  	.res_taken_o(res_taken_o),
	.res_mispredict_o(res_mispredict_o),

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
