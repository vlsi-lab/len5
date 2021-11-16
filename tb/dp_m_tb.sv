// TESTED AND WORKING

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module dp_m_tb;

// To the main control 
    logic    main_cu_stall_o;

    logic clk_i;
	logic rst_n_i;
	logic flush_i;
	satp_mode_t         vm_mode_i;

	// Data from fetch unit
	logic            except_raised_i;
	except_code_t    except_code_i;

	// From/to i-cache  :I$
 	logic             data_ready_o;

	// For pc_gen from or to back end// Input from intruction cache :I$
  	logic             except_i;
  	logic [XLEN-1:0]  except_pc_i;

	// From main unit
   	logic                 abort_i;
   	logic                 clr_l1tlb_mshr_i;
   	logic                 clr_l2tlb_mshr_i;
   	logic                 clear_dmshr_dregs_i; 

	// Update Block <-> d-Cache Updating Unit
  	logic                 synch_l1dc_l2c_i;
  	logic                 l2c_update_done_o;

	// LSQ <-> d-TLB
  	logic                 dtlb_lsq_req_rdy_o;

  	// LSQ <-> d-Cache
 	logic                 l1dc_lsq_req_rdy_o;

 	 // System -> TLBs/PTW
  	logic                 vmem_on_i;
  	logic                 sum_bit_i;
  	logic                 mxr_bit_i;
 	priv_e                priv_mode_i;
  	priv_e                priv_mode_ls_i;
  	asid_t                base_asid_i;
  	logic [PPN_LEN-1:0]   csr_root_ppn_i;
  	tlb_flush_e           L1TLB_flush_type_i;
  	tlb_flush_e           L2TLB_flush_type_i;
  	asid_t                flush_asid_i;
 	vpn_t                 flush_page_i;
	
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
    flush_i = 0;

	vm_mode_i=SV39;

    except_raised_i = 'b0;
    except_code_i = E_I_ACCESS_FAULT;
  	except_i  = 0;
  	except_pc_i = 'd0;
	
	abort_i  = 0;
   	clr_l1tlb_mshr_i  = 0;
   	clr_l2tlb_mshr_i  = 0;
   	clear_dmshr_dregs_i  = 0; 
	synch_l1dc_l2c_i  = 0;

	vmem_on_i  = 0;
  	sum_bit_i  = 0;
  	mxr_bit_i  = 0;

 	priv_mode_i  = U;
  	priv_mode_ls_i  = U;

  	base_asid_i  = 'd0;
  	csr_root_ppn_i  = 'd0;
  	L1TLB_flush_type_i  = NoFlush;
  	L2TLB_flush_type_i  = NoFlush;
  	flush_asid_i  = 'd0;
 	flush_page_i  = 'd0;
	
  	l2c_l2arb_req_rdy_i  = 0;
  	l2c_l2arb_ans_i  = 0;

        // reset
    #2 rst_n_i = 0;
    #10 rst_n_i = 1;

    #30 flush_i = 1;
    #10 flush_i = 0;

    #600 $finish;
end

// ---
// DUT
// ---

data_path_memory u_data_path_memory
(
	.clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	.vm_mode_i(vm_mode_i),
	.main_cu_stall_o(main_cu_stall_o),
	.data_ready_o(data_ready_o),
  	.except_i(except_i),
  	.except_pc_i(except_pc_i),
	.except_raised_i(except_raised_i),
  	.except_code_i(except_code_i),
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
	.dtlb_lsq_req_rdy_o(dtlb_lsq_req_rdy_o),
	.l1dc_lsq_req_rdy_o(l1dc_lsq_req_rdy_o),
 	.l2arb_l2c_req_o(l2arb_l2c_req_o),
  	.l2c_l2arb_req_rdy_i(l2c_l2arb_req_rdy_i),
  	.l2c_l2arb_ans_i(l2c_l2arb_ans_i),
  	.l2arb_l2c_ans_rdy_o(l2arb_l2c_ans_rdy_o) 
);

    
endmodule
