// TESTED AND WORKING

`include "/frontend/front_end.sv"

//import mmm_pkg::*;
import len5_pkg::*;
//import expipe_pkg::*;
//import memory_pkg::*;
//import csr_pkg::*;

module front_end_tb;

    logic clk_i;
	logic rst_n_i;
	logic flush_i;

    logic [XLEN-1:0]  addr_o;
  	logic             addr_valid_o;
  	logic             addr_ready_i;
  	icache_out_t      data_i;
  	logic             data_valid_i;
  	logic             data_ready_o;

  	// From/to instruction decode
  	logic             issue_ready_i;
  	logic             issue_valid_o;
  	logic [ILEN-1:0]  instruction_o;
  	prediction_t      pred_o;

  	// From branch unit (ex stage)
  	resolution_t      res_i;

  	// For pc_gen from or to back end
  	logic             except_i;
  	logic [XLEN-1:0]  except_pc_i;

always #5 clk_i = ~clk_i;
//always #10 instruction_i = instruction_i + 1;

initial begin
    //$monitor("Time = %0t -- instruction = 0x%8x, fetch ready = %0b", $time, instruction_i, fetch_ready_o);
    clk_i = 1;
    rst_n_i = 1;
    flush_i = 0;
    except_i = 0;
    except_pc_i = 'h0;
	issue_ready_i = 0;
    addr_ready_i = 0;
	data_valid_i = 0;

  	data_i.pc= 'h0;
	data_i.line=  {'h0, 'h0, 'h0, 'h0};
	res_i.pc = 'h0;
	res_i.target = 'h0;
	res_i.taken = 0;
	res_i.valid = 0;
	res_i.mispredict = 0;


        // reset
    #2 rst_n_i = 0;
    #10 rst_n_i = 1;

    #10 issue_ready_i = 1;
    #20 issue_ready_i = 0;
	#10 except_i = 1;
    #30 issue_ready_i = 1;
	#10 except_i = 0;
    #20 issue_ready_i = 0;
	#10 addr_ready_i = 1;
	#10 data_valid_i = 1;
    #30 flush_i = 1;
    #10 flush_i = 0;
    #10 except_pc_i = 'h0000000000000002;

    #600 $finish;
end

// ---
// DUT
// ---

front_end #(.HLEN(4),.BTB_BITS(4)) u_front_end
(
  	.clk_i    (clk_i),
    .rst_n_i  (rst_n_i),
    .flush_i  (flush_i),

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
    
endmodule
