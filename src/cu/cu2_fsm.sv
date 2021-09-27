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
// File: CU_FSM.sv
// Author: WALID
// Date: 07/10/2019

/* Include instruction definitions */
`include "instr_macros.svh"

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module cu2_fsm
(
	// From :TB
  	input   logic             	clk_i,
  	input   logic             	rst_n_i,

	// To the main control :CU 
  	input  	logic             	main_cu_stall_o,
	input   logic [ILEN-1:0] 	ins_in,
	output  logic 				stall,
  	
	// For pc_gen from or to back end// Input from intruction cache :I$
  	//input   logic             	except_i,
  	//input   logic [XLEN-1:0]  	except_pc_i,

  	// Data from intruction fetch unit cache // Fix_it from backend i.e., input from data cahce :D$
  	input   logic             	except_raised_i,
  	input   except_code_t     	except_code_i
);

	logic [OPCODE_LEN -1:0]        instr_opcode;
    logic [FUNCT3_LEN -1:0]        instr_funct3;

	assign instr_opcode     = 	ins_in[OPCODE_LEN-1 : 0];
    assign instr_funct3     = 	ins_in[14 -: FUNCT3_LEN];

	typedef enum logic [2:0] { RESET, OP_STATE, EXCEPT_I_MEM_STAGE, EXCEPT_RAISE_STAGE, STALL_STAGE } state_t;
  	state_t present_state, next_state;

  // State transition
  	always_ff @ (posedge clk_i or negedge rst_n_i) begin
    // Async reset
    	if (!rst_n_i) begin
      		present_state 	<= 	RESET;
    	//end else begin
    	//if (flush_i) begin
        	//present_state 	<= 	OP_STATE;
    	end else begin
        	present_state 	<= 	next_state;
    	end
    	//end
  	end

  	// State update
  	always_comb begin
    // Defaults
    	next_state 	= 	RESET;

    case (present_state)
      	RESET: begin
        	next_state 	= 	OP_STATE;
      	end

      	OP_STATE: begin  // Fix these are just states move it to output
			if 		((/*!except_i ||*/ !except_raised_i) && (instr_opcode == `OPCODE_BEQ || instr_opcode == `OPCODE_LB || instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA)) begin
            		next_state 	= 	OP_STATE;
    		end
			//else if (except_i) begin
            	//	next_state 	= 	EXCEPT_I_MEM_STAGE;
    		//end
			else if (except_raised_i) begin
            		next_state 	= 	EXCEPT_RAISE_STAGE;
    		end
			else  begin
            		next_state 	= 	OP_STATE;
    		end
      	end

      	EXCEPT_I_MEM_STAGE: begin
        if 		((/*!except_i ||*/ !except_raised_i) && (instr_opcode == `OPCODE_BEQ || instr_opcode == `OPCODE_LB || instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA)) begin
            		next_state 	= 	OP_STATE;
    		end
			/*else if (except_i) begin
            		next_state 	= 	EXCEPT_I_MEM_STAGE;
    		end*/
			else if (except_raised_i) begin
            		next_state 	= 	EXCEPT_RAISE_STAGE;
    		end
			else  begin
            		next_state 	= 	OP_STATE;
    		end
      	end

      	EXCEPT_RAISE_STAGE: begin
        	if 		((/*!except_i ||*/ !except_raised_i) && (instr_opcode == `OPCODE_BEQ || instr_opcode == `OPCODE_LB || instr_opcode == `OPCODE_FENCE || instr_opcode == `OPCODE_SFENCE_VMA)) begin
            		next_state 	= 	OP_STATE;
    		end
			/*else if (except_i) begin
            		next_state 	= 	EXCEPT_I_MEM_STAGE;
    		end*/
			else if (except_raised_i) begin
            		next_state 	= 	EXCEPT_RAISE_STAGE;
    		end
			else  begin
            		next_state 	= 	OP_STATE;
    		end
      	end
    	endcase
  	end
	// Output update
  	always_comb begin
		stall	 				= 	0;

    case (present_state)
      	RESET: begin
        	//flush_i 				= 	1;
			stall	 				= 	0;//should it be 1 ?
      	end

      	OP_STATE: begin  
			if ((instr_opcode == `OPCODE_FENCE) && (instr_funct3 == `FUNCT3_FENCE_I)) begin
            	
    		end
			else if ((instr_opcode == `OPCODE_SFENCE_VMA) && (instr_funct3 == `FUNCT3_SFENCE_VMA) /*&& (!l2c_update_done_o)*/) begin//Fix
            		
    		end
			else  begin
   
    		end
      	end

      	EXCEPT_I_MEM_STAGE: begin
       	 			stall	 				= 	1;
      	end

      	EXCEPT_RAISE_STAGE: begin
	
      	end

      	//STALL_STAGE: begin
      	//end
    	endcase
  	end

//-----

endmodule
