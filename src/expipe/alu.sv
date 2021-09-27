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
// File: generic_rs.sv
// Author: Michele Caon
// Date: 21/10/2019

import len5_pkg::XLEN;
import len5_pkg::ILEN;
import expipe_pkg::*;

module alu 
#(
    RS_DEPTH = 16,
    
    // EU-specific parameters
    EU_CTL_LEN = 4,
    EXCEPT_LEN = 2
)
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,

    // Handshake from/to the reservation station unit
    output   logic                   eu_ready_i,
    output   logic                   eu_valid_i,
    input  logic                   eu_valid_o,
    input  logic                   eu_ready_o,

    // Data from/to the reservation station unit
    //input   logic [$clog2(RS_DEPTH)-1:0] eu_entry_idx_i,
    output   logic [3-1:0] eu_entry_idx_i,
    output   logic [XLEN-1:0]        eu_result_i,
    output   logic                   eu_except_raised_i,
    output   logic [EXCEPT_LEN-1:0]  eu_except_code_i,
    input  logic [EU_CTL_LEN-1:0]  eu_ctl_o,
    input  logic [XLEN-1:0]        eu_rs1_o,
    input  logic [XLEN-1:0]        eu_rs2_o,
    //output  logic [$clog2(RS_DEPTH)-1:0] eu_entry_idx_o,   // to be produced at the end of execution together with the result
    input  logic [3-1:0] eu_entry_idx_o
);

//logic [3-1:0]       eu_entry_idx_temp;
//logic [XLEN-1:0]     eu_result_temp;
	// Main counting process. The counter clears when reaching the threshold
always_ff @ (posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        eu_ready_i <= 0; // Asynchronous reset
		eu_valid_i <= 0;
		eu_entry_idx_i = 'b000;
		eu_result_i <= 'h0000000000000000;
		eu_except_raised_i <= 0;
		eu_except_code_i <= 'd0;
    end
    else if (flush_i) begin
        eu_ready_i <= 0; // Synchronous clear when requested or when reaching the threshold
		eu_valid_i <= 0;
		eu_entry_idx_i = 'b000;
		eu_result_i <= 'h0000000000000000;
		eu_except_raised_i <= 0;
		eu_except_code_i <= 'd0;
    end
    else if (eu_ready_o) begin
		//case () begin
        //eu_result_temp <= (eu_ctl_o)? eu_rs1_o - eu_rs2_o : eu_rs1_o + eu_rs2_o;
		eu_entry_idx_i <= eu_entry_idx_o;
		eu_ready_i = 1;
		// R-FORMAT INSTRUCTIONS
        
        // ADD
        if (eu_ctl_o == ALU_ADD) begin
            eu_result_i <= eu_rs1_o + eu_rs2_o;
        end
        // ADDW
        else if (eu_ctl_o == ALU_ADDW) begin
            eu_result_i <= eu_rs1_o + eu_rs2_o;
        end
        // AND
        else if (eu_ctl_o == ALU_AND) begin
            eu_result_i <= eu_rs1_o + eu_rs2_o;
        end
        // OR
        else if (eu_ctl_o == ALU_OR) begin
            eu_result_i <= eu_rs1_o || eu_rs2_o;
        end
        
        // SLL
        else if (eu_ctl_o == ALU_SLL) begin
            eu_result_i <= eu_rs1_o << eu_rs2_o;
        end
        // SLLW
        else if (eu_ctl_o == ALU_SLLW) begin
            eu_result_i <= eu_rs1_o << eu_rs2_o;
        end
        // SLT
        else if (eu_ctl_o == ALU_SLT) begin
            eu_result_i <= (eu_rs1_o < eu_rs2_o)? 'd1 : 'd0;
        end
        // SLTU
        else if (eu_ctl_o == ALU_SLTU) begin
            eu_result_i <= (eu_rs1_o < eu_rs2_o)? 'd1 : 'd0;
        end
        // SRA
        else if (eu_ctl_o == ALU_SRA) begin
            eu_result_i <= eu_rs1_o >>> eu_rs2_o;
        end
        // SRAW
        else if (eu_ctl_o == ALU_SRAW) begin
            eu_result_i <= eu_rs1_o >>> eu_rs2_o;
        end
        // SRL
        else if (eu_ctl_o == ALU_SRL) begin
            eu_result_i <= eu_rs1_o >> eu_rs2_o;
        end
        // SRLW
        else if (eu_ctl_o == ALU_SRLW) begin
            eu_result_i <= eu_rs1_o >> eu_rs2_o;
        end
        // SUB
        else if (eu_ctl_o == ALU_SUB) begin
            eu_result_i <= eu_rs1_o - eu_rs2_o;
        end
        // SUBW
        else if (eu_ctl_o == ALU_SUBW) begin
            eu_result_i <= eu_rs1_o - eu_rs2_o;
        end
        // XOR
        else if (eu_ctl_o == ALU_XOR) begin
            eu_result_i <= (eu_rs1_o && !eu_rs2_o) || (!eu_rs1_o && eu_rs2_o);
        end
        else begin
            eu_result_i <= 'd0;
        end
		eu_valid_i <= (eu_valid_o)?1:0;
		//eu_valid_i <= 0;
		//if (eu_valid_o) begin
		//eu_result_i <= eu_result_temp;
		//eu_entry_idx_i <= eu_entry_idx_temp;
		//eu_valid_i <= 1;
		//end
            
    end
	/*else if (eu_valid_o) begin// Swap with above I did
		//case () begin
        eu_result_i <= eu_result_temp;
		eu_entry_idx_i <= eu_entry_idx_temp;
		eu_valid_i <= 1;
    end*/
	else begin
		eu_ready_i = 1;
		eu_result_i <= 'h0000000000000000;
		eu_entry_idx_i <= 'b000;
		eu_valid_i <= 0;
		eu_result_i <= 'h0000000000000000;
		eu_except_raised_i <= 0;
		eu_except_code_i <= 'd0;
end
end


endmodule
