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

import len5_pkg::*;
import expipe_pkg::*;
import csr_pkg::FCSR_FRM_LEN;

module fpu 
#(
    RS_DEPTH = 4, // must be a power of 2,
    
    // EU-specific parameters
    EU_CTL_LEN = 4
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
    output   logic [$clog2(RS_DEPTH)-1:0] eu_entry_idx_i,
    output   logic [XLEN-1:0]        eu_result_i,
    output   logic                   eu_except_raised_i,
    output   except_code_t          eu_except_code_i,
    input  logic [EU_CTL_LEN-1:0]  eu_ctl_o,
    input  logic [XLEN-1:0]        eu_rs1_o,
    input  logic [XLEN-1:0]        eu_rs2_o,
    output  logic [$clog2(RS_DEPTH)-1:0] eu_entry_idx_o,  // to be produced at the end of execution together with the result

    // fcsr data
    input   logic [FCSR_FRM_LEN-1:0]    csr_frm_i   // global rounding mode from fcsr
);
	// Main counting process. The counter clears when reaching the threshold
always_ff @ (posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        eu_ready_i <= 0; // Asynchronous reset
		eu_valid_i <= 0;
		eu_entry_idx_i = 'b000;
		eu_result_i <= 'h0000000000000000;
		eu_except_raised_i <= 0;
		eu_except_code_i <= E_UNKNOWN;
    end
    else if (flush_i) begin
        eu_ready_i <= 0; // Synchronous clear when requested or when reaching the threshold
		eu_valid_i <= 0;
		eu_entry_idx_i = 'b000;
		eu_result_i <= 'h0000000000000000;
		eu_except_raised_i <= 0;
		eu_except_code_i <= E_UNKNOWN;
    end
      /* else if (eu_valid_o) begin
		//case () begin
        eu_result_temp <=  eu_rs1_o * eu_rs2_o;
		eu_entry_idx_temp <= eu_entry_idx_o;
		eu_ready_i = 1;
    end*/
	else if (eu_ready_o) begin
		//case () begin
		eu_entry_idx_i <= eu_entry_idx_o;
		eu_ready_i = 1;
        eu_result_i <= (eu_rs2_o != 'd0)? eu_rs1_o / eu_rs2_o : 'd0;

		if (eu_valid_o) begin
		eu_valid_i <= 1;
		end
    end
	else begin
		eu_ready_i = 1;
		eu_result_i <= 'h0000000000000000;
		eu_entry_idx_i <= 'b000;
		eu_valid_i <= 0;
		eu_result_i <= 'h0000000000000000;
		eu_except_raised_i <= 0;
		eu_except_code_i <= E_UNKNOWN;
end
end

endmodule
