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

module div 
#(
    RS_DEPTH = 4, // must be a power of 2,
    
    // EU-specific parameters
    EU_CTL_LEN = 4,
    EXCEPT_LEN = 2
)
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,

    // Handshake from/to the reservation station unit
    input   logic                   valid_i,
    input   logic                   ready_i,
    output  logic                   ready_o,
    output  logic                   valid_o,

    // Data from/to the reservation station unit
    input   logic [EU_CTL_LEN-1:0]  ctl_i,
    input   logic [$clog2(RS_DEPTH)-1:0] entry_idx_i,
    input   logic [XLEN-1:0]        rs1_value_i,
    input   logic [XLEN-1:0]        rs2_value_i,
    output  logic [$clog2(RS_DEPTH)-1:0] entry_idx_o,
    output  logic [XLEN-1:0]        result_o,
    output  logic                   except_raised_o,
    output  logic [EXCEPT_LEN-1:0]  except_code_o
);

	// Main counting process. The counter clears when reaching the threshold
always_ff @ (posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        ready_o <= 0; // Asynchronous reset
		valid_o <= 0;
		entry_idx_o <= 'b000;
		result_o <= 'h0000000000000000;
		except_raised_o <= 0;
		except_code_o <= 'd0;
    end
    else if (flush_i) begin
        ready_o <= 0; // Synchronous clear when requested or when reaching the threshold
		valid_o <= 0;
		entry_idx_o <= 'b000;
		result_o <= 'h0000000000000000;
		except_raised_o <= 0;
		except_code_o <= 'd0;
    end
	else if (ready_i) begin
		//case () begin
		entry_idx_o <= entry_idx_i;
		ready_o <= 1;
        result_o <= (rs2_value_i != 'd0)? rs1_value_i / rs2_value_i : 'd0;

		if (valid_i) begin
		valid_o <= 1;
		end
    end
	else begin
		ready_o = 1;
		result_o <= 'h0000000000000000;
		entry_idx_o <= 'b000;
		valid_o <= 0;
		result_o <= 'h0000000000000000;
		except_raised_o <= 0;
		except_code_o <= 'd0;
end
end

endmodule
