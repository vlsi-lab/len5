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
// File: commit_decoder.sv
// Author: Michele Caon
// Date: 20/11/2019

// THIS FILE IS ONYL A TEMPLATE, THE COMMIT LOGIC IS NOT IMPLEMENTED YET, SINCE IT REQUIRES ALL THE PROCESSOR PARTS TO BE FUNCTIONAL

/* Include instruction macros */
`include "instr_macros.svh"

import expipe_pkg::*;
import len5_pkg::ILEN;
import len5_pkg::OPCODE_LEN;
import len5_pkg::instr_t;

module commit_decoder 
(
    // Data from the commit logic
    input   instr_t                 instruction_i,

    // Conditions
    input   logic                   sb_store_committing_i,

	input   logic                   rob_valid_i,
	input   logic                   no_exception_i,
	input   logic                   int_rs_ready_i,
	input   logic                   fp_rs_ready_i,
	input   logic                   int_rf_ready_i,
	input   logic                   fp_rf_ready_i,
	input   logic                   mispredict_i,

    // Control to the commit logic
    output  logic                   comm_possible_o    
);

    // DEFINITIONS
    logic [OPCODE_LEN -1:0]       instr_opcode;
    
    // -------------------
    // EXTRACT INSTR. INFO
    // -------------------
    assign instr_opcode             = instruction_i.r.opcode;

    // --------------------
    // COMMIT DOCODER LOGIC
    // --------------------
    always_comb begin: comm_decoder
        case(instr_opcode)
            // If the committing instruction is a store, check if it is also committing from the store buffer
            `OPCODE_SB: begin
                comm_possible_o = (sb_store_committing_i) ? 1'b1 : 1'b0;
            end
			`OPCODE_BEQ: begin
                comm_possible_o = (rob_valid_i && no_exception_i && !mispredict_i) ? 1'b1 : 1'b0;
            end
			`OPCODE_FENCE: begin
                comm_possible_o = (rob_valid_i && no_exception_i) ? 1'b1 : 1'b0;
            end
	       	//`OPCODE_MTYPE, See it. Only mult and div types
       		`OPCODE_ADD, `OPCODE_ADDI, `OPCODE_ADDIW, `OPCODE_ADDW, `OPCODE_LUI, `OPCODE_JAL, `OPCODE_JALR: begin // complete it later also jump
                comm_possible_o = (rob_valid_i && no_exception_i && int_rf_ready_i && int_rs_ready_i) ? 1'b1 : 1'b0;
            end
			// Do here for floating point loads
			`OPCODE_LD: begin // complete it later , `OPCODE_FTYPE, `OPCODE_DTYPE, `OPCODE_QTYPR
                comm_possible_o = (rob_valid_i && no_exception_i && fp_rf_ready_i && fp_rs_ready_i) ? 1'b1 : 1'b0;
            end

            default: comm_possible_o = 1'b0; // normally commit without further checks
        endcase
    end
    
endmodule
