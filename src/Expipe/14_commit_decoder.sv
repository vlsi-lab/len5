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

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/expipe_pkg.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/len5_pkg.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/control_pkg.sv"

import expipe_pkg::*;
import len5_pkg::ILEN;

module commit_decoder (
    // Data from the commit logic
    input   logic [ILEN-1:0]        instruction_i,

    // Conditions
    input   logic                   sb_store_committing_i,

    // Control to the commit logic
    output  logic                   comm_possible_o    
);

    // DEFINITIONS
    logic [`OPCODE_LEN -1:00]       instr_opcode;
    
    //-------------------------------\\
    //----- EXTRACT INSTR. INFO -----\\
    //-------------------------------\\
    assign instr_opcode             = instruction_i[`OPCODE_LEN -1:0];

    //--------------------------------\\
    //----- COMMIT DOCODER LOGIC -----\\
    //--------------------------------\\
    always_comb begin: comm_decoder
        case(instr_opcode)
            // If the committing instruction is a store, check if it is also committing from the store buffer
            `OPCODE_SB, `OPCODE_SD, `OPCODE_SH, `OPCODE_SW: begin
                comm_possible_o = (sb_store_committing_i) ? 1'b1 : 1'b0;
            end

            default: comm_possible_o = 1'b1; // normally commit without further checks
        endcase
    end
    
endmodule
