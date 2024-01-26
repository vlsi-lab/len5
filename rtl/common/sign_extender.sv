// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: sign_extender.sv
// Author: Michele Caon
// Date: 19/08/2022

import expipe_pkg::*;
import len5_pkg::XLEN;
import memory_pkg::*;

module sign_extender
(
    input   ldst_width_t                type_i, // load/store type (number of bytes to select)
    input   logic [XLEN-1:0]            data_i,
    output  logic [XLEN-1:0]            data_o
);
    localparam int unsigned BYTE = 8; // number of bits in a byte

    // Sign extension/zero padding
    // ---------------------------
    always_comb begin: line_generation
        case(type_i)
            // Load bite
            LS_BYTE: data_o = { {(XLEN-1*BYTE){data_i[1*BYTE-1]}}, data_i[1*BYTE-1:0] }; // sign extension
            LS_BYTE_U: data_o = { {(XLEN-1*BYTE){1'b0}}, data_i[1*BYTE-1:0]}; // zero padding

            // Load halfword
            LS_HALFWORD: data_o = { {(XLEN-2*BYTE){data_i[2*BYTE-1]}}, data_i[2*BYTE-1:0] }; // sign extension
            LS_HALFWORD_U: data_o = { {(XLEN-2*BYTE){1'b0}}, data_i[2*BYTE-1:0]}; // zero padding

            // Load word
            LS_WORD: data_o = { {(XLEN-4*BYTE){data_i[4*BYTE-1]}}, data_i[4*BYTE-1:0] }; // sign extension
            LS_WORD_U: data_o = { {(XLEN-4*BYTE){1'b0}}, data_i[4*BYTE-1:0]}; // zero padding

            // Load doubleword
            default: data_o = data_i;
        endcase
    end

endmodule
