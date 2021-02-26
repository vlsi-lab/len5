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
// File: byte_selector.sv
// Author: Michele Caon
// Date: 01/11/2019

`include "expipe_pkg.sv"
`include "len5_pkg.sv"
    
`define BYTE *8 // 1 byte = 8 bits

module byte_selector
    import expipe_pkg::*;
    import len5_pkg::XLEN;
(
    input ldst_type_t type_i, // load/store type (number of bytes to select)
    //input logic [$clog2(XLEN/8)-1:0] byte_off, // the offset of the first byte to select
input logic [3-1:0] byte_off, // the offset of the first byte to select
    input logic [XLEN-1:0] line_i, // the input line
    output logic [XLEN-1:0] line_o // the output line
);

    // DEFINITIONS
    logic [4`BYTE-1:0] selected_w;
    logic [2`BYTE-1:0] selected_h;
    logic [1`BYTE-1:0] selected_b;

    //-------------------------\\
    //----- BYTE SELECTOR -----\\
    //-------------------------\\
    // Three levels of multiplexer select the word, the halfword and the byte according to each offset bit.
    always_comb begin: byte_selector 
        // First level MUX: select the first or the last word
        selected_w = (byte_off[2]) ? line_i[8`BYTE-1 -: 4`BYTE] : line_i[4`BYTE-1 -: 4`BYTE];
        // Second level MUX: select the first or the last halfword
        selected_h = (byte_off[1]) ? selected_w[4`BYTE-1 -: 2`BYTE] : selected_w[2`BYTE-1 -: 2`BYTE];
        // Third lecel MUX: select the first or the last byte
        selected_b = (byte_off[0]) ? selected_h[2`BYTE-1 -: 1`BYTE] : selected_h[1`BYTE-1 -: 1`BYTE];
    end

    //---------------------------------------\\
    //----- SIGN EXTENSION/ZERO PADDING -----\\
    //---------------------------------------\\
    // Perform the sign extension or the zero padding of the correct portion to generate the output line
    always_comb begin: line_generation
        case(type_i)
            // Load bite
            LS_BYTE: line_o = { {(XLEN-1`BYTE){selected_b[1`BYTE-1]}}, selected_b }; // sign extension
            LS_BYTE_U: line_o = { {(XLEN-1`BYTE){1'b0}}, selected_b}; // zero padding

            // Load halfword
            LS_HALFWORD: line_o = { {(XLEN-2`BYTE){selected_h[2`BYTE-1]}}, selected_h }; // sign extension
            LS_HALFWORD_U: line_o = { {(XLEN-2`BYTE){1'b0}}, selected_h}; // zero padding

            // Load word
            LS_WORD: line_o = { {(XLEN-4`BYTE){selected_w[4`BYTE-1]}}, selected_w }; // sign extension
            LS_WORD_U: line_o = { {(XLEN-4`BYTE){1'b0}}, selected_w}; // zero padding

            // Load doubleword
            LS_DOUBLEWORD: line_o = line_i;
            
            default: line_o = line_i;
        endcase
    end

    //----------------------\\
    //----- ASSERTIONS -----\\
    //----------------------\\
    `ifndef SYNTHESIS
    always_comb begin
        case(type_i)
            LS_HALFWORD, LS_HALFWORD_U: assert (!byte_off[0]) else $warning("%s instr. with misaligned byte offset \'%b\' proceeded to cache access/fwd stage. This must be avoided!", type_i.name(), byte_off); 
            LS_WORD, LS_WORD_U: assert (byte_off[1:0] == 2'b00) else $warning("%s instr. with misaligned byte offset \'%b\' proceeded to cache access/fwd stage. This must be avoided!", type_i.name(), byte_off); 
            default:;
        endcase
    end
    `endif
    
endmodule
