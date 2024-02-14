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

module byte_selector (
  input expipe_pkg::ldst_width_t type_i,  // load/store type (number of bytes to select)
  input logic [$clog2(len5_pkg::XLEN/8)-1:0] byte_off,  // the offset of the first byte to select
  input logic [len5_pkg::XLEN-1:0] data_i,  // the input line
  output logic [len5_pkg::XLEN-1:0] data_o  // the output line
);

  import len5_pkg::XLEN;
  import expipe_pkg::*;
  import memory_pkg::*;

  localparam int unsigned ByteLen = 8;  // number of bits in a byte

  // DEFINITIONS
  logic [4*ByteLen-1:0] selected_w;
  logic [2*ByteLen-1:0] selected_h;
  logic [1*ByteLen-1:0] selected_b;

  // -------------
  // BYTE SELECTOR
  // -------------
  // Three levels of multiplexer select the word, the halfword and the byte according to each offset bit.
  always_comb begin : byte_selector
    // First level MUX: select the first or the last word
    selected_w = (byte_off[2]) ? data_i[8*ByteLen-1-:4*ByteLen] : data_i[4*ByteLen-1-:4*ByteLen];
    // Second level MUX: select the first or the last halfword
    selected_h = (byte_off[1]) ? selected_w[4*ByteLen-1-:2*ByteLen] : selected_w[2*ByteLen-1-:2*ByteLen];
    // Third lecel MUX: select the first or the last byte
    selected_b = (byte_off[0]) ? selected_h[2*ByteLen-1-:1*ByteLen] : selected_h[1*ByteLen-1-:1*ByteLen];
  end

  // ---------------------------
  // SIGN EXTENSION/ZERO PADDING
  // ---------------------------
  // Perform the sign extension or the zero padding of the correct portion to generate the output line
  always_comb begin : line_generation
    case (type_i)
      // Load bite
      LS_BYTE:
      data_o = {{(XLEN - 1 * ByteLen) {selected_b[1*ByteLen-1]}}, selected_b};  // sign extension
      LS_BYTE_U: data_o = {{(XLEN - 1 * ByteLen) {1'b0}}, selected_b};  // zero padding

      // Load halfword
      LS_HALFWORD:
      data_o = {{(XLEN - 2 * ByteLen) {selected_h[2*ByteLen-1]}}, selected_h};  // sign extension
      LS_HALFWORD_U: data_o = {{(XLEN - 2 * ByteLen) {1'b0}}, selected_h};  // zero padding

      // Load word
      LS_WORD:
      data_o = {{(XLEN - 4 * ByteLen) {selected_w[4*ByteLen-1]}}, selected_w};  // sign extension
      LS_WORD_U: data_o = {{(XLEN - 4 * ByteLen) {1'b0}}, selected_w};  // zero padding

      // Load doubleword
      LS_DOUBLEWORD: data_o = data_i;

      default: data_o = data_i;
    endcase
  end

  // ----------
  // ASSERTIONS
  // ----------
`ifndef SYNTHESIS
`ifndef VERILATOR
  always_comb begin
    case (type_i)
      LS_HALFWORD, LS_HALFWORD_U:
      assert (!byte_off[0])
      else
        $error(
            $sformatf(
                "HALFOWORD instr. with misaligned byte offset '%b' proceeded to cache. This must be avoided!",
                byte_off
            )
        );
      LS_WORD, LS_WORD_U:
      assert (byte_off[1:0] == 2'b00)
      else
        $error(
            $sformatf(
                "WORD instr. with misaligned byte offset '%b' proceeded to cache. This must be avoided!",
                byte_off
            )
        );
      default: ;
    endcase
  end
`endif  /* VERILATOR */
`endif  /* SYNTHESIS */

endmodule
