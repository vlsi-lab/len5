// Copyright 2024 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: rr_arbiter.sv
// Author: Michele Caon
// Date: 01/03/2024

module rr_arbiter #(
  parameter int unsigned N = 4
) (
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i,

  // Handshake from/to the units
  input  logic [N-1:0] valid_i,
  output logic [N-1:0] ready_o,

  // Handshake from/to the ROB
  output logic valid_o,
  input  logic ready_i,

  // To the CDB MUX
  output logic [$clog2(N)-1:0] served_o
);
  // DEFINITIONS
  logic [N-1:0] rem_valid_q, msk_valid_d;

  // Valid MUX
  logic [        N-1:0] mux_valid;

  // Valid priority encoder + decoder
  logic [$clog2(N)-1:0] enc_out;
  logic                 enc_valid;
  logic [        N-1:0] dec_valid_d;

  // ---------
  // VALID MUX
  // ---------
  // If there's no remaining valid signal, than select the new valids from the input
  assign mux_valid = (|rem_valid_q) ? rem_valid_q : valid_i;

  // ----------------------
  // VALID PRIORITY ENCODER
  // ----------------------
  prio_enc #(
    .N  (N),
    .INV(1'b1)
  ) vaild_prio_enc (
    .lines_i(mux_valid),
    .enc_o  (enc_out),
    .valid_o(enc_valid)
  );

  // Decoder:
  always_comb begin : valid_dec
    dec_valid_d = '0;  // all zeros by default
    if (enc_valid) begin  // if at least one valid is active
      dec_valid_d[enc_out] = 1'b1;
    end
  end

  // -------------------
  // VALID MASKING LOGIC
  // -------------------
  assign msk_valid_d = mux_valid & ~dec_valid_d;

  // -----------------
  // OUTPUT GENERATION
  // -----------------
  // Output valid
  assign valid_o     = |dec_valid_d;

  // Output ready
  always_comb begin : ready_mux
    if (ready_i) ready_o = dec_valid_d;  // notify the unit being served
    else ready_o = '0;  // by default, no input is served
  end

  // Output served index
  assign served_o = enc_out;

  // ------------------------
  // REMAINING VALID REGISTER
  // ------------------------
  always_ff @(posedge clk_i or negedge rst_ni) begin : last_served_reg
    if (!rst_ni) begin
      rem_valid_q <= '0;
    end else if (flush_i) begin
      rem_valid_q <= '0;
    end else begin
      rem_valid_q <= msk_valid_d;
    end
  end

endmodule
