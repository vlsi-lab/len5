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
// File: cdb_arbiter.sv
// Author: Michele Caon
// Date: 11/11/2019

module cdb_arbiter (
  input logic clk_i,
  input logic rst_n_i,
  input logic flush_i,


  // Handshake from/to the maximum priority unit
  input  logic max_prio_valid_i,
  output logic max_prio_ready_o,

  // Handshake from/to the units
  input  logic [len5_config_pkg::MAX_EU_N-2:0] valid_i,
  output logic [len5_config_pkg::MAX_EU_N-2:0] ready_o,

  // Handshake from/to the ROB
  input  logic rob_ready_i,
  output logic rob_valid_o,

  // To the CDB MUX
  output logic                                         served_max_prio_o,
  output logic [$clog2(len5_config_pkg::MAX_EU_N)-1:0] served_o
);

  import len5_config_pkg::MAX_EU_N;
  import expipe_pkg::*;

  // DEFINITIONS
  logic [MAX_EU_N-2:0] rem_valid_q, msk_valid_d;

  // Valid MUX
  logic [          MAX_EU_N-2:0] mux_valid;

  // Valid priority encoder + decoder
  logic [$clog2(MAX_EU_N-1)-1:0] enc_out;
  logic                          enc_valid;
  logic [          MAX_EU_N-2:0] dec_valid_d;

  // ---------
  // VALID MUX
  // ---------
  // If there's no remaining valid signal, than select the new valids from the input
  assign mux_valid = (|rem_valid_q) ? rem_valid_q : valid_i;

  // ----------------------
  // VALID PRIORITY ENCODER
  // ----------------------
  prio_enc_inv #(
    .N(MAX_EU_N - 1)
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
  always_comb begin : valid_msk_logic
    // If the maximum priority line is active, keep all other requests
    if (max_prio_valid_i) msk_valid_d = mux_valid;
    // Otherwise keep all but the currently served one
    else
      msk_valid_d = mux_valid & ~dec_valid_d;
  end

  // -----------------
  // OUTPUT GENERATION
  // -----------------
  // Output valid
  assign rob_valid_o      = max_prio_valid_i | (|dec_valid_d);

  // Output ready
  assign max_prio_ready_o = 1'b1;  // the maximum priority channel is always served
  always_comb begin : ready_mux
    if (!max_prio_valid_i && rob_ready_i) ready_o = dec_valid_d;  // notify the unit being served
    else ready_o = '0;  // by default, no input is served
  end

  // Output served index
  assign served_max_prio_o = max_prio_valid_i;
  assign served_o          = enc_out;

  // ------------------------
  // REMAINING VALID REGISTER
  // ------------------------
  always_ff @(posedge clk_i or negedge rst_n_i) begin : last_served_reg
    if (!rst_n_i) begin
      rem_valid_q <= 0;
    end else if (flush_i) begin
      rem_valid_q <= 0;
    end else begin
      rem_valid_q <= msk_valid_d;
    end
  end

endmodule
