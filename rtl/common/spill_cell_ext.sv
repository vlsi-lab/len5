// Copyright 2021 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: spill_cell_ext.sv
// Author: Michele Caon
// Date: 26/11/2021

// ----------
// SPILL CELL
// ----------
// Spill cell to interrupt a combinational path with handshaking. When the
// downstream hardware is not ready, buffer input data on a spill register
// and lower the output ready for the upstream hardware in the next cycle.

module spill_cell_ext #(
  parameter type DATA_T = logic,
  parameter bit  SKIP   = 1'b0
) (
  // Clock, reset, and flush
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i,

  // Handshaking signals
  input  logic valid_i,  // from upstream hardware
  input  logic ready_i,  // from downstream hardware
  output logic valid_o,  // to downstream hardware
  output logic ready_o,  // to upstream hardware

  // Input and output data
  input  DATA_T data_i,
  output DATA_T data_o,
  output logic  buff_full_o,  // also the spill cell buffer is full
  output DATA_T buff_data_o   // spill cell buffer data
);
  // Bypass internal logic
  generate
    if (SKIP) begin : gen_skip_cell_gen
      assign valid_o     = valid_i;
      assign ready_o     = ready_i;
      assign data_o      = data_i;
      assign buff_full_o = 1'b0;
      assign buff_data_o = '0;
    end else begin : gen_spill_cell_gen
      // ----------------
      // INTERNAL SIGNALS
      // ----------------

      // Control signals
      logic  a_en;
      logic  b_en;
      logic  b_sel;

      // Register data
      logic  buff_full;
      DATA_T a_data_q;
      DATA_T b_data_q;

      // ------------
      // CONTROL UNIT
      // ------------

      spill_cell_ext_cu u_spill_cell_cu (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .flush_i    (flush_i),
        .valid_i    (valid_i),
        .ready_i    (ready_i),
        .valid_o    (valid_o),
        .ready_o    (ready_o),
        .a_en_o     (a_en),
        .b_en_o     (b_en),
        .b_sel_o    (b_sel),
        .buff_full_o(buff_full)
      );

      // --------
      // DATAPATH
      // --------

      // Register A
      always_ff @(posedge clk_i or negedge rst_ni) begin : reg_a
        if (!rst_ni) a_data_q <= '0;
        else if (a_en) a_data_q <= data_i;
      end

      // Register B
      always_ff @(posedge clk_i or negedge rst_ni) begin : reg_b
        if (!rst_ni) b_data_q <= '0;
        else if (b_en) b_data_q <= data_i;
      end

      // Output MUX
      assign data_o      = (b_sel) ? b_data_q : a_data_q;

      // Output data
      assign buff_full_o = buff_full;
      assign buff_data_o = (b_sel) ? a_data_q : b_data_q;
    end
  endgenerate
endmodule
