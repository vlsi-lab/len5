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
// File: prio_2way_arbiter.sv
// Author: Michele Caon
// Date: 29/10/2019

module prio_2way_arbiter #(
    parameter type DATA_T
) (
    // Handshaking
    input  logic high_prio_valid_i,  // from upstream hardware
    input  logic low_prio_valid_i,   // from upstream hardware
    input  logic ready_i,            // from downstream hardware
    output logic valid_o,            // to downstream hardware
    output logic high_prio_ready_o,  // to upstream hardware
    output logic low_prio_ready_o,   // to upstream hardware

    // Data
    input  DATA_T high_prio_data_i,
    input  DATA_T low_prio_data_i,
    output DATA_T data_o
);
  // INTERNAL SIGNALS
  // ----------------
  logic sel_high_prio;

  // Valid generation
  // ----------------
  assign valid_o = high_prio_valid_i | low_prio_valid_i;

  // Ready generation
  // ----------------
  always_comb begin : ready_gen
    // Default (downstram not ready)
    high_prio_ready_o = 1'b0;
    low_prio_ready_o  = 1'b0;
    sel_high_prio     = 1'b1;

    // Downstream ready
    if (ready_i) begin
      if (high_prio_valid_i) begin
        high_prio_ready_o = 1'b1;
        low_prio_ready_o  = 1'b0;
        sel_high_prio     = 1'b1;
      end else if (low_prio_valid_i) begin
        high_prio_ready_o = 1'b0;
        low_prio_ready_o  = 1'b1;
        sel_high_prio     = 1'b0;
      end else begin
        high_prio_ready_o = 1'b1;
        low_prio_ready_o  = 1'b1;
        sel_high_prio     = 1'b1;
      end
    end
  end

  // Output multiplexer
  // ------------------
  assign data_o = (sel_high_prio) ? high_prio_data_i : low_prio_data_i;

endmodule
