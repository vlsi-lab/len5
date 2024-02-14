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
// File: mux.sv
// Author: Matteo Perotti
// Date: 22/10/2019
// Description: multiplexer
// Details: unpacked dimension: different input items. Packed dimension: parallelism

import memory_pkg::*;

module mux #(
               PARALLELISM = DCACHE_L1_IDX_A_LEN,
               SEL_LEN     = DCACHE_L1_ASSOCIATIVITY,
    localparam N_INPUT     = 1 << SEL_LEN
) (
    input  logic [    SEL_LEN-1:0] sel,
    input  logic [PARALLELISM-1:0] input_i [N_INPUT],
    output logic [PARALLELISM-1:0] output_o
);

  logic [N_INPUT-1:0] internal_mux_mtx[PARALLELISM];

  // AND masking
  for (genvar k = 0; k < PARALLELISM; k++) begin : mux_structure_and_rows
    for (genvar j = 0; j < N_INPUT; j++) begin : mux_structure_and_cols
      assign internal_mux_mtx[k][j] = (sel == j) ? input_i[j][k] : '0;
    end
  end

  // OR reduction
  for (genvar k = 0; k < PARALLELISM; k++) begin : mux_structure_or
    assign output_o[k] = |internal_mux_mtx[k];
  end

endmodule
