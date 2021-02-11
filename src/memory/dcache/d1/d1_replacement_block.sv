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
// File: d1_replacement_block.sv
// Author: Matteo Perotti
// Date: 22/10/2019
// Description: FIFO replacement policy for the cache, implemented with shift registers

`include "memory_pkg.sv"
import memory_pkg::*;

`include "decoder.sv"
`include "mux.sv"
`include "one_hot_shift_reg.sv"

module d1_replacement_block
#(
  LOG2_N_SETS = DCACHE_L1_IDX_A_LEN
)
(
  input  logic                   clk_i,
  input  logic                   rst_ni,
  input  logic                   update_i,
  input  logic [LOG2_N_SETS-1:0] idx_addr_i,
  output repl_vec_t              replace_vec_o
);

  localparam N_SETS = 2**LOG2_N_SETS;
  localparam N_WAY  = DCACHE_L1_ASSOCIATIVITY;

  logic [N_SETS-1:0] decoded_idx_addr;
  logic [N_WAY-1:0]  replace_mtx_q [N_SETS];

  //---------\\
  // DECODER \\
  //---------\\

  decoder #(
    .INPUT_LEN(LOG2_N_SETS)
  ) i_decoder (
    .en_i(update_i),
    .encoded_i(idx_addr_i),
    .decoded_o(decoded_idx_addr)
  );

  //-------------------------\\
  // ONE-HOT SHIFT REGISTERs \\
  //-------------------------\\

  for (genvar k = 0; k < N_SETS; k++) begin : shift_register_mtx
    one_hot_shift_reg #(
      .REG_LEN(N_WAY)
    ) i_shift_reg (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .update_i(decoded_idx_addr[k]),
      .output_o(replace_mtx_q[k])
    );
  end

  //-----\\
  // MUX \\
  //-----\\

  mux #(
    .PARALLELISM(N_WAY),
    .SEL_LEN(LOG2_N_SETS),
    .N_INPUT(N_SETS)
  ) i_mux (
    .sel(idx_addr_i),
    .input_i(replace_mtx_q),
    .output_o(replace_vec_o)
  );

endmodule
