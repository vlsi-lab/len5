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
// File: l0_cache.sv
// Author: Michele Caon
// Date: 05/10/2022
/**
 * @brief "Level-zero cache"
 *
 * @details This module implements a small cache that records the store buffer
 *          entry containing the latest store instruction that wrote a certain
 *          memory location. When a load on the same address occurs (provided
 *          that the address is not masked), the store value is forwarded to
 *          the load without accessing the memory.
 */
module l0_cache #(
  /* Dependent parameters: do NOT override */
  localparam int unsigned StIdxW = $clog2(len5_config_pkg::STBUFF_DEPTH)
) (
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i, // flush after exception

  // Store buffer
  input logic st_valid_i,  // store instruction valid
  input logic [len5_pkg::ALEN-1:0] st_addr_i,  // store address
  input logic [StIdxW-1:0] st_idx_i,  // store buffer index
  input logic st_cached_i,  // the store instruction is cached
  input logic [len5_pkg::ALEN-1:0] st_cached_addr_i,  // cached store address
  input expipe_pkg::ldst_width_t st_cached_width_i,  // cached store width
  input logic [len5_pkg::XLEN-1:0] st_cached_value_i,  // cached store value
  output logic [StIdxW-1:0] st_idx_o,  // store buffer index

  // Load buffer
  input  logic                    [len5_pkg::ALEN-1:0] ld_addr_i,   // load address
  input  expipe_pkg::ldst_width_t                      ld_width_i,  // load width
  output logic                                         ld_valid_o,  // forwarding succeeded
  output logic                    [len5_pkg::XLEN-1:0] ld_value_o   // cached value
);

  import len5_config_pkg::*;
  import len5_pkg::*;

  // INTERNAL SIGNALS
  // ----------------
  // Cache data
  typedef struct packed {
    logic              valid;
    logic [StIdxW-1:0] st_idx;
  } l0_cache_t;
  l0_cache_t [STBUFF_DEPTH-1:0] data;

  // Address and tag
  logic      [      StIdxW-1:0] st_idx;
  logic      [      StIdxW-1:0] ld_idx;

  // Cache control
  logic                         addr_valid;
  logic                         cache_upd;
  logic                         st_hit;

  // --------------------
  // LEVEL-0 CACHE UPDATE
  // --------------------
  // Update the cache when a valid store is detected and the address is not
  // reserved.
  assign addr_valid = (st_addr_i & MMAP_MASK) == 64'h0;
  assign cache_upd  = st_valid_i & addr_valid;
  assign st_idx     = st_addr_i[StIdxW+3-1:3];  // doubleword-indexed
  always_ff @(posedge clk_i or negedge rst_ni) begin : blockName
    if (!rst_ni) foreach (data[i]) data[i] <= 'h0;
    else if (flush_i) begin
      foreach (data[i]) data[i].valid <= 1'b0;
    end else if (cache_upd) begin
      data[st_idx].valid  <= 1'b1;
      data[st_idx].st_idx <= st_idx_i;
    end
  end

  // Load address found in cache
  assign ld_idx     = ld_addr_i[StIdxW+3-1:3];

  // Cached instruction still valid in store buffer
  assign st_hit     = st_cached_i & st_cached_width_i == ld_width_i & st_cached_addr_i == ld_addr_i;

  // --------------
  // OUTPUT NETWORK
  // --------------
  // To store buffer
  assign st_idx_o   = data[ld_idx].st_idx;
  // Forwarding occurs when:
  // - the target address is found
  // - the target store instruction is still cached in the store buffer
  // - the pending load and the target store have the save width
  assign ld_valid_o = st_hit;
  assign ld_value_o = st_cached_value_i;
endmodule
