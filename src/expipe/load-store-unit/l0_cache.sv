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

`include "len5_config.svh"
import len5_pkg::*;
import expipe_pkg::ldst_width_t;

/**
 * @brief	"Level-zero cache"
 *
 * @details	This module implements a small cache that records the store buffer
 *          entry containing the latest store instruction that wrote a certain
 *          memory location. When a load on the same address occurs (provided 
 *          that the address is not masked), the store value is forwarded to 
 *          the load without accessing the memory.
 */
module l0_cache #(
    parameter   STBUFF_DEPTH,
    localparam  ST_IDX_W    = $clog2(STBUFF_DEPTH),
    localparam  TAG_W       = XLEN-ST_IDX_W
) (
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,        // flush after exception
    input   logic                   st_valid_i,     // store instruction valid
    input   logic [XLEN-1:0]        st_addr_i,      // store address
    input   logic [ST_IDX_W-1:0]    st_idx_i,       // store buffer index
    input   logic [TAG_W-1:0]       st_tag_i,       // cache store tag
    input   logic                   st_cached_i,    // the store instruction is cached
    input   ldst_width_t            st_width_i,     // cached store width
    input   logic [XLEN-1:0]        st_value_i,     // cached store value
    input   logic [XLEN-1:0]        ld_addr_i,      // load address
    input   ldst_width_t            ld_width_i,     // load width
    output  logic [ST_IDX_W-1:0]    st_idx_o,       // store buffer tag
    output  logic                   ld_valid_o,     // forwarding succeeded
    output  logic [XLEN-1:0]        ld_value_o      // cached value
);
    // INTERNAL SIGNALS 
    // ----------------
    // Cache data
    typedef struct packed {
        logic                   valid;
        logic [TAG_W-1:0]       tag;
        logic [ST_IDX_W-1:0]    st_idx;
    } l0_cache_t;
    l0_cache_t  data[0:STBUFF_DEPTH-1];

    // Address and tag
    logic [ST_IDX_W-1:0]    st_idx;
    logic [TAG_W-1:0]       st_tag;
    logic [ST_IDX_W-1:0]    ld_idx;
    logic [TAG_W-1:0]       ld_tag;

    // Cache control
    logic   addr_valid;
    logic   cache_upd;
    logic   cache_hit;
    logic   st_hit;

    // --------------------
    // LEVEL-0 CACHE UPDATE
    // --------------------
    // Update the cache when a valid store is detected and the address is not
    // reserved.
    assign  addr_valid  = (st_addr_i & `ST2LD_FWD_MASK) != 64'h0;
    assign  cache_upd   = st_valid_i & addr_valid;
    assign  st_idx      = st_addr_i[ST_IDX_W-1:0];
    assign  st_tag      = st_addr_i[XLEN-1-:TAG_W];
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : blockName
        if (!rst_n_i)   foreach (data[i]) data[i] <= 'h0;
        else if (flush_i) begin
            foreach (data[i]) data[i].valid <= 1'b0;
        end
        else if (cache_upd) begin
            data[st_idx].valid   <= 1'b1;
            data[st_idx].tag     <= st_tag;
            data[st_idx].st_idx  <= st_idx_i;
        end
    end

    // Load address found in cache
    assign  ld_idx      = ld_addr_i[ST_IDX_W-1:0];
    assign  ld_tag      = ld_addr_i[XLEN-1-:TAG_W];
    assign  cache_hit   = data[ld_idx].valid & data[ld_idx].tag == ld_tag;

    // Cached instruction still valid in store buffer
    assign  st_hit      = st_cached_i & st_width_i == ld_width_i & st_tag_i == ld_tag;

    // --------------
    // OUTPUT NETWORK
    // --------------
    // To store buffer
    assign  st_idx_o    = data[ld_idx].st_idx;
    // Forwarding occurs when:
    // - the target address is found
    // - the target store instruction is still cached in the store buffer
    // - the pending load and the target store have the save width
    assign  ld_valid_o  = cache_hit & st_hit;
    assign  ld_value_o  = st_value_i;
endmodule