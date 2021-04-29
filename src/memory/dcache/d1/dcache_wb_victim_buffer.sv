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
// File: dcache_wb_victim_buffer.sv
// Author: Matteo Perotti
// Date: 27/10/2019
// Description: L1 D-Cache Write Back Victim Buffer

import memory_pkg::*;

`include "one_hot_encoder.sv"

module dcache_wb_victim_buffer
(
  // Main control
  input  logic              clk_i,
  input  logic              rst_ni,
  // Control
  input  logic              add_line_addr_i,          // add a new line address
  input  logic              put_wait_tag_read_line_i, // set the wait bit for the read line
  input  logic              clr_hit_line_i,           // clear the line which hit
  input  logic              switch_hit_line_i,        // when a line switch is requested
  input  logic              wup_hit_line_i,           // wake-up the hit line
  // Input tag from L2 arbiter
  input  wbb_tag_t          new_tag_i,                // input tag from the L2 counter
  // Input data from d1
  input  dcache_line_t      line_i,                   // d1 input line
  input  line_addr_t        line_addr_i,              // d1 input line address (also compared)
  input  wbb_tag_t          tag_to_be_compared_i,     // d1 input tag to be compared
  // Output line address for L2C req
  output dcache_line_t      wbb_l2c_line_o,           // next ready line
  output line_addr_t        wbb_l2c_line_addr_o,      // next ready line addr
  // Output line which hit
  output dcache_line_t      wbb_d1_line_o,            // line linked to the addr which hit
  // Output state
  output logic              line_hit_o,               // d1 compared line hit
  output logic              tag_hit_o,                // d1 compared tag hit
  output logic              req_available_o,          // Request available
  output logic              full_o,                   // wbb full - for L2 Update*
  // To L2 interface
  output wbb_free_entries_t free_entries_o            // How many free entries
);

  localparam WBB_ENTRIES      = L1C_WBB_ENTRIES;
  localparam LOG2_WBB_ENTRIES = $clog2(WBB_ENTRIES);

  // Register file entries
  dcache_line_t line      [WBB_ENTRIES];
  line_addr_t   line_addr [WBB_ENTRIES];
  wbb_tag_t     tag       [WBB_ENTRIES];
  // Valid and Waiting state bits
  logic [WBB_ENTRIES-1:0] valid_vec;
  logic [WBB_ENTRIES-1:0] wait_vec;

  // Auxiliary internal signals
  logic [WBB_ENTRIES-1:0] line_hit_vec;
  logic [WBB_ENTRIES-1:0] tag_hit_vec;
  logic [WBB_ENTRIES-1:0] hit_vec;
  logic [WBB_ENTRIES-1:0] valid_vec_n;
  logic [WBB_ENTRIES-1:0] val_wait_n_vec;

  // Three types of address
  logic [LOG2_WBB_ENTRIES-1:0] addr_new_entry, addr_hit_entry, addr_next_req_entry;

  //---------------\\
  // REGISTER FILE \\
  //---------------\\

  // Each entry can be addressed only by one address among addr_new_entry, addr_hit_entry, addr_next_req_entry
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int k = 0; k < WBB_ENTRIES; k++) begin
        line[k]                       <= '0;
        line_addr[k]                  <= '0;
        tag[k]                        <= '0;
        valid_vec[k]                  <= '0;
        wait_vec[k]                   <= '0;
      end
    end else if (add_line_addr_i) begin
      line[addr_new_entry]          <= line_i;
      line_addr[addr_new_entry]     <= line_addr_i;
      valid_vec[addr_new_entry]     <= 1'b1;
      wait_vec[addr_new_entry]      <= 1'b0;
    end else if (put_wait_tag_read_line_i) begin
      tag[addr_next_req_entry]      <= new_tag_i;   // tag assigned when a request is done
      wait_vec[addr_next_req_entry] <= 1'b1;
    end else if (clr_hit_line_i) begin
      valid_vec[addr_hit_entry]     <= 1'b0;
      wait_vec[addr_hit_entry]      <= 1'b0;
    end else if (switch_hit_line_i) begin
      line[addr_hit_entry]          <= line_i;
      line_addr[addr_hit_entry]     <= line_addr_i;
      valid_vec[addr_hit_entry]     <= 1'b1;
      wait_vec[addr_hit_entry]      <= 1'b0;
    end else if (wup_hit_line_i) begin
      valid_vec[addr_hit_entry]     <= 1'b1;
      wait_vec[addr_hit_entry]      <= 1'b0;
    end
  end

  assign wbb_l2c_line_o      = line[addr_next_req_entry];
  assign wbb_l2c_line_addr_o = line_addr[addr_next_req_entry];
  assign wbb_d1_line_o       = line[addr_hit_entry];

  //------------------\\
  // COMPARISON BLOCK \\
  //------------------\\

  // Hit vector: incoming line address compared to the WBB entries
  always_comb begin
    for (int k = 0; k < WBB_ENTRIES; k++) begin
      line_hit_vec[k] = (line_addr_i == line_addr[k]) ? valid_vec[k] : 1'b0;
    end
  end

  // Tag hit vector: hit only if tag hit and that line is waiting (otherwise, the tag was old and is not valid!)
  always_comb begin
    for (int k = 0; k < WBB_ENTRIES; k++) begin
      tag_hit_vec[k] = (tag_to_be_compared_i == tag[k]) ? wait_vec[k] : 1'b0; // (If wait = 1'b1, also valid = 1'b1)
    end
  end

  assign line_hit_o = |line_hit_vec;
  assign tag_hit_o  = |tag_hit_vec;

  // General hit vector
  assign hit_vec    = line_hit_o | tag_hit_o;

  //-----------\\
  // ADDRESSES \\
  //-----------\\

  // An invalid entry is a free one
  assign valid_vec_n = ~valid_vec;
  one_hot_encoder #(
    .D(WBB_ENTRIES),
    .E($clog2(WBB_ENTRIES))
  ) l1dc_wbb_free_encoder (
    .mh_decoded_i(valid_vec_n),
    .oh_encoded_o(addr_new_entry)
  );

  // A valid entry which is not waiting can be the next L2 request
  assign val_wait_n_vec = valid_vec & ~wait_vec;
  one_hot_encoder #(
    .D(WBB_ENTRIES),
    .E($clog2(WBB_ENTRIES))
  ) l1dc_wbb_read_encoder (
    .mh_decoded_i(val_wait_n_vec),
    .oh_encoded_o(addr_next_req_entry)
  );

  // The hit vector determines the hit address
  one_hot_encoder #(
    .D(WBB_ENTRIES),
    .E($clog2(WBB_ENTRIES))
  ) l1dc_wbb_hit_encoder (
    .mh_decoded_i(hit_vec),
    .oh_encoded_o(addr_hit_entry)
  );

  //----------------------\\
  // OUTPUT STATE SIGNALS \\
  //----------------------\\

  // Is there any Valid && !Waiting entry?
  assign req_available_o = |val_wait_n_vec;

  // Is the WBB full?
  assign full_o = &valid_vec;

  // Adder to count how many free entries are present in the buffer
  always_comb begin
    free_entries_o = '0;
    for (int k = 0; k < WBB_ENTRIES; k++) begin
      if (!valid_vec_n[k]) free_entries_o += 1'b1;
    end
  end

endmodule

// * it's not important to know if the buffer is full when L2 returns, because the L2 request
//   policy avoids possible issues. If the buffer has not enough free entries, MSHR requests are
//   blocked. The buffer can
