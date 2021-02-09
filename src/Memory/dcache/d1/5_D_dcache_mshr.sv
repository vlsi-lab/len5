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
// File: dcache_mshr.sv
// Author: Matteo Perotti
// Date: 27/10/2019
// Description: L1 D-Cache MSHR

`include "memory_pkg.sv"
import memory_pkg::*;

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/dcache/d1/0_D_one_hot_encoder.sv"

module dcache_mshr
(
  // Main control
  input  logic                         clk_i,
  input  logic                         rst_ni,
  // Control
  input  logic                         clr_all_i,            // clear the MSHR
  input  logic                         add_line_addr_i,      // add a new line address
  input  logic                         put_wait_read_line_i, // set the wait bit for the read line
  input  logic                         clr_hit_line_i,       // clear the line which hit
  // Input line address from d1
  input  line_addr_t                   line_addr_i,          // d1 input line address compared
  // Output line address for L2C req
  output line_addr_t                   mshr_l2c_line_addr_o, // next ready line
  // Output state
  output logic                         hit_o,                // d1 compared line hit
  output logic                         req_available_o,      // Request available
  output logic                         full_o,               // MSHR full
  output mshr_pending_req_t            pending_req_o         // How many Valid && Waiting entries
);

  localparam MSHR_ENTRIES      = L1C_MSHR_ENTRIES;
  localparam LOG2_MSHR_ENTRIES = $clog2(MSHR_ENTRIES);

  // Register file entries
  line_addr_t              line_addr [MSHR_ENTRIES];
  // Valid and Waiting state bits
  logic [MSHR_ENTRIES-1:0] valid_vec;
  logic [MSHR_ENTRIES-1:0] wait_vec;

  // Auxiliary internal signals
  logic [MSHR_ENTRIES-1:0] hit_vec;
  logic [MSHR_ENTRIES-1:0] valid_vec_n;
  logic [MSHR_ENTRIES-1:0] val_wait_vec;
  logic [MSHR_ENTRIES-1:0] val_wait_n_vec;

  // Three types of address
  logic [LOG2_MSHR_ENTRIES-1:0] addr_new_entry, addr_hit_entry, addr_next_req_entry;

  //---------------\\
  // REGISTER FILE \\
  //---------------\\

  // Each entry can be addressed only by one address among addr_new_entry, addr_hit_entry, addr_next_req_entry
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int k = 0; k < MSHR_ENTRIES; k++) begin
        line_addr[k]                <= '0;
        valid_vec[k]                <= '0;
        wait_vec[k]                 <= '0;
      end
    end else if (clr_all_i) begin
      valid_vec                     <= '0;
      wait_vec                      <= '0;
    end else if (add_line_addr_i) begin
      line_addr[addr_new_entry]     <= line_addr_i;
      valid_vec[addr_new_entry]     <= 1'b1;
      wait_vec[addr_new_entry]      <= 1'b0;
    end else if (put_wait_read_line_i) begin
      wait_vec[addr_next_req_entry] <= 1'b1;
    end else if (clr_hit_line_i) begin
      valid_vec[addr_hit_entry]     <= 1'b0;
      wait_vec[addr_hit_entry]      <= 1'b0;
    end
  end

  assign mshr_l2c_line_addr_o = line_addr[addr_next_req_entry];

  //------------------\\
  // COMPARISON BLOCK \\
  //------------------\\

  // Hit vector: incoming line address compared to the MSHR entries
  always_comb begin
    for (int k = 0; k < MSHR_ENTRIES; k++) begin
      hit_vec[k] = (valid_vec[k] && line_addr_i == line_addr[k]) ? 1'b1 : 1'b0;
    end
  end

  assign hit_o = |hit_vec;

  //-----------\\
  // ADDRESSES \\
  //-----------\\

  // An invalid entry is a free one
  assign valid_vec_n = ~valid_vec;
  one_hot_encoder #(
    .D(MSHR_ENTRIES),
    .E($clog2(MSHR_ENTRIES))
  ) l1dc_mshr_free_encoder (
    .mh_decoded_i(valid_vec_n),
    .oh_encoded_o(addr_new_entry)
  );

  // A valid entry which is not waiting can be the next L2 request
  assign val_wait_n_vec = valid_vec & ~wait_vec;
  one_hot_encoder #(
    .D(MSHR_ENTRIES),
    .E($clog2(MSHR_ENTRIES))
  ) l1dc_mshr_read_encoder (
    .mh_decoded_i(val_wait_n_vec),
    .oh_encoded_o(addr_next_req_entry)
  );

  // The hit vector determines the hit address
  one_hot_encoder #(
    .D(MSHR_ENTRIES),
    .E($clog2(MSHR_ENTRIES))
  ) l1dc_mshr_hit_encoder (
    .mh_decoded_i(hit_vec),
    .oh_encoded_o(addr_hit_entry)
  );

  //----------------------\\
  // OUTPUT STATE SIGNALS \\
  //----------------------\\

  // Is there any Valid && !Waiting entry?
  assign req_available_o = |val_wait_n_vec;

  // Is the MSHR full?
  assign full_o = &valid_vec;

  // Adder to count how many pending requests are present in the buffer
  assign val_wait_vec = valid_vec & wait_vec;
  always_comb begin
    pending_req_o = '0;
    for (int k = 0; k < MSHR_ENTRIES; k++) begin
      if (val_wait_vec[k]) pending_req_o += 1'b1;
    end
  end

endmodule
