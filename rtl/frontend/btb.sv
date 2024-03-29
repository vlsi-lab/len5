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
// File: btb.sv
// Author: Marco Andorno
// Date: 2/8/2019

module btb #(
  parameter int unsigned BTB_BITS = 4
) (
  input logic                      clk_i,
  input logic                      rst_ni,
  input logic                      flush_i,
  input logic [len5_pkg::XLEN-1:0] curr_pc_i,
  input logic                      valid_i,
  input logic                      del_entry_i,
  input       [len5_pkg::XLEN-1:0] res_pc_i,
  input       [len5_pkg::XLEN-1:0] res_target_i,

  output logic                                        hit_o,
  output logic [len5_pkg::XLEN-fetch_pkg::OFFSET-1:0] target_o
);

  import len5_pkg::*;
  import fetch_pkg::*;

  // Definitions
  localparam int unsigned BtbRows = 1 << BTB_BITS;

  typedef struct packed {
    logic                                      valid;
    logic [len5_pkg::XLEN-BTB_BITS-OFFSET-1:0] tag;
    logic [len5_pkg::XLEN-OFFSET-1:0]          target;
  } btb_entry_t;
  btb_entry_t btb_d[BtbRows], btb_q[BtbRows];

  logic [BTB_BITS-1:0] addr_r, addr_w;
  logic [len5_pkg::XLEN-BTB_BITS-OFFSET-1:0] tag_r, tag_w;

  // --------------------------
  // Branch Target Buffer (BTB)
  // --------------------------
  // Write
  assign addr_w = res_pc_i[BTB_BITS+OFFSET-1:OFFSET];
  assign tag_w  = res_pc_i[XLEN-1:BTB_BITS+OFFSET];

  always_comb begin : btb_update
    // By default, store previous value
    btb_d = btb_q;

    // If a valid branch resolution arrives, update BTB
    if (valid_i) begin
      if (del_entry_i) begin
        btb_d[addr_w] = '0;
      end else begin
        btb_d[addr_w].valid  = 1'b1;
        btb_d[addr_w].tag    = tag_w;
        btb_d[addr_w].target = res_target_i[XLEN-1:OFFSET];
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin : btb_async_rst
      for (int i = 0; i < BtbRows; i++) begin
        btb_q[i] <= '0;
      end
    end else if (flush_i) begin : btb_sync_flush
      for (int i = 0; i < BtbRows; i++) begin
        btb_q[i] <= '0;
      end
    end else btb_q <= btb_d;
  end

  // Read
  assign addr_r   = curr_pc_i[BTB_BITS+OFFSET-1:OFFSET];
  assign tag_r    = curr_pc_i[XLEN-1:BTB_BITS+OFFSET];

  assign hit_o    = btb_q[addr_r].valid & (btb_q[addr_r].tag == tag_r);
  assign target_o = btb_q[addr_r].target;

endmodule
