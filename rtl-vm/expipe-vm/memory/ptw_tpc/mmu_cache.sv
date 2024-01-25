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
// File: mmu_cache.sv
// Author: Matteo Perotti
// Date: 14/10/2019
// Description: Translation Path Cache
// Reference: Translation Caching: Skip, Don’t Walk (the Page Table) - Thomas W. Barr, Alan L. Cox, Scott Rixner

import memory_pkg::*;


module mmu_cache
(
  input logic            clk_i,
  input logic            rst_ni,           // async reset
  // ptw -> mmu_cache
  input ptw_mmuc_req_t   ptw_mmuc_req_i,   // first two VPNs
  input ptw_mmuc_write_t ptw_mmuc_write_i, // info for mmu_cache lines replacement
  input logic            mmuc_flush_i,     // flush the mmuc
  // mmu_cache -> ptw
  output mmuc_ptw_ans_t  mmuc_ptw_ans_o    // PPN, hit, full_hit, is_superpage
);

  localparam MMUC_HALF_TAG_LEN = MMUC_TAG_LEN / 2;
  localparam LOG2_MMUC_ENTRIES = $clog2(MMUC_ENTRIES);

  //---------\\
  // SIGNALS \\
  //---------\\

  // interface
  logic                    req_valid;
  logic [VPN_PART_LEN-1:0] wtag;      // 9 bits tag to be written (VPN part)
  logic [PPN_LEN-1:0]      wdata;     // 44 bits data to be written (PPN)
  logic                    wpartial;  // if '1', only the first tag is valid (incomplete trace)
  logic                    wr_part_en;
  logic                    which_side; // write either the first tag/data couple or the second one
  logic                    wr_en;     // request a write
  logic                    try_update; // try to update the shift register for replacement. *

  // internal
  logic [MMUC_ENTRIES-1:0]                        dec_waddr;                    // one-hot decoded address for write control
  logic [MMUC_ENTRIES-1:0][1:0][VPN_PART_LEN-1:0] tag_vec;                      // all the tags
  logic [MMUC_ENTRIES-1:0][1:0][PPN_LEN-1:0]      data_vec;                     // all the data
  logic [MMUC_ENTRIES-1:0]                        partial_vec;                  // all the partial bits
  logic [MMUC_ENTRIES-1:0]                        valid_vec;                    // all the valid bits
  logic [1:0][VPN_PART_LEN-1:0]                   comp_tag;                     // 9 bits VPN + 9 bits VPN = 18 bits
  logic [1:0][PPN_LEN-1:0]                        selected_ppns;                // the pnn trace which hit
  logic [LOG2_MMUC_ENTRIES-1:0]                   selected_ppns_idx;            // index the hit ppn
  logic                                           hit_d, hit_q;                 // global hit signal
  logic                                           full_hit;                     // full or partial hit of the VPN trace
  logic [MMUC_ENTRIES-1:0]                        hit_vec_d, hit_vec_q;         // vector of the hit lines
  logic [MMUC_ENTRIES-1:0]                        replace_vec_d, replace_vec_q; // replacement vector (shift register)
  logic                                           update_replace_vec;           // upadte the FIFO shift register

  assign req_valid  = ptw_mmuc_req_i.valid;
  assign comp_tag   = ptw_mmuc_req_i.mmuc_tags;
  assign wtag       = ptw_mmuc_write_i.mmuc_tag;
  assign wdata      = ptw_mmuc_write_i.mmuc_data;
  assign wpartial   = ptw_mmuc_write_i.partial;
  assign wr_part_en = ptw_mmuc_write_i.wr_partial;
  assign which_side = ptw_mmuc_write_i.which_side;
  assign wr_en      = ptw_mmuc_write_i.wr_en;
  assign try_update = ptw_mmuc_write_i.try_update;

  //-----\\
  // TPC \\
  //-----\\

  tpc_regfile #(
    .ADDR_LEN(MMUC_ENTRIES)
  ) tpc (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .wr_en_i(wr_en),
    .wr_part_en_i(wr_part_en),
    .tag_i(wtag),
    .data_i(wdata),
    .partial_i(wpartial),
    .flush_i(mmuc_flush_i),
    .decoded_waddr_i(dec_waddr),
    .which_side_i(which_side),
    .tag_vec_o(tag_vec),
    .data_vec_o(data_vec),
    .partial_vec_o(partial_vec),
    .valid_vec_o(valid_vec)
  );

  tpc_comp_block #(
    .REG_ENTRIES(MMUC_ENTRIES),
    .HALF_TAG_LEN(MMUC_HALF_TAG_LEN)
  ) comb_block (
    .tag_i(comp_tag),
    .tag_vec_i(tag_vec),
    .partial_vec_i(partial_vec),
    .valid_vec_i(valid_vec),
    .hit_o(hit_d),
    .full_hit_o(full_hit),
    .hit_vec_o(hit_vec_d)
  );

  // Store the hit vector to know the entry to possibly update
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      hit_vec_q <= '0;
    end else if (req_valid) begin
      hit_vec_q <= hit_vec_d;
    end
  end

  // Flip Flop to store if a hit occurred, to select the cache write address **
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      hit_q <= '0;
    end else if (req_valid) begin
      hit_q <= hit_d;
    end
  end

  // Shift Register for FIFO tag/data replacement
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      replace_vec_q[MMUC_ENTRIES-1:1] <=   '0;
      replace_vec_q[0]                <= 1'b1;
    end else if (update_replace_vec) begin
      replace_vec_q                   <= replace_vec_d;
    end
  end

  always_comb begin
    replace_vec_d[MMUC_ENTRIES-1] = replace_vec_q[0];
    for (int k = 1; k < MMUC_ENTRIES; k++) begin
      replace_vec_d[k-1] = replace_vec_q[k];
    end
  end

  // Shift register update for FIFO replace
  assign update_replace_vec = ~hit_q & try_update;

  // Address mux for the TPC (FIFO replace or hit line update)
  assign dec_waddr = (hit_q) ? hit_vec_q : replace_vec_q;

  // Trace selection - TO BE PARAMETRIZED
  always_comb begin
    selected_ppns_idx = '0;
    for (int k = MMUC_ENTRIES-1; k >= 0; k--) begin
      if (hit_vec_d[k]) selected_ppns_idx = k;
    end
  end
  assign selected_ppns = data_vec[selected_ppns_idx];

  // Ouput assignment
  assign mmuc_ptw_ans_o.ppn         = (full_hit) ? selected_ppns[0] : selected_ppns[1];
  assign mmuc_ptw_ans_o.hit         = hit_d;
  assign mmuc_ptw_ans_o.is_full_hit = full_hit;

endmodule

// * "try_update" should be asserted only for one cycle, otherwise the shift register can receive more than one enable per miss (hit_q is NOT cleared)
// ** For full hit the page is a kibipage, and no update is requested. For a partial hit, the page can be a Mebipage or a Kibipage. In the first case,
