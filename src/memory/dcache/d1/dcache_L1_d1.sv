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
// File: dcache_L1_d1.sv
// Author: Matteo Perotti
// Date: 26/10/2019
// Description: d1 part of the L1 D-Cache

import memory_pkg::*;

//`include "d1_dirty_vec_one_hotter.sv"
//`include "d1_d0_data_sel.sv"
//`include "d1_replacement_block.sv"
//`include "d1_comp_block.sv"
//`include "d1_stall_replay_cu.sv"
//`include "dcache_wb_victim_buffer.sv"
//`include "d1_wbb_tag_gen.sv"
//`include "dcache_mshr.sv"
//`include "d1_wbb_mshr_ctrl_L2_side.sv"
//`include "d1_L2_req_data_sel.sv"
//`include "d1_L2_req_arbiter.sv"
//`include "d1_ctrl.sv"

module dcache_L1_d1
(
  // Main
  input  logic          clk_i,
  input  logic          rst_ni,
  // Control
  input  logic          clr_i,              // Clear MSHR and other regs
  // d0 -> d1
  input  d0_d1_req_t    d0_d1_req_i,        // Request related information from d0 output register
  output logic          d1_d0_req_rdy_o,    // d1 stage ready?
  output logic          d1_d0_stalled_o,    // d1 is stalled (let pass L2 answers only)
  // d1 -> d0
  output d1_d0_req_t    d1_d0_req_o,        // d1 wants to use the cache itself (e.g. for a store)
//output logic          d0_d1_req_rdy_i,    // fixed '1' (d1 requests have the highest priority)
  // D-Cache -> LSQ
  output l1dc_lsq_ans_t l1dc_lsq_ans_o,     // D-Cache answer to LSQ
  // D-Cache -> L2-Cache
  output l1dc_l2c_req_t l1dc_l2c_req_o,     // D-Cache request to L2-Cache
  input  logic          l2c_l1dc_req_rdy_i,
  // D-Cache -> L2 update block
  output logic          l1dc_upd_cnt_en_o,  // Counter enable to address the next set
  output logic          wbb_empty_o         // the WBB is empty
);

  localparam N_WAY         = DCACHE_L1_ASSOCIATIVITY;
  localparam MEM_ADDR_LEN  = DCACHE_L1_IDX_A_LEN;
  localparam WORDS_IN_LINE = 2**DCACHE_L1_LINE_OFF_A_LEN;
  localparam CACHE_LINES   = 2**MEM_ADDR_LEN;         // Number of lines of each cache block
  localparam DATA_WORD_LEN = DCACHE_L1_LINE_LEN;      //

  // Incoming data from d0
  d1_req_info_t      d0_reg_out_q;
  d1_mem_out_t       mem_out;
  line_addr_t        d0_reg_out_line_addr;
  // The hit vector, used to select the correct doubleword
  hit_vec_t          hit_vec;
  // The requested line is in the cache
  logic              cache_hit;
  // The replace vector, used to choose the next line to be evicted when a replace occurs
  repl_vec_t         replace_vec;
  // The line designated by the replace vector is dirty
  logic              line_to_be_replaced_dirty;
  // One hotted version of the dirty vector. It is used to update L2 with the dirty lines of L1.
  dirty_vec_t        one_hot_dirty_vec;
  // The WBB is being written by the L2 updating process
  logic              l2_update_is_writing_wbb;
  // MSHR
  logic              mshr_clr;                       // clear all the mshr
  logic              mshr_hit;                       // mshr hit
  logic              mshr_full;                      // the mshr is full
  logic              mshr_add_data;                  // mshr control: add the line addr to a free entry
  logic              mshr_put_wait_read_line;        // put the read line in a waiting state
  logic              mshr_clr_hit_line;              // mshr control: clear the line which hit
  line_addr_t        mshr_l2c_line_addr;             // line address from mshr to l2c
  logic              mshr_req_available;             // request available from the mshr
  mshr_pending_req_t mshr_pending_req;               // how many pending requests in the mshr
  // WBB
  logic              wbb_line_addr_hit;              // line addr hit (for normal operations)
  logic              wbb_tag_hit;                    // tag hit (for WB acknowledge)
  logic              wbb_full;                       // WBB full
  logic              wbb_add_data;                   // wbb control: add new data to a free entry
  logic              wbb_clr_hit_line;               // wbb control: clear the entry which hit
  logic              wbb_switch_hit_line;            // wbb control: write the input data in the entry which hit
  logic              wbb_wup_hit_line;               // wbb control: wake-up the entry which hit
  logic              wbb_put_wait_tag_read_line;     // wbb control: assign a tag and put in a waiting state the read entry (L2 side)
  dcache_line_t      wbb_input_line;                 // wbb input line
  line_addr_t        wbb_input_line_addr;            // wbb input line address
  dcache_line_t      wbb_output_line;                // line from the entry which hit
  wbb_free_entries_t wbb_free_entries;               // how many free entries are present in the WBB
  logic              wbb_req_available;              // there is a valid wbb -> l2c request
  dcache_line_t      wbb_l2c_line;                   // wbb -> l2c line
  line_addr_t        wbb_l2c_line_addr;              // wbb -> l2c line addr
  // WBB TAG GEN
  wbb_tag_t          wbb_new_tag;                    // new tag for the wbb. It is written in the read entry during a valid L2C transaction
  // L2 interface
  logic              mshr_l2c_transaction_ok;        // successful mshr transaction with l2c
  logic              wbb_l2c_transaction_ok;         // successful wbb transaction with l2c
  mshr_wbb_winner_e  mshr_wbb_l2c_req_winner;        // priority given to the mshr or to the wbb for l2c req
  // The dirty vector has at least one '1'
  logic              at_least_one_dirty;
  // d1 flow control
  logic              d1_replaying;
  logic              d1_stalled;
  // Internal signals (d1_d0 request can be generated also by the replay registers!)
  d1_d0_req_type_e   d1_d0_req_type_from_ctrl;       // possible d1_d0 request from the d1 ctrl
  logic              d1_d0_req_type_from_ctrl_valid; // valid the request
  logic              wbb_d0_fwd;                     // a wbb -> cache forward is happening
  // CU
  logic              lets_stall;                     // next cycle -> stall
  logic              lets_replay;                    // next cycle -> replay
  logic              lets_wait_wbb;                  // next cycle -> wait the wbb
  logic              wbb_will_free;                  // next cycle -> unlock the cache which was in "wait wbb"
  // Replay registers
  l1dc_replay_t      replay_reg_d, replay_reg_q;     // data signals
  logic              replay_reg_en;                  // reg enable
  // Replacement block
  logic              update_replacement;
  // Output data selection
  logic [WORDS_IN_LINE-1:0] [DCACHE_L1_WORD_LEN-1:0] cache_hit_line;
  // Dirty line paddr during an L2 updating (to be sent back to d0 for line cleaning)
  line_addr_t        l2_update_dirty_line_addr;

  // Signal binding
  assign d0_reg_out_q = d0_d1_req_i.info;
  assign mem_out      = d0_d1_req_i.mem_out;

  //-----------------\\
  // DATA COMPARISON \\
  //-----------------\\

  d1_comp_block #(
    .N_WAY(N_WAY)
  ) i_d1_comp_block (
    .tag_i(d0_reg_out_q.paddr.tag),
    .tag_vec_i(mem_out.tag_vec),
    .valid_vec_i(mem_out.valid_vec),
    .dirty_vec_i(mem_out.dirty_vec),
    .replace_vec(replace_vec),
    .hit_vec_o(hit_vec),
    .hit_o(cache_hit),
    .dirty_o(line_to_be_replaced_dirty)
  );

  //----------------------\\
  // DIRTY BIT ONE HOTTER \\
  //----------------------\\

  d1_dirty_vec_one_hotter i_d1_dirty_vec_one_hotter (
    .l2_update_is_writing_wbb_i(l2_update_is_writing_wbb),
    .mh_dirty_vec_i(mem_out.dirty_vec),
    .oh_dirty_vec_o(one_hot_dirty_vec),
    .at_least_one_dirty_o(at_least_one_dirty),
    .l2_update_cnt_en_o(l1dc_upd_cnt_en_o)
  );

  //---------\\
  // CONTROL \\
  //---------\\

  d1_ctrl i_d1_ctrl (
    .clr_mshr_i(clr_i),
    .d1_req_type_i(d0_reg_out_q.req_type),
    .d1_req_valid_i(d0_reg_out_q.valid),
    .cache_hit_i(cache_hit),
    .mshr_hit_i(mshr_hit),
    .wbb_line_addr_hit_i(wbb_line_addr_hit),
    .wbb_tag_hit_i(wbb_tag_hit),
    .line_dirty_i(line_to_be_replaced_dirty),
    .at_least_one_dirty_i(at_least_one_dirty),
    .mshr_full_i(mshr_full),
    .wbb_full_i(wbb_full),
    .d1_stalled_i(d1_stalled),
    .replaying_i(d1_replaying),
    .d1_d0_req_type_o(d1_d0_req_type_from_ctrl),
    .d1_d0_req_valid_o(d1_d0_req_type_from_ctrl_valid),
    .mshr_add_data_o(mshr_add_data),
    .mshr_clr_hit_line_o(mshr_clr_hit_line),
    .mshr_clr_all_o(mshr_clr),
    .wbb_add_data_o(wbb_add_data),
    .wbb_clr_hit_line_o(wbb_clr_hit_line),
    .wbb_switch_hit_line_o(wbb_switch_hit_line),
    .wbb_wup_hit_line_o(wbb_wup_hit_line),
    .lets_stall_o(lets_stall),
    .lets_replay_o(lets_replay),
    .lets_wait_wbb_o(lets_wait_wbb),
    .wbb_will_free_o(wbb_will_free),
    .replay_reg_en_o(replay_reg_en),
    .d1_d0_req_type_repl_d_o(replay_reg_d.req_type),
    .d1_lsq_ans_valid_o(l1dc_lsq_ans_o.valid),
    .d1_lsq_ans_was_store_o(l1dc_lsq_ans_o.was_store),
    .l2_update_is_writing_wbb_o(l2_update_is_writing_wbb),
    .wbb_d0_fwd_o(wbb_d0_fwd),
    .d1_d0_req_rdy_o(d1_d0_req_rdy_o)
  );

  d1_stall_replay_cu i_d1_stall_replay_cu (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .lets_stall_i(lets_stall),
    .lets_replay_i(lets_replay),
    .lets_wait_wbb_i(lets_wait_wbb),
    .wbb_will_free_i(wbb_will_free),
    .replaying_o(d1_replaying),
    .d1_stalled_o(d1_stalled)
  );

  assign d1_d0_stalled_o = d1_stalled;

  //-------------------\\
  // d1 -> d0 DATA SEL \\
  //-------------------\\

  // This dirty line paddr is valid ONLY during an L2 updating when
  always_comb begin
    l2_update_dirty_line_addr = '0;
    // If an L2 updating is ongoing and a dirty line is found, send the address of the selected dirty line to d0
    if (d0_reg_out_q.req_type == d0_d1_UpdateL2) begin
      for (int k = 0; k < N_WAY; k++) begin
        if (one_hot_dirty_vec[k]) l2_update_dirty_line_addr = {mem_out.tag_vec[k], d0_reg_out_q.paddr.idx};
      end
    end
  end

  d1_d0_data_sel i_d1_d0_data_sel (
    .d1_req_type_i(d0_reg_out_q.req_type),
    .d1_d0_req_type_i(d1_d0_req_type_from_ctrl),
    .d1_d0_req_valid_i(d1_d0_req_type_from_ctrl_valid),
    .replaying_i(d1_replaying),
    .d0_reg_out_paddr_i(d0_reg_out_q.paddr),
    .d0_reg_out_data_i(d0_reg_out_q.data),
    .d0_reg_out_line_i(d0_reg_out_q.line),
    .d0_reg_out_lsq_addr_i(d0_reg_out_q.lsq_addr),
    .d0_reg_out_store_width_i(d0_reg_out_q.store_width),
    .dirty_line_addr_i(l2_update_dirty_line_addr),
    .hit_vec_i(hit_vec),
    .dirty_vec_i(one_hot_dirty_vec),
    .replace_vec_i(replace_vec),
    .wbb_d1_line_i(wbb_output_line),
    .replay_reg_type_i(replay_reg_q.req_type),
    .replay_reg_paddr_i(replay_reg_q.paddr),
    .replay_reg_doubleword_i(replay_reg_q.doubleword),
    .replay_reg_lsq_addr_i(replay_reg_q.lsq_addr),
    .replay_reg_store_width_i(replay_reg_q.store_width),
    .d1_d0_req_o(d1_d0_req_o)
  );

  //------\\
  // MHSR \\
  //------\\

  assign d0_reg_out_line_addr = {d0_reg_out_q.paddr.tag, d0_reg_out_q.paddr.idx};

  dcache_mshr i_l1dc_mshr (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_all_i(mshr_clr),
    .add_line_addr_i(mshr_add_data),
    .put_wait_read_line_i(mshr_put_wait_read_line),
    .clr_hit_line_i(mshr_clr_hit_line),
    .line_addr_i(d0_reg_out_line_addr),
    .mshr_l2c_line_addr_o(mshr_l2c_line_addr),
    .hit_o(mshr_hit),
    .req_available_o(mshr_req_available),
    .full_o(mshr_full),
    .pending_req_o(mshr_pending_req)
  );

  //---------------\\
  // VICTIM BUFFER \\
  //---------------\\

  // WBB data selection -> Input line to the WBB can be the one selected by the hit vector,
  //                       by the one hot dirty vector or by the replacement vector
  always_comb begin
    wbb_input_line = '0;
    // If L2 updating, send the selected dirty line to the WBB
    if (d0_reg_out_q.req_type == d0_d1_Store) begin
      for (int k = 0; k < N_WAY; k++) begin
        if (hit_vec[k]) wbb_input_line = mem_out.data_vec[k];
      end
    end else if (d0_reg_out_q.req_type == d0_d1_UpdateL2) begin
      for (int k = 0; k < N_WAY; k++) begin
        if (one_hot_dirty_vec[k]) wbb_input_line = mem_out.data_vec[k];
      end
    end else if (d0_reg_out_q.req_type == d0_d1_ReplaceReq) begin
      for (int k = 0; k < N_WAY; k++) begin
        if (replace_vec[k]) wbb_input_line = mem_out.data_vec[k];
      end
    end
  end

  // If L2 updating, send the selected dirty tag along with the set index
  assign wbb_input_line_addr = (d0_reg_out_q.req_type == d0_d1_UpdateL2) ? l2_update_dirty_line_addr : d0_reg_out_line_addr;

  // Write back buffer empty to signal that L2 Synchronization has ended
  assign wbb_empty_o = (wbb_free_entries == L1C_WBB_ENTRIES) ? 1'b1 : 1'b0;

  // Write Back victim Buffer
  dcache_wb_victim_buffer i_l1dc_wb_victim_buffer (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .add_line_addr_i(wbb_add_data),
    .put_wait_tag_read_line_i(wbb_put_wait_tag_read_line),
    .clr_hit_line_i(wbb_clr_hit_line),
    .switch_hit_line_i(wbb_switch_hit_line),
    .wup_hit_line_i(wbb_wup_hit_line),
    .new_tag_i(wbb_new_tag),
    .line_i(wbb_input_line),
    .line_addr_i(wbb_input_line_addr),
    .tag_to_be_compared_i(d0_reg_out_q.wbb_tag),
    .wbb_l2c_line_o(wbb_l2c_line),
    .wbb_l2c_line_addr_o(wbb_l2c_line_addr),
    .wbb_d1_line_o(wbb_output_line),
    .line_hit_o(wbb_line_addr_hit),
    .tag_hit_o(wbb_tag_hit),
    .req_available_o(wbb_req_available),
    .full_o(wbb_full),
    .free_entries_o(wbb_free_entries)
  );

  //-------------------\\
  // WBB TAG GENERATOR \\
  //-------------------\\

  d1_wbb_tag_gen i_d1_wbb_tag_gen (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .wbb_valid_transaction_i(wbb_l2c_transaction_ok),
    .wbb_tag_o(wbb_new_tag)
  );

  //--------------------------------------------------\\
  // MSHR / WBB -> L2 INTERFACE, DATA SEL AND CONTROL \\
  //--------------------------------------------------\\

  d1_L2_req_arbiter i_d1_L2_req_arbiter (
    .mshr_l2c_req_valid_i(mshr_req_available),
    .wbb_l2c_req_valid_i(wbb_req_available),
    .l2c_l1dc_req_rdy_i(l2c_l1dc_req_rdy_i),
    .mshr_pending_req_i(mshr_pending_req),
    .wbb_free_entries_i(wbb_free_entries),
    .wbb_d0_fwd_i(wbb_d0_fwd),
    .winner_o(mshr_wbb_l2c_req_winner),
    .mshr_l2c_transaction_ok_o(mshr_l2c_transaction_ok),
    .wbb_l2c_transaction_ok_o(wbb_l2c_transaction_ok),
    .d1_l2c_valid_o(l1dc_l2c_req_o.valid)
  );

  d1_L2_req_data_sel i_d1_L2_req_data_sel (
    .winner_i(mshr_wbb_l2c_req_winner),
    .wbb_l2c_line_i(wbb_l2c_line),
    .wbb_l2c_line_addr_i(wbb_l2c_line_addr),
    .wbb_tag_i(wbb_new_tag),
    .mshr_l2c_line_addr_i(mshr_l2c_line_addr),
    .l1dc_l2c_req_line_addr_o(l1dc_l2c_req_o.line_addr),
    .l1dc_l2c_req_line_o(l1dc_l2c_req_o.line),
    .l1dc_l2c_req_wbb_tag_o(l1dc_l2c_req_o.wbb_tag),
    .l1dc_l2c_req_is_store_o(l1dc_l2c_req_o.is_store)
  );

  d1_wbb_mshr_ctrl_L2_side i_d1_wbb_mshr_ctrl_L2_side (
    .mshr_transaction_ok_i(mshr_l2c_transaction_ok),
    .wbb_transaction_ok_i(wbb_l2c_transaction_ok),
    .mshr_put_wait_read_line_o(mshr_put_wait_read_line),
    .wbb_put_wait_tag_read_line_o(wbb_put_wait_tag_read_line)
  );

  //------------------\\
  // REPLAY REGISTERS \\
  //------------------\\

  assign replay_reg_d.paddr       = d1_d0_req_o.paddr;
  assign replay_reg_d.doubleword  = d1_d0_req_o.data;
  assign replay_reg_d.lsq_addr    = d1_d0_req_o.lsq_addr;
  assign replay_reg_d.store_width = d1_d0_req_o.store_width;

  // Keep req info to replay it
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      replay_reg_q <= '0;
    end else if (replay_reg_en) begin
      replay_reg_q <= replay_reg_d;
    end
  end

  //-------------------\\
  // REPLACEMENT_BLOCK \\
  //-------------------\\

  // FIFO replacement. Update only when a line write is performed using the replace_vec
  assign update_replacement = (d1_d0_req_o.valid && ((d1_d0_req_o.req_type == WriteCleanLine)    ||
                                                     (d1_d0_req_o.req_type == WriteDirtyLine)));

  d1_replacement_block #(
    .LOG2_N_SETS(DCACHE_L1_IDX_A_LEN)
  ) i_d0_replacement_block (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .update_i(update_replacement),
    .idx_addr_i(d1_d0_req_o.paddr.idx),  // Indexed with the effective write address for this cycle
    .replace_vec_o(replace_vec)
  );

  //------------------\\
  // OUTPUT SELECTION \\
  //------------------\\

  // Choose the line which hit in the set, then the requested doubleword
  always_comb begin
    cache_hit_line = '0;
    for (int k = 0; k < N_WAY; k++) begin
      if (hit_vec[k]) cache_hit_line = mem_out.data_vec[k];
    end
  end
  assign l1dc_lsq_ans_o.data     = cache_hit_line[d0_reg_out_q.paddr.line_off];
  assign l1dc_lsq_ans_o.lsq_addr = d0_reg_out_q.lsq_addr;

endmodule
