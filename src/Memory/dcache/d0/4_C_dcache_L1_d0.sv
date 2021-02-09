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
// File: dcache_L1_d0.sv
// Author: Matteo Perotti
// Date: 21/10/2019
// Description: d0 part of the L1 D-Cache

`include "memory_pkg.sv"
import memory_pkg::*;

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/dcache/d0/0_C_d0_scheduler.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/dcache/d0/1_C_d0_arbiter.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/dcache/d0/2_C_d0_req_encoder.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/dcache/d0/3_C_d0_cache_ctrl.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/dcache/d0/3_C_d0_data_sel_block.sv"
module dcache_L1_d0
(
  // Main
  input  logic          clk_i,
  input  logic          rst_ni,
  // Control
  input  logic          clr_i,              // Clear MSHR and other regs
  // Reset Block -> D-Cache
  input  rst_l1dc_req_t rst_l1dc_req_i,     // Initial reset request
  // L2-Update -> D-Cache
  input  upd_l1dc_req_t upd_l1dc_req_i,     // UpdateL2 block request
  // LSQ -> D-Cache
  input  lsq_l1dc_req_t lsq_l1dc_req_i,     // LSQ request to the D-Cache
  output logic          l1dc_lsq_req_rdy_o,
  // L2-Cache -> D-Cache
  input  l2c_l1dc_ans_t l2c_l1dc_ans_i,     // L2-Cache answer to D-Cache
  output logic          l1dc_l2c_ans_rdy_o,
  // D-Cache -> LSQ
  output l1dc_lsq_wup_t l1dc_lsq_wup_o,     // D-Cache wake-up signal to LSQ
  // d1 -> d0
  input  d1_d0_req_t    d1_d0_req_i,        // d1 wants to use the cache itself (e.g. for a store)
//output logic          d0_d1_req_rdy_o,    // fixed '1' (d1 requests have the highest priority)
  // d0 -> d1
  output d0_d1_req_t    d0_d1_req_o,        // Cache output and request related information
  input  logic          d1_d0_req_rdy_i,    // d1 stage ready?
  input  logic          d1_d0_stalled_i,    // d1 is stalled (let only L2 answers pass)
  // Memory Interface
  output dcache_addr_t                             dcache_addr_o,
  output tmem_ctrl_t [DCACHE_L1_ASSOCIATIVITY-1:0] tmem_ctrl_vec_o,
  output dmem_ctrl_t [DCACHE_L1_ASSOCIATIVITY-1:0] dmem_ctrl_vec_o,
  output tvd_mem_line_t                            dcache_wtvd_o,
  output dcache_line_t                             dcache_wdata_o,
  input  tvd_mem_line_t                            tvd_mem_out_vec_i [DCACHE_L1_ASSOCIATIVITY],
  input  dcache_line_t                             data_mem_out_vec_i [DCACHE_L1_ASSOCIATIVITY]
);

  localparam N_WAY         = DCACHE_L1_ASSOCIATIVITY;
  localparam MEM_ADDR_LEN  = DCACHE_L1_IDX_A_LEN;

  localparam BYTE_OFF_LEN  = DCACHE_L1_LINE_OFF_A_LEN + DCACHE_L1_WORD_A_LEN;
  localparam TVD_BE_LEN    = ((DCACHE_L1_TVD_LEN)+7)/8;
  localparam DATA_BE_LEN   = DCACHE_L1_LINE_SIZE;

  dcache_ctrl_t            cache_ctrl_vec;              // physical ssram control

  tmem_ctrl_t [N_WAY-1:0]  tmem_ctrl_vec;               // control vector for tag ram blocks
  dmem_ctrl_t [N_WAY-1:0]  dmem_ctrl_vec;               // control vector for data ram blocks

  d1_req_info_t            d0_d1_reg_d;                 // d0 -> d1 control and data (before output regs)
  d1_req_info_t            d0_d1_reg_q;                 // d0 -> d1 control and data (after output regs)

  dcache_addr_t            dcache_addr;                 // physical cache address
  dcache_line_t            dcache_wdata;                // cache line to be written
  tvd_mem_line_t           dcache_wtvd;                 // tag + valid + dirty bit to be written

  d1_mem_out_t             mem_out;

  logic                    reg_out_en;
  logic                    reg_out_clr;

  logic                    d0_enable;
  d0_winner_e              next_scheduled_block;

  tvd_mem_line_t           tvd_mem_out_vec  [N_WAY];
  dcache_line_t            data_mem_out_vec [N_WAY];

  d0_req_type_e            d0_req_type;
  d0_d1_req_type_e         d1_next_req_type;

  // Combinatorial control
  logic [BYTE_OFF_LEN-1:0] byte_addr_in_line;

  //-----------\\
  // SCHEDULER \\
  //-----------\\

  d0_scheduler i_d0_scheduler (
    .rst_val_i(rst_l1dc_req_i.valid),
    .d1_val_i(d1_d0_req_i.valid),
    .l2c_val_i(l2c_l1dc_ans_i.valid),
    .upd_val_i(upd_l1dc_req_i.valid),
    .lsq_val_i(lsq_l1dc_req_i.valid),
    .winner_o(next_scheduled_block)
  );

  //---------\\
  // ARBITER \\
  //---------\\

  d0_arbiter i_d0_arbiter (
    .winner_i(next_scheduled_block),
    .d1_rdy_i(d1_d0_req_rdy_i),
    .d1_stalled_i(d1_d0_stalled_i),
    .l2c_rdy_o(l1dc_l2c_ans_rdy_o),
    .lsq_rdy_o(l1dc_lsq_req_rdy_o),
    .d0_enable(d0_enable)
  );

  //-------------\\
  // REQ ENCODER \\
  //-------------\\

  d0_req_encoder i_d0_req_encoder (
    .winner_i(next_scheduled_block),
    .d1_req_type_i(d1_d0_req_i.req_type),
    .l2c_ans_type_i(l2c_l1dc_ans_i.ans_type),
    .lsq_req_type_i(lsq_l1dc_req_i.req_type),
    .d0_req_type_o(d0_req_type),
    .d1_next_req_type_o(d1_next_req_type)
  );

  //----------------\\
  // DATA SEL BLOCK \\
  //----------------\\

  d0_data_sel_block i_d0_data_sel_block (
    .d0_req_type_i(d0_req_type),
    .d1_req_type_i(d1_next_req_type),
    .lsq_l1dc_req_i(lsq_l1dc_req_i),
    .l2c_l1dc_ans_i(l2c_l1dc_ans_i),
    .d1_d0_req_i(d1_d0_req_i),
    .upd_l1dc_req_i(upd_l1dc_req_i),
    .rst_l1dc_req_i(rst_l1dc_req_i),
    .reg_out_d_o(d0_d1_reg_d),
    .dcache_addr_o(dcache_addr),
    .dcache_wdata_o(dcache_wdata),
    .dcache_wtvd_o(dcache_wtvd)
  );

  //------------------\\
  // CACHE CONTROLLER \\
  //------------------\\

  assign byte_addr_in_line = {d1_d0_req_i.paddr.line_off, d1_d0_req_i.paddr.word_off};

  d0_cache_ctrl #(
    .N_WAY(N_WAY),
    .BYTE_OFF_LEN(BYTE_OFF_LEN),
    .TVD_BE_LEN(TVD_BE_LEN),
    .DATA_BE_LEN(DATA_BE_LEN)
  ) i_d0_cache_ctrl (
    .d0_enable_i(d0_enable),
    .d0_req_type_i(d0_req_type),
    .store_width_i(d1_d0_req_i.store_width),
    .byte_addr_in_line_i(byte_addr_in_line),
    .hit_vec_i(d1_d0_req_i.hit_vec),
    .replace_vec_i(d1_d0_req_i.replace_vec),
    .d1_one_hot_dirty_vec_i(d1_d0_req_i.dirty_vec),
    .d1_stalled_i(d1_d0_stalled_i),
    .d0_cache_ctrl_o(cache_ctrl_vec)
  );

  //------------------\\
  // MEMORY INTERFACE \\
  //------------------\\

  assign dcache_addr_o    = dcache_addr;
  assign tmem_ctrl_vec_o  = tmem_ctrl_vec;
  assign dmem_ctrl_vec_o  = dmem_ctrl_vec;
  assign dcache_wtvd_o    = dcache_wtvd;
  assign dcache_wdata_o   = dcache_wdata;
  assign tvd_mem_out_vec  = tvd_mem_out_vec_i;
  assign data_mem_out_vec = data_mem_out_vec_i;

  assign tmem_ctrl_vec = cache_ctrl_vec.tvd_ctrl_vec;
  assign dmem_ctrl_vec = cache_ctrl_vec.data_ctrl_vec;

  // Memory output assignment
  always_comb begin
    for (int k = 0; k < N_WAY; k++) begin
      mem_out.data_vec[k]  = data_mem_out_vec[k];
      mem_out.tag_vec[k]   = tvd_mem_out_vec[k].tag;
      mem_out.valid_vec[k] = tvd_mem_out_vec[k].valid;
      mem_out.dirty_vec[k] = tvd_mem_out_vec[k].dirty;
    end
  end

  //------------------\\
  // OUTPUT REGISTERS \\
  //------------------\\

  // Update control
  always_comb begin
    reg_out_clr = 1'b0;
    reg_out_en  = 1'b0;
    // Update only if d0 is enabled and useful information should reach d1
    if (d0_enable && d1_next_req_type != Idle) begin
      reg_out_en = 1'b1;
    // Otherwise clear the regs if d1 is ready
    end else if (d1_d0_req_rdy_i) begin
      reg_out_clr = 1'b1;
    end
  end

  // Output registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      d0_d1_reg_q <= '0;
    end else if (clr_i) begin
      d0_d1_reg_q <= '0;
    end else if (reg_out_clr) begin
      d0_d1_reg_q <= '0;
    end else if (reg_out_en) begin
      d0_d1_reg_q <= d0_d1_reg_d;
    end
  end

  assign d0_d1_req_o.info    = d0_d1_reg_q;
  assign d0_d1_req_o.mem_out = mem_out;

  //--------------------\\
  // LSQ WAKE-UP SIGNAL \\
  //--------------------\\

  assign l1dc_lsq_wup_o.line_addr = l2c_l1dc_ans_i.line_addr;
  assign l1dc_lsq_wup_o.valid     = (d0_req_type == d0_ReadL2 || d0_req_type == d0_FwdL2StAddr) ? 1'b1 : 1'b0;

endmodule
