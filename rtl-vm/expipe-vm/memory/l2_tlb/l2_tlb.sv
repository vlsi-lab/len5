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
// File: l2_tlb.sv
// Author: Matteo Perotti
// Date: 04/11/2019
// Description: L2-TLB
// Details: hash-rehash for multiple page size support. L1 TLB always ready to accept answers


import memory_pkg::*;
import len5_pkg::*;
import csr_pkg::csr_priv_t;


module l2_tlb
(
  // Main
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             clr_mshr_i,
  input  logic             abort_i,
  // From CSR
  input  logic             sum_bit_i,      // For U bit access permissions check. Neglected for isntruction checks
  input  logic             mxr_bit_i,      // Executable pages can become Readable
  input  csr_priv_t        priv_mode_i,    // The actual privilege mode (NOT filtered by the MPRV BIT!!)
  input  csr_priv_t        priv_mode_ls_i, // The actual privilege mode (filtered by the MPRV BIT!!)
  input  asid_t            base_asid_i,    // Actual ASID from "satp" register
  // Flush control
  input  tlb_flush_e       flush_type_i,   // External flush request to the L2 TLB flush unit
  input  asid_t            flush_asid_i,
  input vpn_t             flush_page_i,
  // (L1 TLB Arbiter -> L2 TLB) request channel
  input l1tlb_l2tlb_req_t l1tlb_l2tlb_req_i,
  output logic             l2tlb_l1tlb_req_rdy_o,
  // (L2 TLB -> PTW) request channel
  output l2tlb_ptw_req_t   l2tlb_ptw_req_o,
  input  logic             ptw_l2tlb_req_rdy_i,
  // (PTW -> L2 TLB) answer channel
  input ptw_l2tlb_ans_t   ptw_l2tlb_ans_i,
  output logic             l2tlb_ptw_ans_rdy_o,
  // (L2 TLB -> L1 TLB Arbiter) answer channel
  output l2tlb_l1tlb_ans_t l2tlb_l1tlb_ans_o,
  // Memory Interface
  output l2tlb_tmem_ctrl_t          tag_mem_ctrl_o [L2_TLB_ASSOCIATIVITY],
  output logic [L2_TLB_IDX_LEN-1:0] tlb_addr_o,
  output l2tlb_dmem_ctrl_t          data_mem_ctrl_o [L2_TLB_ASSOCIATIVITY],
  output l2tlb_t_entry_t            tlb_input_entry_tag_o,
  output logic [PPN_LEN-1:0]        tlb_input_entry_data_o,
  input l2tlb_t_entry_t            tlb_output_entry_vec_tag_i  [L2_TLB_ASSOCIATIVITY],
  input logic [PPN_LEN-1:0]        tlb_output_entry_vec_data_i [L2_TLB_ASSOCIATIVITY]
);

  localparam N_SETS_TLB  = L2_TLB_ENTRIES / L2_TLB_ASSOCIATIVITY;
  localparam N_WAY       = L2_TLB_ASSOCIATIVITY;
  localparam N_MSHR      = L2_TLB_MSHR_ENTRIES;
  localparam IDX_LEN     = L2_TLB_IDX_LEN;

  // Control and data to/from the (t0 -> t1) registers
  logic               t0_t1_reg_en;
  t0_t1_req_t         t0_t1_req_d, t0_t1_req_q;
  // Memory control
  l2tlb_dmem_ctrl_t   data_mem_ctrl [N_WAY];
  l2tlb_tmem_ctrl_t   tag_mem_ctrl [N_WAY];
  // Memory data I/O
  logic [IDX_LEN-1:0] tlb_addr;
  l2tlb_entry_t       tlb_input_entry;
  l2tlb_entry_t       tlb_output_entry_vec [N_WAY];
  l2tlb_t_entry_t     tlb_input_entry_tag;
  logic [PPN_LEN-1:0] tlb_input_entry_data;
  l2tlb_t_entry_t     tlb_output_entry_vec_tag  [N_WAY];
  logic [PPN_LEN-1:0] tlb_output_entry_vec_data [N_WAY];
  // (Flush unit -> t0)
  logic [IDX_LEN-1:0] flush_idx;
  logic               flush_req_valid;
  tlb_flush_e         effective_flush_type; // Flush request produced by the Flush Unit for the L2 TLB
  // (t0 -> Flush unit)
  logic               flush_cnt_en;
  // (t0 -> Replacement unit)
  logic [IDX_LEN-1:0] replace_idx;
  // (Replacement block -> t0)
  logic [N_WAY-1:0]   replace_vec;
  // (t1 -> Replacement block)
  logic [N_WAY-1:0]   hit_vec;
  logic [N_WAY-1:0]   valid_vec;
  logic [N_WAY-1:0]   valid_vec_masked;     // The valid vector is masked everytime the TLB output is not valid
  logic               valid_tlb_access;
  logic               valid_tlb_read;
  logic               replacing_an_entry;
  // (t1 -> t0) request
  t1_t0_req_t         t1_t0_req;
  // (t0 -> MSHR)
  logic               rm_mshr_entry;
  logic               add_mshr_entry;
  // (t1 -> MSHR)
  logic               let_entry_waiting;
  vpn_t               t1_mshr_vpn;
  tlb_arb_tag_e       t1_mshr_destination;
  // (MSHR -> t0)
  vpn_t               mshr_t0_vpn;
  tlb_arb_tag_e       mshr_t0_destination;
  logic               mshr_full;
  // (MSHR -> PTW) control
  logic               mshr_req_available;


  //------------\\
  // FLUSH UNIT \\
  //------------\\

  l2_tlb_flush_unit #(
    .A(IDX_LEN)
  ) i_l2_tlb_flush_unit (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .flush_type_i(flush_type_i),
    .flush_idx_o(flush_idx),
    .flush_idx_cnt_en_i(flush_cnt_en),
    .flush_type_o(effective_flush_type),
    .flush_req_valid_o(flush_req_valid)
  );

  //-------------------\\
  // REPLACEMENT BLOCK \\
  //-------------------\\

  // Mask the valid_vec if no access is occurring
  assign valid_vec_masked = (valid_tlb_read) ? valid_vec : '0;

  L2_tlb_replacement_unit #(
    .N_WAY(N_WAY),
    .A(IDX_LEN),
    .N_SETS(N_SETS_TLB)
  ) i_L2_tlb_replacement_unit (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .index_i(replace_idx),
    .hit_vec_i(hit_vec),
    .valid_tlb_access_i(valid_tlb_access),
    .replacing_an_entry_i(replacing_an_entry),
    .valid_vec_i(valid_vec_masked),
    .replace_vec_o(replace_vec)
  );

  //----\\
  // t0 \\
  //----\\

  L2_tlb_t0 #(
    .A(IDX_LEN),
    .N_WAY(N_WAY)
  ) i_L2_tlb_t0 (
    .abort_i(abort_i),
    .base_asid_i(base_asid_i),
    .flush_type_i(effective_flush_type),
    .flush_idx_i(flush_idx),
    .flush_req_valid_i(flush_req_valid),
    .flush_idx_cnt_en_o(flush_cnt_en),
    .l1tlb_l2tlb_req_i(l1tlb_l2tlb_req_i),
    .l2tlb_l1tlb_req_rdy_o(l2tlb_l1tlb_req_rdy_o),
    .ptw_l2tlb_ans_i(ptw_l2tlb_ans_i),
    .l2tlb_ptw_ans_rdy_o(l2tlb_ptw_ans_rdy_o),
    .data_mem_ctrl_o(data_mem_ctrl),
    .tag_mem_ctrl_o(tag_mem_ctrl),
    .tlb_addr_o(tlb_addr),
    .tlb_input_entry_o(tlb_input_entry),
    .t0_t1_req_d_o(t0_t1_req_d),
    .t0_t1_reg_en_o(t0_t1_reg_en),
    .t1_t0_req_i(t1_t0_req),
    .mshr_vpn_i(mshr_t0_vpn),
    .mshr_destination_i(mshr_t0_destination),
    .mshr_full_i(mshr_full),
    .rm_mshr_entry_o(rm_mshr_entry),
    .replace_idx_o(replace_idx),
    .replace_vec_i(replace_vec)
  );

  //------------------\\
  // MEMORY INTERFACE \\
  //------------------\\

  // TAG - DATA separation
  // Memory input
  assign tlb_input_entry_tag.tag     = tlb_input_entry.tag;
  assign tlb_input_entry_tag.asid    = tlb_input_entry.asid;
  assign tlb_input_entry_tag.glob    = tlb_input_entry.glob;
  assign tlb_input_entry_tag.user    = tlb_input_entry.user;
  assign tlb_input_entry_tag.read    = tlb_input_entry.read;
  assign tlb_input_entry_tag.write   = tlb_input_entry.write;
  assign tlb_input_entry_tag.execute = tlb_input_entry.execute;
  assign tlb_input_entry_tag.dirty   = tlb_input_entry.dirty;
  assign tlb_input_entry_tag.mebi    = tlb_input_entry.mebi;
  assign tlb_input_entry_tag.gibi    = tlb_input_entry.gibi;
  assign tlb_input_entry_tag.valid   = tlb_input_entry.valid;
  assign tlb_input_entry_data        = tlb_input_entry.ppn;

  // Memory output
  for (genvar k = 0; k < N_WAY; k++) begin
    assign tlb_output_entry_vec[k].tag     = tlb_output_entry_vec_tag[k].tag;
    assign tlb_output_entry_vec[k].asid    = tlb_output_entry_vec_tag[k].asid;
    assign tlb_output_entry_vec[k].glob    = tlb_output_entry_vec_tag[k].glob;
    assign tlb_output_entry_vec[k].user    = tlb_output_entry_vec_tag[k].user;
    assign tlb_output_entry_vec[k].read    = tlb_output_entry_vec_tag[k].read;
    assign tlb_output_entry_vec[k].write   = tlb_output_entry_vec_tag[k].write;
    assign tlb_output_entry_vec[k].execute = tlb_output_entry_vec_tag[k].execute;
    assign tlb_output_entry_vec[k].dirty   = tlb_output_entry_vec_tag[k].dirty;
    assign tlb_output_entry_vec[k].mebi    = tlb_output_entry_vec_tag[k].mebi;
    assign tlb_output_entry_vec[k].gibi    = tlb_output_entry_vec_tag[k].gibi;
    assign tlb_output_entry_vec[k].valid   = tlb_output_entry_vec_tag[k].valid;
    assign tlb_output_entry_vec[k].ppn     = tlb_output_entry_vec_data[k];
  end

  // Memory interface connection
  assign tag_mem_ctrl_o            = tag_mem_ctrl;
  assign tlb_addr_o                = tlb_addr;
  assign data_mem_ctrl_o           = data_mem_ctrl;
  assign tlb_input_entry_tag_o     = tlb_input_entry_tag;
  assign tlb_input_entry_data_o    = tlb_input_entry_data;
  assign tlb_output_entry_vec_tag  = tlb_output_entry_vec_tag_i;
  assign tlb_output_entry_vec_data = tlb_output_entry_vec_data_i;

  //--------------------\\
  // t0 -> t1 REGISTERS \\
  //--------------------\\

  // If it's not sampling, t1 will be necessary Idle
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      t0_t1_req_q.vpn         <= '0;
      t0_t1_req_q.destination <= ITLB;
      t0_t1_req_q.ppn         <= '0;
      t0_t1_req_q.page_type   <= KibiPage;
      t0_t1_req_q.exception   <= NoException;
      t0_t1_req_q.wrx_bits    <= '0;
      t0_t1_req_q.d_bit       <= 1'b0;
      t0_t1_req_q.g_bit       <= 1'b0;
      t0_t1_req_q.u_bit       <= 1'b0;
      t0_t1_req_q.req_type    <= t0_t1_Idle;
    // Sample only if the next cycle t1 will be actively used
    end else if (t0_t1_reg_en) begin
      t0_t1_req_q             <= t0_t1_req_d;
    // Clear in the other cases
    end else begin
      t0_t1_req_q.vpn         <= '0;
      t0_t1_req_q.destination <= ITLB;
      t0_t1_req_q.ppn         <= '0;
      t0_t1_req_q.page_type   <= KibiPage;
      t0_t1_req_q.exception   <= NoException;
      t0_t1_req_q.wrx_bits    <= '0;
      t0_t1_req_q.d_bit       <= 1'b0;
      t0_t1_req_q.g_bit       <= 1'b0;
      t0_t1_req_q.u_bit       <= 1'b0;
      t0_t1_req_q.req_type    <= t0_t1_Idle;
    end
  end

  //----\\
  // t1 \\
  //----\\

  L2_tlb_t1 #(
    .A(IDX_LEN),
    .N_WAY(N_WAY)
  ) i_L2_tlb_t1 (
    .abort_i(abort_i),
    .sum_bit_i(sum_bit_i),
    .mxr_bit_i(mxr_bit_i),
    .priv_mode_i(priv_mode_i),
    .priv_mode_ls_i(priv_mode_ls_i),
    .base_asid_i(base_asid_i),
    .flush_asid_i(flush_asid_i),
    .flush_page_i(flush_page_i),
    .t1_mshr_vpn_o(t1_mshr_vpn),
    .mshr_destination_o(t1_mshr_destination),
    .add_mshr_entry_o(add_mshr_entry),
    .l2tlb_l1tlb_ans_o(l2tlb_l1tlb_ans_o),
    .t0_t1_req_q_i(t0_t1_req_q),
    .tlb_output_entry_vec_i(tlb_output_entry_vec),
    .t1_t0_req_o(t1_t0_req),
    .valid_vec_o(valid_vec),
    .hit_vec_o(hit_vec),
    .valid_tlb_read_o(valid_tlb_read),
    .valid_tlb_access_o(valid_tlb_access),
    .replacing_an_entry_o(replacing_an_entry)
  );

  //------\\
  // MSHR \\
  //------\\

  // PTW request unit
  assign l2tlb_ptw_req_o.valid = mshr_req_available;
  assign let_entry_waiting     = (ptw_l2tlb_req_rdy_i && mshr_req_available) ? 1'b1 : 1'b0;

  // MSHR
  L2_tlb_mshr #(
    .N(N_MSHR)
  ) i_L2_tlb_mshr (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clr_mshr_i(clr_mshr_i),
    .add_entry_i(add_mshr_entry),
    .rm_entry_i(rm_mshr_entry),
    .let_entry_waiting_i(let_entry_waiting),
    .req_available_o(mshr_req_available),
    .mshr_full_o(mshr_full),
    .vpn_i(t1_mshr_vpn),
    .destination_i(t1_mshr_destination),
    .ptw_ans_vpn_o(mshr_t0_vpn),
    .ptw_req_vpn_o(l2tlb_ptw_req_o.vpn),
    .destination_o(mshr_t0_destination)
  );

endmodule
