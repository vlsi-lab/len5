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
// File: ptw.sv
// Author: Matteo Perotti
// Date: 15/10/2019
// Description: Page Table Walker

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/memory_pkg.sv"
import memory_pkg::*;

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/ptw_tpc/1_J_mmuc_update_ctrl.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/ptw_tpc/1_J_pte_checker.sv"
`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/Memory/ptw_tpc/1_J_ptw_cu.sv"

module ptw
(
  input  logic               clk_i,
  input  logic               rst_ni,            // async reset
  input  logic               flush_i,           // flush ptw and mmuc
  // L2_tlb -> ptw
  input  l2tlb_ptw_req_t     tlb_ptw_req_i,     // 3*9 = 27 bits of virtual page numbers
  output logic               ptw_tlb_req_rdy_o, // ptw ready for TLB request
  // ptw -> L2_tlb
  output ptw_l2tlb_ans_t     ptw_tlb_ans_o,     // ppn, isSuperpage, exception, valid
  input  logic               tlb_ptw_ans_rdy_i, // tlb ready
  // ptw -> mmu_cache
  output ptw_mmuc_req_t      ptw_mmuc_req_o,    // first two VPNs
  output ptw_mmuc_write_t    ptw_mmuc_write_o,  // info for mmu_cache lines replacement
  output logic               mmuc_flush_o,      // flush the mmuc
  // mmu_cache -> ptw
  input  mmuc_ptw_ans_t      mmuc_ptw_ans_i,    // low_vpn, hit, full_hit, isSuperpage
  // ptw -> L2_cache
  output ptw_l2c_req_t       ptw_l2c_req_o,     // PPN to address a PTE
  input  logic               l2c_ptw_req_rdy_i, // L2 cache ready for ptw
  // L2_cache -> ptw
  input  l2c_ptw_ans_t       l2c_ptw_ans_i,     // PTE from L2 cache
  output logic               ptw_l2c_ans_rdy_o, // ptw ready for L2 cache
  // csr -> ptw
  input  logic [PPN_LEN-1:0] csr_root_ppn_i     // the root ppn
);

  //--------\\
  // SIGNAL \\
  //--------\\

  // Internal Control
  logic                                   mmuc_flush;
  logic                                   turn_on_reg_rx; // valid transaction with L2C or MMUC
  logic                                   l2c_ptw_hs_ok;  // valid handshake (L2C ans)
  pte_level_e                             pte_level;
  pte_ctrl_t                              pte_ctrl;

  // Internal Data
  logic [PT_LEVELS-2:0][VPN_PART_LEN-1:0] mmuc_tags;
  logic                                   mmuc_which_side;
  logic [VPN_PART_LEN-1:0]                chosen_vpn_part;
  logic [PAGE_OFFSET_LEN-1:0]             pp_offset;       // physical page offset
  pte_level_e                             cnt;             // In this description -> sequencer
  logic [PPN_LEN-1:0]                     first_ppn;
  pte_t                                   first_ppn_pte_aligned;

  // Register Control
  logic                                   reg_tx_en;
  logic                                   reg_rx_en;
  logic                                   reg_tlb_req_en;
  logic                                   reg_tlb_ans_en;
  logic                                   cnt_en;

  // Register Data
  vpn_t                                   vpn_q;
  logic [PADDR_LEN-1:0]                   pte_paddr_d;
  pte_t                                   pte_or_ppn_d, pte_or_ppn_q;
  logic [PPN_LEN-1:0]                     ppn_d;
  page_type_e                             page_type_d;
  exception_e                             exception_d;
  wrx_t                                   wrx_bits_d;
  logic                                   d_bit_d;
  logic                                   g_bit_d;
  logic                                   u_bit_d;
  pte_level_e                             cnt_load_value;

  // CU control
  logic                                   ptw_done;
  logic                                   ptw_tlb_req_rdy;
  logic                                   load_cnt;
  logic                                   mux_rx_sel_internal;
  logic                                   reg_tx_cond_en;
  logic                                   reg_ans_cond_en;
  logic                                   chk_en;
  logic                                   mmuc_update_cond_en;
  logic                                   ptw_l2c_ans_rdy;
  logic                                   reg_rx_cond_en;
  logic                                   cnt_cond_en;

  //------------\\
  // ASSIGNMENT \\
  //------------\\

  // Interface - Assigned only outputs used also as internal logic
  assign ptw_mmuc_req_o.mmuc_tags    = mmuc_tags;
  assign ptw_mmuc_write_o.which_side = mmuc_which_side; // used to drive VPN part MUX
  assign ptw_tlb_req_rdy_o           = ptw_tlb_req_rdy;
  assign ptw_l2c_ans_rdy_o           = ptw_l2c_ans_rdy;
  assign mmuc_flush                  = flush_i;
  assign ptw_mmuc_write_o.try_update = reg_tlb_ans_en;  // try to update mmuc shift reg
  assign mmuc_flush_o                = flush_i;

  // Internal
  assign mmuc_tags = vpn_q[2:1]; // two higher level parts of the VPN
  assign pte_level = cnt;        // PTE Level handled by the decrementer

  //----\\
  // CU \\
  //----\\

  ptw_cu ptw_cu_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .tlb_ptw_req_valid_i(tlb_ptw_req_i.valid),
    .tlb_ptw_ans_rdy_i(tlb_ptw_ans_rdy_i),
    .l2c_ptw_req_rdy_i(l2c_ptw_req_rdy_i),
    .l2c_ptw_ans_valid_i(l2c_ptw_ans_i.valid),
    .ptw_done_i(ptw_done),
    .ptw_tlb_req_rdy_o(ptw_tlb_req_rdy),
    .load_cnt_o(load_cnt),
    .ptw_mmuc_req_valid_o(ptw_mmuc_req_o.valid),
    .mux_rx_sel_internal_o(mux_rx_sel_internal),
    .reg_tx_cond_en_o(reg_tx_cond_en),
    .reg_ans_cond_en_o(reg_ans_cond_en),
    .chk_en_o(chk_en),
    .mmuc_update_cond_en_o(mmuc_update_cond_en),
    .ptw_l2c_req_valid_o(ptw_l2c_req_o.valid),
    .ptw_l2c_ans_rdy_o(ptw_l2c_ans_rdy),
    .reg_rx_cond_en_o(reg_rx_cond_en),
    .cnt_cond_en_o(cnt_cond_en),
    .ptw_tlb_ans_valid_o(ptw_tlb_ans_o.valid)
  );

  //----------\\
  // REGISTER \\
  //----------\\

  // Input register: VPN from L2-TLB
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      vpn_q <= '0;
    end else if (flush_i) begin
      vpn_q <= '0;
    end else if (reg_tlb_req_en) begin
      vpn_q <= tlb_ptw_req_i.vpn;
    end
  end

  // Output register: Physical PTE address to L2-Cache
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      ptw_l2c_req_o.pte_paddr <= '0;
    end else if (flush_i) begin
      ptw_l2c_req_o.pte_paddr <= '0;
    end else if (reg_tx_en) begin
      ptw_l2c_req_o.pte_paddr <= pte_paddr_d;
    end
  end

  // Input register: PTE from L2-Cache or PPN from MMUC
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      pte_or_ppn_q <= '0;
    end else if (flush_i) begin
      pte_or_ppn_q <= '0;
    end else if (reg_rx_en) begin
      pte_or_ppn_q <= pte_or_ppn_d;
    end
  end

  // Output register: answer to L2-TLB
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      ptw_tlb_ans_o.ppn       <= '0;
      ptw_tlb_ans_o.page_type <= KibiPage;
      ptw_tlb_ans_o.exception <= NoException;
      ptw_tlb_ans_o.wrx_bits  <= '0;
      ptw_tlb_ans_o.d_bit     <= 1'b0;
      ptw_tlb_ans_o.g_bit     <= 1'b0;
      ptw_tlb_ans_o.u_bit     <= 1'b0;
    end else if (flush_i) begin
      ptw_tlb_ans_o.ppn       <= '0;
      ptw_tlb_ans_o.page_type <= KibiPage;
      ptw_tlb_ans_o.exception <= NoException;
      ptw_tlb_ans_o.wrx_bits  <= '0;
      ptw_tlb_ans_o.d_bit     <= 1'b0;
      ptw_tlb_ans_o.g_bit     <= 1'b0;
      ptw_tlb_ans_o.u_bit     <= 1'b0;
    end else if (reg_tlb_ans_en) begin
      ptw_tlb_ans_o.ppn       <= ppn_d;
      ptw_tlb_ans_o.page_type <= page_type_d;
      ptw_tlb_ans_o.exception <= exception_d;
      ptw_tlb_ans_o.wrx_bits  <= wrx_bits_d;
      ptw_tlb_ans_o.d_bit     <= d_bit_d;
      ptw_tlb_ans_o.g_bit     <= g_bit_d;
      ptw_tlb_ans_o.u_bit     <= u_bit_d;
    end
  end

  //-----\\
  // MUX \\
  //-----\\

  // PPN offset selection
  always_comb begin
    chosen_vpn_part = '0;
    case (pte_level)
      Root: chosen_vpn_part = vpn_q[2];
      L3:   chosen_vpn_part = vpn_q[1];
      L2:   chosen_vpn_part = vpn_q[0];
    endcase
  end

  // VPN part selection for MMUC-single-tag update
  assign ptw_mmuc_write_o.mmuc_tag = (mmuc_which_side) ? mmuc_tags[1] : mmuc_tags[0];

  // First PPN selection: Root or MMUC
  assign first_ppn = (mmuc_ptw_ans_i.hit) ? mmuc_ptw_ans_i.ppn : csr_root_ppn_i;

  // Internal/external source for RX-MUXes
  assign pte_or_ppn_d   = (mux_rx_sel_internal) ? first_ppn_pte_aligned : l2c_ptw_ans_i.pte;
  assign turn_on_reg_rx = (mux_rx_sel_internal) ? 1'b1                  : l2c_ptw_hs_ok;

  // Page Table Level selection for CNT initial value
  always_comb begin
    cnt_load_value = L1;
    if (!mmuc_ptw_ans_i.hit) begin
      cnt_load_value = Root;
    end else if (mmuc_ptw_ans_i.hit && !mmuc_ptw_ans_i.is_full_hit) begin
      cnt_load_value = L3;
    end else if (mmuc_ptw_ans_i.hit && mmuc_ptw_ans_i.is_full_hit) begin
      cnt_load_value = L2;
    end
  end

  // (Page Table Level -> Page Type) conversion
  always_comb begin
    page_type_d = KibiPage;
    case (pte_level)
      L3: page_type_d = GibiPage;
      L2: page_type_d = MebiPage;
      L1: page_type_d = KibiPage;
    endcase
  end

  //------------------\\
  // SEQUENTIAL LOGIC \\
  //------------------\\

  // Decrementer for PTE Level tracking

  // !!!!!!!! CANNOT ASSIGN LOGIC TYPE TO ENUM AND VICE VERSA !!!!!!!!!!!!
  /*
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      cnt <= '0;
    end else if (load_cnt) begin
      cnt <= cnt_load_value;
    end else if (cnt_en) begin
      cnt <= cnt - 1;
    end
  end
  */
  // !!!!!!!! COUNTER DESCRIBED AS A SEQUENCER !!!!!!!!!!!!
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      cnt <= L1;
    end else if (flush_i) begin
      cnt <= L1;
    end else if (load_cnt) begin
      cnt <= cnt_load_value;
    end else if (cnt_en) begin
      case (cnt)
        Root:    cnt <= L3;
        L3:      cnt <= L2;
        L2:      cnt <= L1;
        L1:      cnt <= Root;
      endcase
    end
  end

  //---------------------\\
  // COMBINATORIAL LOGIC \\
  //---------------------\\

  // PTE physical address maker
  assign pp_offset   = {chosen_vpn_part, 3'b0};
  assign pte_paddr_d = {ppn_d, pp_offset};

  // First PPN alignemnt to PTE format
  assign first_ppn_pte_aligned = {10'b0, first_ppn, 10'b0};

  // PPN for MMUC-single-tag update
  assign ptw_mmuc_write_o.mmuc_data = pte_or_ppn_q.ppn;

  // PTE control bits for PTE checker
  assign pte_ctrl.a = pte_or_ppn_q.a;
  assign pte_ctrl.x = pte_or_ppn_q.x;
  assign pte_ctrl.w = pte_or_ppn_q.w;
  assign pte_ctrl.r = pte_or_ppn_q.r;
  assign pte_ctrl.v = pte_or_ppn_q.v;

  // Leaf PTE or exception checker
  pte_checker pte_checker_i (
    .pte_level_i(pte_level),
    .ppn_i(pte_or_ppn_q.ppn),
    .pte_ctrl_i(pte_ctrl),
    .chk_en_i(chk_en),
    .exception_o(exception_d),
    .done_o(ptw_done)
  );

  // MMUC update controller
  mmuc_update_ctrl mmuc_update_ctrl_i (
    .pte_level_i(pte_level),
    .mmuc_update_cond_en_i(mmuc_update_cond_en),
    .ptw_done_i(ptw_done),
    .wr_en_o(ptw_mmuc_write_o.wr_en),
    .which_side_o(mmuc_which_side),
    .wr_partial_o(ptw_mmuc_write_o.wr_partial),
    .partial_o(ptw_mmuc_write_o.partial)
  );

  // Register Enable creation
  assign reg_tlb_req_en = ptw_tlb_req_rdy && tlb_ptw_req_i.valid;
  assign reg_tlb_ans_en = reg_ans_cond_en && ptw_done;
  assign reg_rx_en      = reg_rx_cond_en  && turn_on_reg_rx;
  assign reg_tx_en      = reg_tx_cond_en  && ~ptw_done;

  // Auxiliary signal for effective L2C ans handshake
  assign l2c_ptw_hs_ok  = ptw_l2c_ans_rdy && l2c_ptw_ans_i.valid;

  // Decrementer Enable creation
  assign cnt_en         = l2c_ptw_hs_ok   && cnt_cond_en;

  // TLB ans assignment
  assign ppn_d          = pte_or_ppn_q.ppn;
  assign d_bit_d        = pte_or_ppn_q.d;
  assign g_bit_d        = pte_or_ppn_q.g;
  assign u_bit_d        = pte_or_ppn_q.u;
  assign wrx_bits_d.w   = pte_or_ppn_q.w;
  assign wrx_bits_d.r   = pte_or_ppn_q.r;
  assign wrx_bits_d.x   = pte_or_ppn_q.x;
  //     page_type_d                        // Assigned in the MUX section of this file

endmodule
