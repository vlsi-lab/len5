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
// File: ptw_cu.sv
// Author: Matteo Perotti
// Date: 15/10/2019
// Description: Page Table Walker Moore CU

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/memory_pkg.sv"
import memory_pkg::*;

module ptw_cu
(
  // Main
  input  logic clk_i,
  input  logic rst_ni,
  // Control
  input  logic tlb_ptw_req_valid_i,
  input  logic tlb_ptw_ans_rdy_i,
  input  logic l2c_ptw_req_rdy_i,
  input  logic l2c_ptw_ans_valid_i,
  input  logic ptw_done_i,
  output logic ptw_tlb_req_rdy_o,
  output logic load_cnt_o,            // load a value into the cnt-decrementer
  output logic ptw_mmuc_req_valid_o,
  output logic mux_rx_sel_internal_o, // set the source for the rx-register (L2-Cache side)
  output logic reg_tx_cond_en_o,
  output logic reg_ans_cond_en_o,
  output logic chk_en_o,
  output logic mmuc_update_cond_en_o,
  output logic ptw_l2c_req_valid_o,
  output logic ptw_l2c_ans_rdy_o,
  output logic reg_rx_cond_en_o,
  output logic cnt_cond_en_o,
  output logic ptw_tlb_ans_valid_o
);

  // PTW states
  typedef enum logic [2:0] {
    StIdle, StMmucReq, StInitialPaddr, StL2Req, StWaitL2, StCheck, StDone
  } ptw_state_e;

  ptw_state_e state_d, state_q;

  always_comb begin
    state_d               = state_q;
    ptw_tlb_req_rdy_o     = 1'b0;
    load_cnt_o            = 1'b0;
    ptw_mmuc_req_valid_o  = 1'b0;
    mux_rx_sel_internal_o = 1'b0;
    reg_tx_cond_en_o      = 1'b0;
    reg_ans_cond_en_o     = 1'b0;
    chk_en_o              = 1'b0;
    mmuc_update_cond_en_o = 1'b0;
    ptw_l2c_req_valid_o   = 1'b0;
    ptw_l2c_ans_rdy_o     = 1'b0;
    reg_rx_cond_en_o      = 1'b0;
    cnt_cond_en_o         = 1'b0;
    ptw_tlb_ans_valid_o   = 1'b0;
    unique case (state_q)
      // StIdle: wait for L2-TLB valid request
      StIdle: begin
        ptw_tlb_req_rdy_o                = 1'b1;
        if (tlb_ptw_req_valid_i) state_d = StMmucReq;
      end
      // StMmucReq: query the MMUC
      StMmucReq: begin
        load_cnt_o            = 1'b1;
        ptw_mmuc_req_valid_o  = 1'b1;
        mux_rx_sel_internal_o = 1'b1;
        reg_rx_cond_en_o      = 1'b1;
        state_d               = StInitialPaddr;
      end
      // StInitialPaddr: compose the physical address
      StInitialPaddr: begin
        reg_tx_cond_en_o        = 1'b1;
        state_d                 = StL2Req;
      end
      // StL2Req: req a PTE to L2-Cache
      StL2Req: begin
        ptw_l2c_req_valid_o            = 1'b1;
        if (l2c_ptw_req_rdy_i) state_d = StWaitL2;
      end
      // StWaitL2: wait for L2 ans
      StWaitL2: begin
        ptw_l2c_ans_rdy_o                = 1'b1;
        reg_rx_cond_en_o                 = 1'b1;
        cnt_cond_en_o                    = 1'b1;
        if (l2c_ptw_ans_valid_i) state_d = StCheck;
      end
      // StCheck: check the PTE, compose the physical address
      StCheck: begin
        reg_tx_cond_en_o        = 1'b1;
        reg_ans_cond_en_o       = 1'b1;
        chk_en_o                = 1'b1;
        mmuc_update_cond_en_o   = 1'b1;
        if (ptw_done_i) state_d = StDone;
        else            state_d = StL2Req;
      end
      // StDone: valid ans to L2-TLB
      StDone: begin
        ptw_tlb_ans_valid_o            = 1'b1;
        if (tlb_ptw_ans_rdy_i) state_d = StIdle;
      end
      default: begin
        state_d = StIdle;
      end
    endcase
  end

  // Sample next state into present state
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StIdle;
    end else begin
      state_q <= state_d;
    end
  end

endmodule
