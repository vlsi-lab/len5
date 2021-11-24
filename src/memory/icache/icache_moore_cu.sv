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
// File: icache_moore_cu.sv
// Author: Matteo Perotti
// Date: 29/10/2019
// Description: Moore CU of the i-Cache which control the memory address source and the misses/requests policy


import len5_pkg::*;
import memory_pkg::*;

module icache_moore_cu (
  // Main
  input logic              clk_i,
  input logic              rst_ni,
  input logic              flush_i,            // Flush the whole cache
  input logic              abort_op_i,         // Abort pending operations
  // From the icache
  input logic              is_last_set_i,      // The terminal counter of the flush counter used to address the cache
  input logic              cache_hit_i,        // The cache hit signal
  // From the Front-End
  input logic              fend_req_valid_i,   // Valid front end request
  // From the i-TLB
  input logic              itlb_rdy_i,         // The i-TLB is ready to accept a request
  input logic              itlb_hit_i,         // The requested page was in the TLB
  input logic              is_exception_i,     // The requested page threw an exception
  // From L2 Cache
  input logic              l2c_req_rdy_i,      // L2C is ready to accept the request
  input logic              l2c_ans_valid_i,    // L2C is returning a valid answer
  // To the icache
  output logic             flushing_o,         // Used as count enable for the flush counter
  output logic             comparing_o,        // Cache is working on a request
  output logic             replaying_o,        // Cache replaying the instruction after the replacement
  output logic             waiting_tlb_o,      // Waiting for the TLB
  output logic             waiting_l2c_o,      // Waiting for L2C
  output icache_addr_src_e icache_addr_src_o,  // Where does the memory address come from
  output icache_ctrl_e     icache_cond_ctrl_o, // i-Cache conditional control
  // To L2 Cache
  output logic             l2c_req_valid_o,    // L2C request valid
  // To the i-TLB
  output logic             itlb_req_valid_o    // Valid i-TLB request
);

  typedef enum logic [2:0] {
    StFlush,        // The cache is flushing
    StReady,        // The cache is ready to accept new requests
    StTLBReqTagCmp, // The cache is querying the TLB and evaluating the responses
    StWaitTLB,      // Waiting for a not ready TLB
    StL2Req,        // L2 request until it is accepted
    StWaitL2,       // Waiting for L2
    StReadReplay    // Replay the read after the line was replaced
  } icache_state_t;

  icache_state_t state_d, state_q;

  always_comb begin
    // Default assignments
    state_d            = StFlush;
    flushing_o         = 1'b0;
    comparing_o        = 1'b0;
    replaying_o        = 1'b0;
    waiting_tlb_o      = 1'b0;
    waiting_l2c_o      = 1'b0;
    icache_addr_src_o  = VaddrD;
    icache_cond_ctrl_o = Idle;
    l2c_req_valid_o    = 1'b0;
    itlb_req_valid_o   = 1'b0;
    case (state_q)
      StFlush: begin
        flushing_o         = 1'b1;
        icache_addr_src_o  = FlushCnt;
        icache_cond_ctrl_o = InvalidSet;
        state_d            = (is_last_set_i) ? StReady : StFlush;
      end
      StReady: begin
        icache_cond_ctrl_o = ReadSet;
        state_d            = (fend_req_valid_i) ? StTLBReqTagCmp : StReady;
      end
      StTLBReqTagCmp: begin
        comparing_o        = 1'b1;
        icache_cond_ctrl_o = ReadSet;
        itlb_req_valid_o   = 1'b1;
        if (!itlb_rdy_i || (!itlb_hit_i && !is_exception_i)) state_d = StWaitTLB;
        else if (!is_exception_i && !cache_hit_i)            state_d = StL2Req;
        // else if (is_exception_i || (!is_exception_i && cache_hit_i))
        else begin
          if (fend_req_valid_i) state_d = StTLBReqTagCmp;
          else                  state_d = StReady;
        end
      end
      StWaitTLB: begin
        waiting_tlb_o       = 1'b1;
        icache_cond_ctrl_o  = ReadSet;
        icache_addr_src_o   = VaddrQ;
        state_d             = (itlb_rdy_i) ? StTLBReqTagCmp : StWaitTLB;
      end
      StL2Req: begin
        icache_cond_ctrl_o  = Idle;
        l2c_req_valid_o     = 1'b1;
        state_d             = (l2c_req_rdy_i) ? StWaitL2 : StL2Req;
      end
      StWaitL2: begin
        waiting_l2c_o       = 1'b1;
        icache_cond_ctrl_o  = WriteLineAndTag;
        icache_addr_src_o   = VaddrQ;
        state_d             = (l2c_ans_valid_i) ? StReadReplay : StWaitL2;
      end
      StReadReplay: begin
        replaying_o         = 1'b1;
        icache_cond_ctrl_o  = ReadSet;
        icache_addr_src_o   = VaddrQ;
        state_d             = StTLBReqTagCmp;
      end
    endcase
    // In every case, if an abort request arrives, stop the current operation
    if (flush_i)         state_d = StFlush;
    else if (abort_op_i) state_d = StReady;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StFlush;
    end else begin
      state_q <= state_d;
    end
  end

endmodule
