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
// File: itlb_moore_cu.sv
// Author: Matteo Perotti
// Date: 31/10/2019
// Description: moore control for the i-TLB


import len5_pkg::*;
import memory_pkg::*;

module itlb_moore_cu
(
  // Main
  input logic       clk_i,
  input logic       rst_ni,
  input logic       abort_i,
  input logic       vmem_on_i,
  // Conditions for state change
  input logic       cache_req_valid_i,
  input exception_e internal_exception_i,
  input logic       itlb_hit_i,
  input logic       l2c_req_rdy_i,
  input logic       l2c_ans_valid_i,
  // Output control
  output logic      tlb_cond_ready_o,  // i-TLB ready if !(valid access && miss)
  output logic      l2c_req_valid_o,   // L2C valid request
  output logic      l2c_ans_rdy_o,     // Ready for L2C answer
  output logic      waiting_l2c_ans_o // Replace request to the i-TLB
);

  typedef enum logic [1:0] {
    StReady, StL2Req, StL2Wait
  } itlb_state_e;

  itlb_state_e state_d, state_q;

  always_comb begin
    state_d                      = StReady;
    tlb_cond_ready_o             = 1'b0;
    l2c_req_valid_o              = 1'b0;
    l2c_ans_rdy_o                = 1'b0;
    waiting_l2c_ans_o            = 1'b0;
    case (state_q)
      StReady: begin
        tlb_cond_ready_o = 1'b1;
        if (cache_req_valid_i && !internal_exception_i && !itlb_hit_i) begin
          state_d = StL2Req;
        end
      end
      StL2Req: begin
        l2c_req_valid_o = 1'b1;
        if (l2c_req_rdy_i) state_d = StL2Wait;
        else               state_d = StL2Req;
      end
      StL2Wait: begin
        l2c_ans_rdy_o                = 1'b1;
        waiting_l2c_ans_o            = 1'b1;
        if (l2c_ans_valid_i) state_d = StReady;
        else                 state_d = StL2Wait;
      end
    endcase
    if (abort_i) state_d = StReady;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StReady;
    end else begin
      state_q <= state_d;
    end
  end

endmodule
