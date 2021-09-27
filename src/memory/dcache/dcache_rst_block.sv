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
// File: dcache_rst_block.sv
// Author: Matteo Perotti
// Date: 25/10/2019
// Description: block to handle the initial dcache reset

import memory_pkg::*;

module dcache_rst_block
#(
  IDX_LEN = DCACHE_L1_IDX_A_LEN
)
(
  // At "reset" the cache is fully reset
  input  logic          clk_i,
  input  logic          rst_ni,
  // The address of the set
  output rst_l1dc_req_t rst_l1dc_req_o
);

  typedef enum logic {
    StReset, StDone
  } state_t;

  state_t state_d, state_q;

  dcache_addr_t cnt;    // Count signal
  logic         en_cnt; // Coutner enable
  logic         tc;     // Terminal Count

  // Counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      cnt <= 0;
    end else begin
      cnt <= cnt + 1;
    end
  end

  assign tc = &cnt;

  // Control Unit
  always_comb begin
    case (state_q)
      StReset: begin
        rst_l1dc_req_o.valid = 1'b1;
        if (tc) state_d = StDone;
        else    state_d = StReset;
      end
      StDone:  begin
        rst_l1dc_req_o.valid = 1'b0;
        state_d = StDone;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      state_q <= StReset;
    end else begin
      state_q <= state_d;
    end
  end

  // Ouput address binding
  assign rst_l1dc_req_o.dcache_addr = cnt;

endmodule
