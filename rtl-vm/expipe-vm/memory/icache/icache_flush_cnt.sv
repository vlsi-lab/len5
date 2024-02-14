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
// File: icache_flush_cnt.sv
// Author: Matteo Perotti
// Date: 29/10/2019
// Description: flush counter for i-Cache flushing

import len5_pkg::*;

import memory_pkg::*;

module icache_flush_cnt (
    // Main
    input logic clk_i,
    input logic rst_ni,
    // From the CU: count enable
    input logic flushing_i,
    // The flush address used to index the sets of the cache
    output icache_idx_addr_t flush_addr_o,
    // To the CU: next cycle the cache will be ready
    output logic last_set_to_flush_o  // Terminal count of the counter -> This is the last set
);

  icache_idx_addr_t cnt;
  logic             tc;

  // Counting process
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
    end else if (flushing_i) begin
      cnt <= cnt + 1;
    end
  end

  // Terminal count
  assign tc = &cnt;

  assign flush_addr_o = cnt;
  assign last_set_to_flush_o = tc;

endmodule
