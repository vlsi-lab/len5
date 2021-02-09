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
// File: l2_tlb_flush_unit.sv
// Author: Matteo Perotti
// Date: 04/11/2019
// Description: L2-TLB flush unit
// Details: keep a valid flush request for t0 and provide the flush index

`include "memory_pkg.sv"
import memory_pkg::*;

module l2_tlb_flush_unit
#(
  A = L2_TLB_IDX_LEN
)
(
  // Main
  input  logic         clk_i,
  input  logic         rst_ni,
  // Trigger for the flush
  input  tlb_flush_e   flush_type_i,
  // Update the address
  input  logic         flush_idx_cnt_en_i,
  // Address to target and flush a specific set *
  output logic [A-1:0] flush_idx_o,
  // Valid flushing request for t0
  output tlb_flush_e   flush_type_o,
  output logic         flush_req_valid_o
);

  typedef enum logic [1:0] {
    StIdle, StTotalFlushing, StASIDFlushing, StPageFlushing
  } flush_state_t;

  flush_state_t state_d, state_q;

  logic [A-1:0] flush_idx;

  logic last_set;
  logic flush_end;

  assign flush_idx_o = flush_idx;

  // Flush counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      flush_idx <= '0;
    end else if (flush_idx_cnt_en_i) begin
      flush_idx <= flush_idx + 1;
    end
  end
  // Asserted when the last set is being addressed
  assign last_set = &flush_idx;
  // Asserted if the last set is being addressed and the counter is being updated
  assign flush_end = (flush_idx_cnt_en_i && last_set);

  // Flush control
  always_comb begin
    state_d           = StIdle;
    flush_type_o      = NoFlush;
    flush_req_valid_o = 1'b0;
    case (state_q)
      StIdle: begin
        if      (flush_type_i == FlushAll ) state_d = StTotalFlushing;
        else if (flush_type_i == FlushASID) state_d = StASIDFlushing;
        else if (flush_type_i == FlushPage) state_d = StPageFlushing;
      end
      StTotalFlushing: begin
        flush_type_o            = FlushAll;
        flush_req_valid_o       = 1'b1;
        if (!flush_end) state_d = StTotalFlushing;
      end
      StASIDFlushing: begin
        flush_type_o            = FlushASID;
        flush_req_valid_o       = 1'b1;
        if (!flush_end) state_d = StASIDFlushing;
      end
      StPageFlushing: begin
        flush_type_o            = FlushPage;
        flush_req_valid_o       = 1'b1;
        if (!flush_end) state_d = StPageFlushing;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StTotalFlushing;
    end else begin
      state_q <= state_d;
    end
  end


endmodule

// * It was hypothesized a number of sets which is a power of 2
