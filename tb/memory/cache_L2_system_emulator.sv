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
// File: cache_L2_system_emulator.sv
// Author: Matteo Perotti
// Date: 10/11/2019
// Description: behavioural emulator of a non-blocking L2 Cache system

`include "../tb/memory/memory_class.svh"

import len5_pkg::*;
import memory_pkg::*;

module cache_L2_system_emulator #(
  parameter MEM_FILE_PATH = "memory.txt"
) (
    // Main
    input   logic           clk_i,
    input   logic           rst_ni,
    input   logic           flush_i,
    // (L2 arbiter -> L2 Cache) request channel
    input l2arb_l2c_req_t l2arb_l2c_req_i,
    output  logic           l2c_l2arb_req_rdy_o,
    // (L2 Cache -> L2 arbiter) answer channel
    output  l2c_l2arb_ans_t l2c_l2arb_ans_o,
    input   logic           l2arb_l2c_ans_rdy_i,

    // Memory file
    input   string          mem_file_i = MEM_FILE_PATH
);

  //--------------------\\
  // TUNABLE PARAMETERS \\
  //--------------------\\

  localparam isAlwaysHit = 1;

  //------------\\
  // PARAMETERS \\
  //------------\\

  localparam BUF_LEN       = 3;
  localparam LOG2_BUF_LEN  = $clog2(BUF_LEN);
  localparam H_DELAY       = BUF_LEN-1;
  localparam M_DELAY       = 7;

  l2arb_l2c_req_t          req_vec    [BUF_LEN]; // The buffer for the requests
  int                      time_vec   [BUF_LEN]; // How many clocks the request should wait before completion (if L2 Arb ready)
  int                      missed_vec [BUF_LEN]; // A tag to specify if the request missed ('0' -> hit, '1' -> missed)
  logic [LOG2_BUF_LEN-1:0] free_idx;
  logic [BUF_LEN-1:0]      free_oh_vec;
  logic [LOG2_BUF_LEN-1:0] ans_valid_idx;
  logic [BUF_LEN-1:0]      ans_valid_vec;
  logic [BUF_LEN-1:0]      ans_valid_oh_vec;
  logic                    buf_stalled;
  logic                    stalling_event;
  logic                    stalled_answer;
  logic                    ans_tie;
  logic                    free_idx_valid;
  logic                    ans_valid_idx_valid;
  logic [XLEN-1:0]         memory_dw_addr;
  logic [XLEN-1:0]         memory_line_addr;

  memory_class i_memory = new(mem_file_i);

  //-----------------\\
  // CACHE REQ READY \\
  //-----------------\\

  // L2 Cache ready if not stalled and no ties, and if there is at least one free entry or one entry which will be freed within this cycle
  assign l2c_l2arb_req_rdy_o = (!buf_stalled && !ans_tie && (free_idx_valid || ans_valid_idx_valid)) ? 1'b1 : 1'b0;

  //---------------\\
  // STALL CONTROL \\
  //---------------\\

  // Stall if a stall event occurs or if the answer is stalled because L2 Arbiter is not ready
  assign buf_stalled = stalling_event || stalled_answer;

  // Stall event (random stall)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stalling_event <= 1'b0;
    end else begin
      stalling_event <= $urandom_range(1, 0);
    end
  end

  // An answer is stalled because the L2 Arbiter is not ready
  assign stalled_answer = (l2c_l2arb_ans_o.valid && !l2arb_l2c_ans_rdy_i);

  //-----------------\\
  // BUFFER UPDATING \\
  //-----------------\\

  // Entry insertion and delay updating
  for (genvar k = 0; k < BUF_LEN; k++) begin
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if(!rst_ni) begin
        req_vec[k]    <= '0;
        time_vec[k]   <= '0;
        missed_vec[k] <= 1'b0;
      end else if (flush_i) begin
        req_vec[k].valid <= 1'b0;
      // If this is the next available position
      end else if (free_oh_vec[k]) begin
        // If there is a valid request, there is no tie and the buffer is not stalled
        if (l2arb_l2c_req_i.valid && !buf_stalled && !ans_tie) begin
          // Save the request in this entry
          req_vec[k]      <= l2arb_l2c_req_i;
          if ($urandom_range(1, 0)) begin
            time_vec[k]   <= H_DELAY;
            missed_vec[k] <= 1'b0;
          end else begin
            time_vec[k]   <= (isAlwaysHit) ? H_DELAY : M_DELAY;
            missed_vec[k] <= (isAlwaysHit) ? 1'b0    : 1'b1   ;
          end
        end
      // If this is the valid entry ready to be processed
      end else if (ans_valid_oh_vec[k]) begin
        // If the buffer is not stalled
        if (!buf_stalled) begin
          // Remove the entry
          req_vec[k].valid <= 1'b0;
          // If there is not space in the buffer but there is a request, put it here!
          if (!free_idx_valid && l2arb_l2c_req_i.valid) begin
            req_vec[k]  <= l2arb_l2c_req_i;
            if ($urandom_range(1, 0)) begin
              time_vec[k]   <= H_DELAY;
              missed_vec[k] <= 1'b0;
            end else begin
              time_vec[k]   <= (isAlwaysHit) ? H_DELAY : M_DELAY;
              missed_vec[k] <= (isAlwaysHit) ? 1'b0    : 1'b1   ;
            end
          end
        end
      end else if (req_vec[k].valid) begin
        // Let the requests percolate through the pipeline only if there is no tie and the pipe is not stalled
        if (!ans_tie && !buf_stalled) time_vec[k] <= time_vec[k] - 1;
      end
    end
  end

  // Asserted if more than one valid entry is ready to leave the buffer
  assign ans_tie = (ans_valid_vec != ans_valid_oh_vec) ? 1'b1 : 1'b0;

  //------------------------------\\
  // REGISTER ENABLES AND INDEXES \\
  //------------------------------\\

  // One hot index and valid
  always_comb begin
    free_idx       = '0;
    free_idx_valid = 1'b0;
    for (int k = BUF_LEN-1; k >= 0; k--) begin
      if (!req_vec[k].valid) free_idx = k;
      free_idx_valid |= !req_vec[k].valid;
    end
  end
  // One hot free vec formation
  always_comb begin
    free_oh_vec           = '0;
    free_oh_vec[free_idx] = (free_idx_valid) ? 1'b1 : 1'b0;
  end

  // One hot index and ans_rdy_vec creation
  always_comb begin
    ans_valid_idx = '0;
    ans_valid_vec = '0;
    for (int k = BUF_LEN-1; k >= 0; k--) begin
      if (req_vec[k].valid && time_vec[k] == 0) begin
        ans_valid_idx    = k;
        ans_valid_vec[k] = 1'b1;
      end
    end
  end
  assign ans_valid_idx_valid = |ans_valid_vec;
  // One hot ans ready vec formation
  always_comb begin
    ans_valid_oh_vec                = '0;
    ans_valid_oh_vec[ans_valid_idx] = (ans_valid_idx_valid) ? 1'b1 : 1'b0;
  end

  //--------\\
  // ANSWER \\
  //--------\\

  assign memory_dw_addr   = {req_vec[ans_valid_idx].paddr.tag, req_vec[ans_valid_idx].paddr.idx, req_vec[ans_valid_idx].paddr.line_off, 3'b0};
  assign memory_line_addr = {req_vec[ans_valid_idx].paddr.tag, req_vec[ans_valid_idx].paddr.idx, 6'b0};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      l2c_l2arb_ans_o.line      <= '0;
      l2c_l2arb_ans_o.data      <= '0;
      l2c_l2arb_ans_o.paddr     <= '0;
      l2c_l2arb_ans_o.wbb_tag   <= '0;
      l2c_l2arb_ans_o.ans_type  <= l2arb_s0_PTWLoad;
      l2c_l2arb_ans_o.valid     <= 1'b0;
    // Process and answer only if there is one ready request and the buffer is not stalled, and if there is space to do so
    end else if (ans_valid_idx_valid && !buf_stalled) begin
      unique case (req_vec[ans_valid_idx].req_type)
        IReadLine: begin
          void'(i_memory.ReadLine(memory_line_addr));
          l2c_l2arb_ans_o.line      <= i_memory.read_line;
          l2c_l2arb_ans_o.data      <= '0;
          l2c_l2arb_ans_o.paddr     <= req_vec[ans_valid_idx].paddr;
          l2c_l2arb_ans_o.wbb_tag   <= '0;
          l2c_l2arb_ans_o.ans_type  <= l2arb_s0_ILineRead;
          l2c_l2arb_ans_o.valid     <= 1'b1;
        end
        DReadLine: begin
          void'(i_memory.ReadLine(memory_line_addr));
          l2c_l2arb_ans_o.line      <= i_memory.read_line;
          l2c_l2arb_ans_o.data      <= '0;
          l2c_l2arb_ans_o.paddr     <= req_vec[ans_valid_idx].paddr;
          l2c_l2arb_ans_o.wbb_tag   <= '0;
          l2c_l2arb_ans_o.ans_type  <= l2arb_s0_DLineRead;
          l2c_l2arb_ans_o.valid     <= 1'b1;
        end
        DWriteLine: begin
          l2c_l2arb_ans_o.line      <= '0;
          l2c_l2arb_ans_o.data      <= '0;
          l2c_l2arb_ans_o.paddr     <= req_vec[ans_valid_idx].paddr;
          l2c_l2arb_ans_o.wbb_tag   <= req_vec[ans_valid_idx].wbb_tag;
          l2c_l2arb_ans_o.ans_type  <= (missed_vec[ans_valid_idx]) ? l2arb_s0_DWbbWakeUp : l2arb_s0_DLineWritten;
          l2c_l2arb_ans_o.valid     <= 1'b1;
          void'(i_memory.WriteLine(memory_line_addr, l2arb_l2c_req_i.line));
        end
        PTWLoad: begin
          void'(i_memory.ReadDW(memory_dw_addr));
          l2c_l2arb_ans_o.line      <= '0;
          l2c_l2arb_ans_o.data      <= i_memory.read_doubleword;
          l2c_l2arb_ans_o.paddr     <= req_vec[ans_valid_idx].paddr;
          l2c_l2arb_ans_o.wbb_tag   <= '0;
          l2c_l2arb_ans_o.ans_type  <= l2arb_s0_PTWLoad;
          l2c_l2arb_ans_o.valid     <= 1'b1;
        end
        default: begin
          l2c_l2arb_ans_o.line      <= '0;
          l2c_l2arb_ans_o.data      <= '0;
          l2c_l2arb_ans_o.paddr     <= '0;
          l2c_l2arb_ans_o.wbb_tag   <= '0;
          l2c_l2arb_ans_o.ans_type  <= l2arb_s0_PTWLoad;
          l2c_l2arb_ans_o.valid     <= 1'b0;
        end
      endcase
    end else if (l2arb_l2c_ans_rdy_i) begin
      l2c_l2arb_ans_o.line      <= '0;
      l2c_l2arb_ans_o.data      <= '0;
      l2c_l2arb_ans_o.paddr     <= '0;
      l2c_l2arb_ans_o.wbb_tag   <= '0;
      l2c_l2arb_ans_o.ans_type  <= l2arb_s0_PTWLoad;
      l2c_l2arb_ans_o.valid     <= 1'b0;
    end
  end

endmodule
