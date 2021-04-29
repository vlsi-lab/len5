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
// File: d0_req_encoder.sv
// Author: Matteo Perotti
// Date: 23/10/2019
// Description: encode the actual scheduled request into instructions for d0 and d1

import memory_pkg::*;

module d0_req_encoder
(
  // Scheduler -> Req Encoder
  input  d0_winner_e       winner_i,
  // Information about requests and answers
  input  d1_d0_req_type_e  d1_req_type_i,
  input  l2c_d0_ans_type_e l2c_ans_type_i,
  input  lsq_d0_req_type_e lsq_req_type_i,
  // Req Encoder -> d0
  output d0_req_type_e     d0_req_type_o,
  // Req Encoder -> d0 output regs
  output d0_d1_req_type_e  d1_next_req_type_o
);

  always_comb begin
    // Default case
    d0_req_type_o      = d0_Idle;
    d1_next_req_type_o = d0_d1_Idle;
    case (winner_i)
      LSQ: begin
        // Load - d0: read, d1: load
        if (lsq_req_type_i == Load) begin
          d0_req_type_o      = d0_ReadLsq;
          d1_next_req_type_o = d0_d1_Load;
        // Store - d0: read, d1: store
        end else if (lsq_req_type_i == Store) begin
          d0_req_type_o      = d0_ReadLsq;
          d1_next_req_type_o = d0_d1_Store;
        end
      end
      UpdateL2: begin
        // Update L2 - d0: read idx from cnt, d1: write the buf and control dirty clean and cnt
        d0_req_type_o      = d0_ReadUpdate;
        d1_next_req_type_o = d0_d1_UpdateL2;
      end
      L2Cache: begin
        // Requested line from L2 - d0: read using L2 addr, d1: target line dirty?
        if (l2c_ans_type_i == ReplaceLine) begin
          d0_req_type_o      = d0_ReadL2;
          d1_next_req_type_o = d0_d1_ReplaceReq;
        // Store hit info from L2 - d0: forward store address, d1: inform the buffer
        end else if (l2c_ans_type_i == StoreHit) begin
          d0_req_type_o      = d0_FwdL2StAddr;
          d1_next_req_type_o = d0_d1_L2StHit;
        end else if (l2c_ans_type_i == WWBWakeUp) begin
          d0_req_type_o      = d0_FwdL2StAddr;
          d1_next_req_type_o = d0_d1_L2WBBWakeUp;
        end
      end
      D1: begin
        // d1 load replay req - d0: read using d1 addr, d1: load
        if (d1_req_type_i == LoadReplay) begin
          d0_req_type_o      = d0_ReadD1;
          d1_next_req_type_o = d0_d1_Load;
        // d1 store replay req - d0: write using d1 addr, d1: nothing
        end else if (d1_req_type_i == StoreReplay) begin
          d0_req_type_o      = d0_ReadD1;
          d1_next_req_type_o = d0_d1_Store;
        // d1 write clean line req - d0: write using d1 line addr, d1: nothing
        end else if (d1_req_type_i == WriteCleanLine) begin
          d0_req_type_o      = d0_WriteCleanLineD1;
          d1_next_req_type_o = d0_d1_Idle;
        // d1 write dirty line req - d0: write using d1 line addr, d1: nothing
        end else if (d1_req_type_i == WriteDirtyLine) begin
          d0_req_type_o      = d0_WriteDirtyLineD1;
          d1_next_req_type_o = d0_d1_Idle;
        // d1 write doubleword req - d0: write using d1 doubleword addr, d1: nothing
        end else if (d1_req_type_i == WriteStore) begin
          d0_req_type_o      = d0_WriteStoreD1;
          d1_next_req_type_o = d0_d1_Idle;
        // d1 clean req - d0: clean the dirty, d1: nothing
        end else if (d1_req_type_i == CleanDirty) begin
          d0_req_type_o      = d0_CleanDirty;
          d1_next_req_type_o = d0_d1_Idle;
        end else if (d1_req_type_i == WaitL2UpdatingCnt) begin
          d0_req_type_o      = d0_Idle;
          d1_next_req_type_o = d0_d1_Idle;
        end
      end
      RstBlock: begin
        // Reset the cache - d0: invalid lines, d1: nothing
        d0_req_type_o      = d0_ResetLines;
        d1_next_req_type_o = d0_d1_Idle;
      end
    endcase
  end

endmodule
