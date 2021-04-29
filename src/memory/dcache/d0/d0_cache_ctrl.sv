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
// File: d0_cache_ctrl.sv
// Author: Matteo Perotti
// Date: 24/10/2019
// Description: combinatorial cache controller

import memory_pkg::*;

module d0_cache_ctrl
#(
  N_WAY        = DCACHE_L1_ASSOCIATIVITY,
  BYTE_OFF_LEN = DCACHE_L1_LINE_OFF_A_LEN + DCACHE_L1_WORD_A_LEN,
  TVD_BE_LEN   = ((DCACHE_L1_TVD_LEN) + 7) / 8,
  DATA_BE_LEN  = DCACHE_L1_LINE_SIZE
)
(
  // Main enable and request type
  input logic                    d0_enable_i,
  input d0_req_type_e            d0_req_type_i,
  // The store can be of a Byte, a HalfWord, a Word or a DoubleWord
  store_width_e                  store_width_i,
  // Encoded line offset to write only the correct bytes (store DW)
  input logic [BYTE_OFF_LEN-1:0] byte_addr_in_line_i,
  // Hit vector, next line to be replaced and one-hotted dirty vector form d1
  input logic [N_WAY-1:0]        hit_vec_i,
  input logic [N_WAY-1:0]        replace_vec_i,
  input logic [N_WAY-1:0]        d1_one_hot_dirty_vec_i, // useful when performing an L2 updating
  // d1 stalled because the store buffer is full
  input logic                    d1_stalled_i,
  // The physical control signals
  output dcache_ctrl_t           d0_cache_ctrl_o
);

  localparam DW_IN_LINE = DCACHE_L1_LINE_SIZE / DCACHE_L1_WORD_SIZE; // How many doublewords in a line
  localparam W_IN_LINE  = 2*DW_IN_LINE;                              // How many words in a line
  localparam HW_IN_LINE = 2*W_IN_LINE;                               // How many halfwords in a line
  localparam B_IN_LINE  = 2*HW_IN_LINE;                              // How many bytes in a line

  tmem_ctrl_t [N_WAY-1:0] tvd_ctrl_vec;
  dmem_ctrl_t [N_WAY-1:0] data_ctrl_vec;

  logic [DATA_BE_LEN-1:0] store_be; // Store byte enable

  assign d0_cache_ctrl_o.tvd_ctrl_vec  = tvd_ctrl_vec;
  assign d0_cache_ctrl_o.data_ctrl_vec = data_ctrl_vec;

  // Store byte enable definition. The granularity of the selection depends on the store width
  always_comb begin
    store_be = '0;
    case (store_width_i)
      B:  begin
        for (int k = 0; k < B_IN_LINE; k++) begin
          store_be[k]      = (k == byte_addr_in_line_i) ? 1'b1 : 1'b0;
        end
      end
      HW: begin
        for (int k = 0; k < HW_IN_LINE; k++) begin
          store_be[2*k+:2] = (k == byte_addr_in_line_i[BYTE_OFF_LEN-1:1]) ? '1 : '0;
        end
      end
      W:begin
        for (int k = 0; k < W_IN_LINE; k++) begin
          store_be[4*k+:4] = (k == byte_addr_in_line_i[BYTE_OFF_LEN-1:2]) ? '1 : '0;
        end
      end
      DW: begin
        for (int k = 0; k < DW_IN_LINE; k++) begin
          store_be[8*k+:8] = (k == byte_addr_in_line_i[BYTE_OFF_LEN-1:3]) ? '1 : '0;
        end
      end
    endcase
  end

  always_comb begin
    // Mask the control
      tvd_ctrl_vec  = '0;
      data_ctrl_vec = '0;
    // Cache ctrl behavioural description
    if (d0_enable_i) begin
      unique case (d0_req_type_i)
        // Full read
        d0_ReadLsq, d0_ReadD1, d0_ReadL2: begin
          for (int k = 0; k < N_WAY; k++) begin
            tvd_ctrl_vec[k].cs  = 1'b1;
            tvd_ctrl_vec[k].be  = '1;
            data_ctrl_vec[k].cs = 1'b1;
            data_ctrl_vec[k].be = '1;
          end
        end
        // Full line write
        d0_WriteCleanLineD1, d0_WriteDirtyLineD1: begin
          for (int k = 0; k < N_WAY; k++) begin
            tvd_ctrl_vec[k].cs  = replace_vec_i[k];
            tvd_ctrl_vec[k].we  = replace_vec_i[k];
            tvd_ctrl_vec[k].be  = '1;
            data_ctrl_vec[k].cs = replace_vec_i[k];
            data_ctrl_vec[k].we = replace_vec_i[k];
            data_ctrl_vec[k].be = '1;
          end
        end
        // Doubleword write
        d0_WriteStoreD1: begin
          for (int k = 0; k < N_WAY; k++) begin
            tvd_ctrl_vec[k].cs      = hit_vec_i[k];
            tvd_ctrl_vec[k].we      = hit_vec_i[k];
            tvd_ctrl_vec[k].be[1:0] = 2'b11;        // make dirty, keep valid, preserve tag
            data_ctrl_vec[k].cs     = hit_vec_i[k];
            data_ctrl_vec[k].we     = hit_vec_i[k];
            data_ctrl_vec[k].be     = store_be;     // write the correct bytes of the line
          end
        end
        // Write only the dirty bit
        d0_CleanDirty: begin
          for (int k = 0; k < N_WAY; k++) begin
            tvd_ctrl_vec[k].cs                 = d1_one_hot_dirty_vec_i[k];
            tvd_ctrl_vec[k].we                 = d1_one_hot_dirty_vec_i[k];
            tvd_ctrl_vec[k].be[TVD_BE_LEN-1:2] = '0;
            tvd_ctrl_vec[k].be[1:0]            = 2'b11; // Last 2 bytes if d_bit is the bit 0 and not the bit 1
          end
        end
        // If the buffer can't tolerate the request, wait for a free entry
        d0_ReadUpdate: begin
          if (!d1_stalled_i) begin
            for (int k = 0; k < N_WAY; k++) begin
              tvd_ctrl_vec[k].cs  = 1'b1;
              tvd_ctrl_vec[k].be  = '1;
              data_ctrl_vec[k].cs = 1'b1;
              data_ctrl_vec[k].be = '1;
            end
          end
        end
        // Write '0' to the valid bit of all the lines into the set
        d0_ResetLines: begin
          for (int k = 0; k < N_WAY; k++) begin
            tvd_ctrl_vec[k].cs                 = 1'b1;
            tvd_ctrl_vec[k].we                 = 1'b1;
            tvd_ctrl_vec[k].be[TVD_BE_LEN-1:2] = '0;
            tvd_ctrl_vec[k].be[1:0]            = 2'b11; // Last 2 bytes if d_bit is the bit 0 and not the bit 1
          end
        end
        // Redundant default assignment. For an optimization, can become 'X
        default: begin
          tvd_ctrl_vec  = '0;
          data_ctrl_vec = '0;
        end
      endcase
    end
  end

endmodule
