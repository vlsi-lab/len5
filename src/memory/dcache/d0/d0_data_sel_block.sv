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
// File: d0_data_sel_block.sv
// Author: Matteo Perotti
// Date: 24/10/2019
// Description: select the incoming data and let it reach the cache and the output registers

import memory_pkg::*;

module d0_data_sel_block
(
  // d0 req type
  input  d0_req_type_e    d0_req_type_i,
  input  d0_d1_req_type_e d1_req_type_i,
  // LSQ request
  input lsq_l1dc_req_t   lsq_l1dc_req_i,
  // L2C answer
  input l2c_l1dc_ans_t   l2c_l1dc_ans_i,
  // d1 request
  input d1_d0_req_t      d1_d0_req_i,
  // Update L2 request
  input upd_l1dc_req_t   upd_l1dc_req_i,
  // Reset request
  input rst_l1dc_req_t   rst_l1dc_req_i,
  // To Ouput Registers
  output d1_req_info_t    reg_out_d_o,
  // To the cache
  output dcache_addr_t    dcache_addr_o,
  output dcache_line_t    dcache_wdata_o,
  output tvd_mem_line_t   dcache_wtvd_o
);

  localparam TAG_A_LEN = DCACHE_L1_TAG_A_LEN;
  localparam LINE_BYTE_OFF_A_LEN = DCACHE_L1_WORD_A_LEN + DCACHE_L1_LINE_OFF_A_LEN;

  localparam DW_IN_LINE = DCACHE_L1_LINE_SIZE / DCACHE_L1_WORD_SIZE; // How many doublewords in a line
  localparam W_IN_LINE  = 2*DW_IN_LINE;                              // How many words in a line
  localparam HW_IN_LINE = 2*W_IN_LINE;                               // How many halfwords in a line
  localparam B_IN_LINE  = 2*HW_IN_LINE;                              // How many bytes in a line

  // doubleword to line adapter (to be optimized)
  dcache_line_t line_adapted_dw;
  dcache_line_t line_adapted_w;
  dcache_line_t line_adapted_hw;
  dcache_line_t line_adapted_b;

  // paddr zero filling auxiliary vectors
  logic [TAG_A_LEN-1:0]           zero_tag;
  logic [LINE_BYTE_OFF_A_LEN-1:0] zero_wb;

  // To be optimized! Select only the
  assign line_adapted_dw = {DW_IN_LINE{d1_d0_req_i.data}};       // Replicate the DW on the line
  assign line_adapted_w  = {W_IN_LINE{d1_d0_req_i.data[31:0]}};  // Replicate the W on the line
  assign line_adapted_hw = {HW_IN_LINE{d1_d0_req_i.data[15:0]}}; // Replicate the HW on the line
  assign line_adapted_b  = {B_IN_LINE{d1_d0_req_i.data[7:0]}};   // Replicate the B on the line

  // d1 request type has already been calculated
  assign reg_out_d_o.req_type = d1_req_type_i;

  assign zero_tag = '0;
  assign zero_wb  = '0;

  always_comb begin
    // Default masking
    reg_out_d_o.valid           = 1'b0;
    reg_out_d_o.paddr           = '0;
    reg_out_d_o.data            = '0;
    reg_out_d_o.line            = '0;
    reg_out_d_o.lsq_addr        = '0;
    reg_out_d_o.store_width     = DW;
    reg_out_d_o.wbb_tag         = '0;
    dcache_addr_o               = '0;
    dcache_wdata_o              = '0;
    dcache_wtvd_o.tag           = '0;
    dcache_wtvd_o.valid         = 1'b0;
    dcache_wtvd_o.dirty         = 1'b0;
    // The actual d0 request routes the data flow
    unique case (d0_req_type_i)
      // If no request is present for d1, it is not sampled
      Idle: begin
        reg_out_d_o.valid       = 1'b1;
      end
      // Read by LSQ
      d0_ReadLsq: begin
        reg_out_d_o.valid       = 1'b1;
        reg_out_d_o.paddr       = lsq_l1dc_req_i.paddr;
        reg_out_d_o.data        = lsq_l1dc_req_i.data;
        reg_out_d_o.lsq_addr    = lsq_l1dc_req_i.lsq_addr;
        reg_out_d_o.store_width = lsq_l1dc_req_i.store_width;
        dcache_addr_o           = lsq_l1dc_req_i.paddr.idx;
      end
      // Read by d1
      d0_ReadD1: begin
        reg_out_d_o.valid       = 1'b1;
        reg_out_d_o.paddr       = d1_d0_req_i.paddr;
        reg_out_d_o.data        = d1_d0_req_i.data;
        reg_out_d_o.lsq_addr    = d1_d0_req_i.lsq_addr;
        reg_out_d_o.store_width = d1_d0_req_i.store_width;
        dcache_addr_o           = d1_d0_req_i.paddr.idx;
      end
      // Write line by d1 (enhancement: see if all reg data is necessary)
      d0_WriteCleanLineD1, d0_WriteDirtyLineD1: begin
        reg_out_d_o.valid       = 1'b1;
        reg_out_d_o.paddr       = d1_d0_req_i.paddr;
        reg_out_d_o.data        = d1_d0_req_i.data;
        reg_out_d_o.lsq_addr    = d1_d0_req_i.lsq_addr;
        reg_out_d_o.store_width = d1_d0_req_i.store_width;
        dcache_addr_o           = d1_d0_req_i.paddr.idx;
        dcache_wdata_o          = d1_d0_req_i.line;
        dcache_wtvd_o.tag       = d1_d0_req_i.paddr.tag;
        dcache_wtvd_o.valid     = 1'b1;
        dcache_wtvd_o.dirty     = (d0_req_type_i == d0_WriteDirtyLineD1) ? 1'b1 : 1'b0;
      end
      // Write DW, W, HW, B by d1 (enhancement: see if all reg data is necessary)
      d0_WriteStoreD1: begin
        reg_out_d_o.valid       = 1'b1;
        reg_out_d_o.paddr       = d1_d0_req_i.paddr;
        reg_out_d_o.data        = d1_d0_req_i.data;
        reg_out_d_o.lsq_addr    = d1_d0_req_i.lsq_addr;
        reg_out_d_o.store_width = d1_d0_req_i.store_width;
        dcache_addr_o           = d1_d0_req_i.paddr.idx;
        case (d1_d0_req_i.store_width)
          B:  dcache_wdata_o    = line_adapted_b;
          HW: dcache_wdata_o    = line_adapted_hw;
          W:  dcache_wdata_o    = line_adapted_w;
          DW: dcache_wdata_o    = line_adapted_dw;
        endcase
        dcache_wtvd_o.tag       = d1_d0_req_i.paddr.tag;
        dcache_wtvd_o.valid     = 1'b1;
        dcache_wtvd_o.dirty     = 1'b1;
      end
      // Read the line to be replaced
      d0_ReadL2: begin
        reg_out_d_o.valid       = 1'b1;
        reg_out_d_o.paddr       = {zero_tag, l2c_l1dc_ans_i.line_addr, zero_wb};
        reg_out_d_o.line        = l2c_l1dc_ans_i.line;
        reg_out_d_o.wbb_tag     = l2c_l1dc_ans_i.wbb_tag;
        dcache_addr_o           = l2c_l1dc_ans_i.line_addr;
      end
      // Give the WB buffer previous L2 store address (which hit)
      d0_FwdL2StAddr: begin
        reg_out_d_o.valid       = 1'b1;
        reg_out_d_o.paddr       = l2c_l1dc_ans_i.line_addr;
        reg_out_d_o.wbb_tag     = l2c_l1dc_ans_i.wbb_tag;
      end
      // Read the next set to update L2
      d0_ReadUpdate: begin
        reg_out_d_o.valid       = 1'b1;
        reg_out_d_o.paddr       = {zero_tag, upd_l1dc_req_i.idx, zero_wb};
        dcache_addr_o           = upd_l1dc_req_i.idx;
      end
      // Clean a line
      d0_CleanDirty: begin
        reg_out_d_o.valid       = 1'b1;
        dcache_addr_o           = upd_l1dc_req_i.idx;
        dcache_wtvd_o.tag       = d1_d0_req_i.paddr.tag; // this tag is the read one
        dcache_wtvd_o.valid     = 1'b1;
        dcache_wtvd_o.dirty     = 1'b0;
      end
      // Invalid all the lines into the set
      d0_ResetLines: begin
        reg_out_d_o.valid       = 1'b1;
        dcache_addr_o           = rst_l1dc_req_i.dcache_addr;
      end
      // Request NOT valid
      default: begin
        reg_out_d_o.valid       = 1'b0;
        // Default masking
        reg_out_d_o.paddr       = '0;
        reg_out_d_o.data        = '0;
        reg_out_d_o.line        = '0;
        reg_out_d_o.lsq_addr    = '0;
        reg_out_d_o.store_width = DW;
        reg_out_d_o.wbb_tag     = '0;
        dcache_addr_o           = '0;
        dcache_wdata_o          = '0;
        dcache_wtvd_o.tag       = '0;
        dcache_wtvd_o.valid     = 1'b0;
        dcache_wtvd_o.dirty     = 1'b0;
      end
    endcase
  end

endmodule
