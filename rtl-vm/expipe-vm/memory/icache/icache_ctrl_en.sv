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
// File: icache_ctrl_en.sv
// Author: Matteo Perotti
// Date: 29/10/2019
// Description: enable the memory control and the registers updating. It also controls the handshake
//              combinatorial signals


import len5_pkg::*;
import memory_pkg::*;

module icache_ctrl_en (
    // From the CU
    input icache_ctrl_e icache_cond_ctrl_i,
    input logic comparing_i,
    input logic replaying_i,
    input logic waiting_tlb_i,
    input logic waiting_l2c_i,
    // From the comparison block and the i-TLB
    input logic cache_hit_i,
    input logic itlb_hit_i,
    input exception_e itlb_exception_i,
    input logic itlb_rdy_i,
    // From the L2C
    input logic l2c_req_rdy_i,
    input logic l2c_ans_valid_i,
    // From the Front-End
    input logic fend_icache_valid_i,
    // To the Memory Control block
    output logic icache_cond_ctrl_en_o,  // It validates the scheduled physical cache request
    // To the Front-End
    output logic icache_fend_req_rdy_o,
    output logic icache_fend_ans_valid_o,
    // To the replacement block
    output logic update_replacement_o,
    // To the vaddr register
    output logic vaddr_reg_en_o,
    // To the Tag register
    output logic tag_reg_en_o
);

  // Mealy output of the CU explicited in the Data Path
  always_comb begin
    icache_cond_ctrl_en_o   = 1'b0;
    icache_fend_req_rdy_o   = 1'b0;
    icache_fend_ans_valid_o = 1'b0;
    update_replacement_o    = 1'b0;
    vaddr_reg_en_o          = 1'b0;
    tag_reg_en_o            = 1'b0;
    case (icache_cond_ctrl_i)
      ReadSet: begin
        if (comparing_i) begin
          if (itlb_rdy_i && (itlb_hit_i || itlb_exception_i)) begin
            if (itlb_exception_i || (!itlb_exception_i && cache_hit_i)) begin
              icache_fend_req_rdy_o   = 1'b1;
              icache_fend_ans_valid_o = 1'b1;
              if (fend_icache_valid_i) begin
                icache_cond_ctrl_en_o = 1'b1;
                vaddr_reg_en_o        = 1'b1;
              end
            end else if (!itlb_exception_i && !cache_hit_i) begin
              update_replacement_o = 1'b1;
              tag_reg_en_o         = 1'b1;
            end
          end
          // Replay the instruction without conditions
        end else if (replaying_i) begin
          icache_cond_ctrl_en_o = 1'b1;
          // Waiting for TLB
        end else if (waiting_tlb_i) begin
          if (itlb_rdy_i) icache_cond_ctrl_en_o = 1'b1;
          // Waiting for L2C
        end else if (waiting_l2c_i) begin
          icache_cond_ctrl_en_o = 1'b1;
          // Ready state
        end else begin
          icache_fend_req_rdy_o = 1'b1;
          if (fend_icache_valid_i) begin
            icache_cond_ctrl_en_o = 1'b1;
            vaddr_reg_en_o        = 1'b1;
          end
        end
      end
      WriteLineAndTag: begin
        if (l2c_ans_valid_i) icache_cond_ctrl_en_o = 1'b1;
      end
      InvalidSet: begin
        icache_cond_ctrl_en_o = 1'b1;
      end
    endcase
  end

endmodule
