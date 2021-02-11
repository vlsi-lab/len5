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
// File: dtlb_replacement_block.sv
// Author: Matteo Perotti
// Date: 31/10/2019
// Description: d-TLB PLRU replacement block
// Details: tree PLRU implemented with decoders and D-FF. If a TLB entry is not valid, fill it first.
//          Update the tree when the TLB is accessed *

`include "memory_pkg.sv"
import memory_pkg::*;

module dtlb_replacement_block
#(
  N = D_TLB_ENTRIES
)
(
  // Main
  input logic          clk_i,
  input logic          rst_ni,
  // Update signal for the PLRU
  input logic  [N-1:0] tlb_valid_vec_i,
  input logic          valid_tlb_read_i,
  input logic          valid_tlb_replacement_i,
  input logic  [N-1:0] hit_vec_i,
  // The output replacement vector
  output logic [N-1:0] replace_vec_o
);

  localparam LOG2_N = $clog2(N);

  // D-FF enable
  logic ff_en_0;
  logic ff_en_1 [2];
  logic ff_en_2 [4];
  // D-FF
  logic d_0, q_0;
  logic d_1 [2], q_1 [2];
  logic d_2 [4], q_2 [4];
  // Decoder enable
  logic dec_en_0;
  logic dec_en_1 [2];
  logic dec_en_2 [4];

  // Two types replacement strategy: PLRU and Invalid First
  logic [N-1:0] plru_replace_vec;
  logic [N-1:0] invalid_first_replace_vec;

  // Invalid First strategy auxiliary vectors
  logic [LOG2_N-1:0] first_invalid_idx;

  // Replacement vector
  logic [N-1:0] replace_vec;

  // Access Vector -> it can be the hit vector or the replacement vector
  logic [N-1:0] access_vector;

  // Either a read or a replacement
  logic valid_tlb_access;

  always_comb begin
    access_vector = '0;
    if      ( valid_tlb_read_i && !valid_tlb_replacement_i) access_vector = hit_vec_i;
    else if (!valid_tlb_read_i &&  valid_tlb_replacement_i) access_vector = replace_vec;
  end

  assign valid_tlb_access = (valid_tlb_read_i || valid_tlb_replacement_i) ? 1'b1 : 1'b0;

  //-------------------------------------------------------------------------------------------\\
  //------------------------------ REPLACEMENT VECTOR DEFINITION ------------------------------\\
  //-------------------------------------------------------------------------------------------\\

  //-------------\\
  // FIRST LEVEL \\
  //-------------\\

  // Decoder (works as a "Demultiplexer")
  assign dec_en_0 = 1'b1;

  // D-FF
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      q_0 <= 1'b0;
    end else if (ff_en_0) begin
      q_0 <= d_0;
    end
  end

  //--------------\\
  // SECOND LEVEL \\
  //--------------\\

  // Decoders (works as a "Demultiplexer")
  assign dec_en_1[0] = (dec_en_0) ? ~q_0 : 1'b0;
  assign dec_en_1[1] = (dec_en_0) ?  q_0 : 1'b0;

  // D-FFs
  for (genvar k = 0; k < 2; k++) begin : dff_level_1
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        q_1[k] <= 1'b0;
      end else if (ff_en_1[k]) begin
        q_1[k] <= d_1[k];
      end
    end
  end

  //-------------\\
  // THIRD LEVEL \\
  //-------------\\

  // Decoders (works as a "Demultiplexer")
  for (genvar k = 0; k < 2; k++) begin
    assign dec_en_2[2*k]   = (dec_en_1[k]) ? ~q_1[k] : 1'b0;
    assign dec_en_2[2*k+1] = (dec_en_1[k]) ?  q_1[k] : 1'b0;
  end

  // D-FFs
  for (genvar k = 0; k < 4; k++) begin : dff_level_2
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        q_2[k] <= 1'b0;
      end else if (ff_en_2[k]) begin
        q_2[k] <= d_2[k];
      end
    end
  end

  //--------------------\\
  // REPLACEMENT VECTOR \\
  //--------------------\\

  // Decoders (works as a "Demultiplexer")
  for (genvar k = 0; k < 4; k++) begin
    assign plru_replace_vec[2*k]   = (dec_en_2[k]) ? ~q_2[k] : 1'b0;
    assign plru_replace_vec[2*k+1] = (dec_en_2[k]) ?  q_2[k] : 1'b0;
  end

  //----------------------------------------------------------------------------------------------\\
  //----------------------------------- UPDATING DEFINITION ** -----------------------------------\\
  //----------------------------------------------------------------------------------------------\\

  //-------------\\
  // THIRD LEVEL \\
  //-------------\\

  // Third level D-FF enables
  for (genvar k = 0; k < 4; k++) begin
    assign ff_en_2[k] = ((access_vector[2*k] | access_vector[2*k+1]) & valid_tlb_access);
  end

  // Third level D-FF d definition
  for (genvar k = 0; k < 4; k++) begin
    // The FF is enabled only if one of {access_vector[2*k], access_vector[2*k+1]} is 1'b1. At least one of the two is zero.
    assign d_2[k] = access_vector[2*k];
  end

  //--------------\\
  // SECOND LEVEL \\
  //--------------\\

  // Second level D-FF enables
  for (genvar k = 0; k < 2; k++) begin
    assign ff_en_1[k] = (ff_en_2[2*k] | ff_en_2[2*k+1]) & valid_tlb_access;
  end

  // Second level D-FF d definition
  for (genvar k = 0; k < 2; k++) begin
    // The FF is enabled only if one of {ff_en_2[2*k], ff_en_2[2*k+1]} is 1'b1. At least one of the two is zero.
    assign d_1[k] = ff_en_2[2*k];
  end

  //-------------\\
  // FIRST LEVEL \\
  //-------------\\

  // First level T-FF enable
  assign ff_en_0 = (ff_en_1[0] | ff_en_1[1]) & valid_tlb_access;
  // The FF is enabled only if one of {ff_en_1[0], ff_en_1[1]} is 1'b1. At least one of the two is zero.
  assign d_0 = ff_en_1[0];

  //-------------------------------------------------------------------------------------------\\
  //------------------------------ D-TLB INVALID ENTRIES FILLING ------------------------------\\
  //-------------------------------------------------------------------------------------------\\

  // First invalid index creation
  always_comb begin
    first_invalid_idx = '0;
    for (int k = N-1; k >= 0; k--) begin
      if (!tlb_valid_vec_i[k]) first_invalid_idx = k;
    end
  end

  // One Hot First Invalid replacement vector creation
  always_comb begin
    invalid_first_replace_vec = '0;
    for (int k = 0; k < N; k++) begin
      invalid_first_replace_vec[k] = (first_invalid_idx == k) ? 1'b1 : 1'b0;
    end
  end

  //-------------------------------------------------------------------------------------------\\
  //-------------------------------- REPLACEMENT VECTOR CHOICE --------------------------------\\
  //-------------------------------------------------------------------------------------------\\

  // If all the d-TLB entries are valid, use PLRU policy
  assign replace_vec = (&tlb_valid_vec_i) ? plru_replace_vec : invalid_first_replace_vec ;

  // Output assignment
  assign replace_vec_o = replace_vec;

endmodule

// *  The tree is updated if the TLB is accessed by the LSQ and if the TLB is updated by L2.
//    In the first case, select the entry with the hit vec. In the second case, use the replacement
//    vector.
// ** The replacement vector packed, the various structures of this block are unpacked. Therefore,
//    in the updating process it's "assign d_2[k] = access_vector[2*k];" and not
//    "assign d_2[k] = access_vector[2*k+1];". The arrows are "reversed".
