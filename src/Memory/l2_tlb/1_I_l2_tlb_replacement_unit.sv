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
// File: L2_tlb_replacement_unit.sv
// Author: Matteo Perotti
// Date: 05/11/2019
// Description: replacement unit for the L2 TLB
// Details: PLRU with invalid first

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/memory_pkg.sv"
import memory_pkg::*;

module L2_tlb_replacement_unit
#(
  parameter A      = L2_TLB_IDX_LEN,
  parameter N_WAY  = L2_TLB_ASSOCIATIVITY,
  parameter N_SETS = L2_TLB_N_SETS
)
(
  // Main
  input  logic             clk_i,
  input  logic             rst_ni,
  // Index
  input  logic [A-1:0]     index_i,
  // Valid access and hit vector
  input  logic [N_WAY-1:0] hit_vec_i,
  input  logic             valid_tlb_access_i,   // Use the hit_vector to update the replacement vector of the set
  input  logic             replacing_an_entry_i, // Use the replacement_vector to update the replacement vector of the set
  // Valid vector to fill not-valid first
  input  logic [N_WAY-1:0] valid_vec_i,
  // Replacement vector
  output logic [N_WAY-1:0] replace_vec_o
);

  // One hot vector to indicate the element which has just been accessed in the L2 TLB
  logic [N_WAY-1:0] access_vector;
  // Choose the replacement vector to use
  logic             all_valid;
  // Two different replacement vectors
  logic [N_WAY-1:0] plru_replace_vec [N_SETS];
  logic [N_WAY-1:0] invalid_first_replace_vec;

  //------\\
  // PLRU \\
  //------\\

  localparam LOG2_N_WAY = $clog2(N_WAY);

  // D-FF enable
  logic ff_en_0 [N_SETS];
  logic ff_en_1 [N_SETS][2];
  // D-FF
  logic d_0 [N_SETS]   , q_0 [N_SETS];
  logic d_1 [N_SETS][2], q_1 [N_SETS][2];
  // Decoder enable
  logic dec_en_0 [N_SETS];
  logic dec_en_1 [N_SETS][2];

  // Invalid First strategy auxiliary vector
  logic [LOG2_N_WAY-1:0] first_invalid_idx;

  // PLRU should be updated when an access is computed. The element of the set which was accessed
  // is indicated either by the hit vector if a read access is done or by the replace vector if
  // a replacement takes place.
  always_comb begin
    access_vector = '0;
    if (valid_tlb_access_i) begin
      access_vector = hit_vec_i;
    end else if (replacing_an_entry_i) begin
      access_vector = replace_vec_o;
    end
  end

  // PLRU for each set
  for (genvar z = 0; z < N_SETS; z++) begin

    //-------------------------------------------------------------------------------------------\\
    //------------------------------ REPLACEMENT VECTOR DEFINITION ------------------------------\\
    //-------------------------------------------------------------------------------------------\\

    //-------------\\
    // FIRST LEVEL \\
    //-------------\\

    // Decoder (works as a "Demultiplexer")
    assign dec_en_0[z] = 1'b1;

    // D-FF
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        q_0[z] <= 1'b0;
      end else if (ff_en_0[z]) begin
        q_0[z] <= d_0[z];
      end
    end

    //--------------\\
    // SECOND LEVEL \\
    //--------------\\

    // Decoders (works as a "Demultiplexer")
    assign dec_en_1[z][0] = (dec_en_0[z]) ? ~q_0[z] : 1'b0;
    assign dec_en_1[z][1] = (dec_en_0[z]) ?  q_0[z] : 1'b0;

    // D-FFs
    for (genvar k = 0; k < 2; k++) begin : dff_level_1
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          q_1[z][k] <= 1'b0;
        end else if (ff_en_1[k][0]) begin
          q_1[z][k] <= d_1[z][k];
        end
      end
    end

    //--------------------\\
    // REPLACEMENT VECTOR \\
    //--------------------\\

    // Decoders (works as a "Demultiplexer")
    for (genvar k = 0; k < 2; k++) begin
      assign plru_replace_vec[z][2*k]   = (dec_en_1[z][k]) ? ~q_1[z][k] : 1'b0;
      assign plru_replace_vec[z][2*k+1] = (dec_en_1[z][k]) ?  q_1[z][k] : 1'b0;
    end

  end

  //-------------------------------------------------------------------------------------------\\
  //----------------------------------- UPDATING DEFINITION -----------------------------------\\
  //-------------------------------------------------------------------------------------------\\

  //--------------\\
  // SECOND LEVEL \\
  //--------------\\

  // Second level D-FF enables
  always_comb begin
    for (int k = 0; k < 2; k++) begin
      for (int z = 0; z < N_SETS; z++) begin
        ff_en_1[z][k] = 1'b0;
      end
      // The FF is enabled only if one of {ff_en_2[2*k], ff_en_2[2*k+1]} is 1'b1. At least one of the two is zero.
      ff_en_1[index_i][k] = (access_vector[2*k] || access_vector[2*k+1]) && valid_tlb_access_i;
    end
  end

  // Second level D-FF d definition
  always_comb begin
    for (int k = 0; k < 2; k++) begin
      for (int z = 0; z < N_SETS; z++) begin
        d_1[z][k] = 1'b0;
      end
      // The FF is enabled only if one of {ff_en_2[2*k], ff_en_2[2*k+1]} is 1'b1. At least one of the two is zero.
      d_1[index_i][k] = access_vector[2*k];
    end
  end

  //-------------\\
  // FIRST LEVEL \\
  //-------------\\

  // First level T-FF enable
  always_comb begin
    for (int k = 0; k < N_SETS; k++) begin
      ff_en_0[k] = 1'b0;
    end
    ff_en_0[index_i] = (ff_en_1[index_i][0] || ff_en_1[index_i][1]) && valid_tlb_access_i;
  end
  // The FF is enabled only if one of {ff_en_1[0], ff_en_1[1]} is 1'b1. At least one of the two is zero.
  always_comb begin
    for (int k = 0; k < N_SETS; k++) begin
      d_0[k] = 1'b0;
    end
    d_0[index_i] = ff_en_1[index_i][0];
  end

  //---------------\\
  // INVALID FIRST \\
  //---------------\\

  // First invalid index creation
  always_comb begin
    first_invalid_idx = '0;
    for (int k = N_WAY-1; k >= 0; k--) begin
      if (!valid_vec_i[k]) first_invalid_idx = k;
    end
  end

  // One Hot First Invalid replacement vector creation
  always_comb begin
    invalid_first_replace_vec                    = '0;
    invalid_first_replace_vec[first_invalid_idx] = 1'b1;
  end

  //------------------------------\\
  // REPLACEMENT VECTOR SELECTION \\
  //------------------------------\\

  // If all valid in the set, use PLRU
  assign all_valid = &valid_vec_i;
  // The final replacement vector
  assign replace_vec_o = (all_valid) ? plru_replace_vec[index_i] : invalid_first_replace_vec;

endmodule
