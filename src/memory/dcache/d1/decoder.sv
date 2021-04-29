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
// File: decoder.sv
// Author: Matteo Perotti
// Date: 22/10/2019
// Description: one hot decoder with enable

import memory_pkg::*;

module decoder
#(
  INPUT_LEN = 6
)
(
  input  logic                    en_i,
  input  logic [INPUT_LEN-1:0]    encoded_i,
  output logic [2**INPUT_LEN-1:0] decoded_o
);

// ----------------------------------- CHECK IF OK
//  always_comb begin
//    for (int k = 0; k < 2**INPUT_LEN; k++) begin
//      assign decoded_o[k] = (en_i) ? encoded_i == k : 1'b0;
//    end
//  end
// -----------------------------------------------

  always_comb begin
    if (en_i) begin
      for (int k = 0; k < 2**INPUT_LEN; k++) begin
        decoded_o[k] = (encoded_i == k) ? 1'b1 : 1'b0;
      end
    end else if (!en_i) decoded_o = '0;
  end

endmodule
