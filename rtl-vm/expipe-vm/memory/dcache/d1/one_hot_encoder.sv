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
// File: one_hot_encoder.sv
// Author: Matteo Perotti
// Date: 27/10/2019
// Description: One Hot encoder without priority

import memory_pkg::*;

module one_hot_encoder #(
    D = 16,  // Input parallelism (decoded)
    E = 4    // Output parallelism (encoded)
) (
    // Multi-hot decoded input
    input  logic [D-1:0] mh_decoded_i,
    // One-hot encoded output
    output logic [E-1:0] oh_encoded_o
);

  // The priority is not needed, maybe is only a loss of area and energy
  always_comb begin
    oh_encoded_o = '0;
    for (int k = D - 1; k >= 0; k--) begin
      if (mh_decoded_i[k]) oh_encoded_o = k;
    end
  end

endmodule
