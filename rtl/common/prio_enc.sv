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
// File: prio_enc.sv
// Author: Michele Caon
// Date: 22/10/2019

// NOTE: Synopsys should be able to synthesize a performance-optimised priority encoder from simple behavioural code

module prio_enc #(
    parameter N = 8
) (
    input  logic                 lines_i[N],
    output logic [$clog2(N)-1:0] enc_o,
    output logic                 valid_o
);
  generate
    // If there's only one input, the index is always 0
    if (N == 1) begin : l_prio_enc_gen
      assign valid_o = lines_i[0];
      assign enc_o   = 0;
    end else begin : l_prio_enc_gen
      // The priority decreases with the input index: lines_i[0] has the highest priority and lines_i[N] the lowest
      always_comb begin : prio_enc_logic
        enc_o   = 0;
        valid_o = 1'b0;

        for (int i = N - 1; i >= 0; i = i - 1) begin
          if (lines_i[i]) begin
            enc_o   = i[$clog2(N)-1:0];
            valid_o = 1'b1;
          end
        end
      end
    end
  endgenerate
endmodule
