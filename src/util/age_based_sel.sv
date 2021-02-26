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
// File: age_based_sel.sv
// Author: Michele Caon
// Date: 31/10/2019

module age_based_sel #(N = 8, AGE_LEN = 4)
(
    input logic [N-1:0] lines_i,
    input logic [AGE_LEN-1:0] ages_i [0:N-1],
    //output logic [$clog2(N)-1:0] enc_o,
output logic [3-1:0] enc_o,
    output logic                 valid_o
);
    
    //------------------------------\\
    //----- EXECUTION SELECTOR -----\\
    //------------------------------\\
    // The selector follows a "first come first served" scheduling policy. The oldest entry whose request is valid is selected.
    logic [AGE_LEN-1:0] oldest_age;
    always_comb begin: ex_selector
        oldest_age  = 0;
        enc_o       = 0; // Default if none is selected
        for (int i = 0; i < N; i++) begin
            if (lines_i[i] && (ages_i[i] >= oldest_age[AGE_LEN-1:0])) begin // >= handles initial case where alla ages are 0
                //enc_o   = i[$clog2(N)-1:0];
		enc_o   = i[3-1:0];
                oldest_age[AGE_LEN-1:0] = ages_i[i];
            end 
        end
        valid_o = |lines_i;
    end
    
endmodule
