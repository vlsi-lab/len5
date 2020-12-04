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
// File: fair_2way_arbiter.sv
// Author: Michele Caon
// Date: 29/10/2019

module fair_2way_arbiter
(
    input logic clk_i,
    input logic rst_n_i,

    // Input valid signals
    input logic [1:0] valid_i,

    // Input ready signal
    input logic ready_i,

    // Output valid signal
    output logic valid_o,

    // Output ready signals
    output logic [1:0] ready_o,

    // Selector (usually connected to a mux)
    output logic select_o
);
    // DEFINITIONS
    logic last_served;

    //----------------------------\\
    //----- READY GENERATION -----\\
    //----------------------------\\
    // - No ready signal is asserted if the input ready signal is not
    // - If only one of the inputs is valid, that request is accepted
    // - If both requests are valid (conflict), the one that wasn't served on last conflict is served
    always_comb begin: ready_gen
        if (ready_i) begin
            case(valid_i)
                2'b00: ready_o = 2'b11; // valid_i[0] = 0, valid_i[1] = 0
                2'b01: ready_o = 2'b01; // valid_i[0] = 1, valid_i[1] = 0
                2'b10: ready_o = 2'b10; // valid_i[0] = 1, valid_i[1] = 0
                2'b11: ready_o = (last_served) ? (2'b01) : (2'b10); // valid_i[0] = 1, valid_i[1] = 1

                default: ready_o = 2'b00; // default values
            endcase
        end else ready_o = 2'b00; // default values
        select_o = ready_o[1]; // 1 if valid[1] is served
        valid_o = |valid_i; // 1 if at least one input is valid
    end

    //-----------------------------------\\
    //----- LAST SERVED ON CONFLICT -----\\
    //-----------------------------------\\
    // This flip-flop stores the last input that was accepted during a conflict (both valid asserted). When a new conflict takes place, the other input is served instead.
    always @(posedge clk_i or negedge rst_n_i) begin: last_served_ff
        if (!rst_n_i) begin
            last_served <= 1'b0;
        end else if (valid_i == 2'b11 && ready_i) last_served <= ~last_served;
    end

endmodule