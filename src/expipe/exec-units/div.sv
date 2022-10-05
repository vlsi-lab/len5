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
// File: div.sv
// Author: Michele Caon
// Date: 21/10/2019

import len5_pkg::XLEN;
import len5_pkg::ILEN;
import len5_pkg::*;
import expipe_pkg::*;

module div 
#(
    RS_DEPTH = 4, // must be a power of 2,
    
    // EU-specific parameters
    EU_CTL_LEN = 4,
    PIPE_DEPTH = 4
)
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,

    // Handshake from/to the reservation station unit
    input   logic                   valid_i,
    input   logic                   ready_i,
    output  logic                   ready_o,
    output  logic                   valid_o,

    // Data from/to the reservation station unit
    input   logic [EU_CTL_LEN-1:0]  ctl_i,
    input   logic [$clog2(RS_DEPTH)-1:0] entry_idx_i,
    input   logic [XLEN-1:0]        rs1_value_i,
    input   logic [XLEN-1:0]        rs2_value_i,
    output  logic [$clog2(RS_DEPTH)-1:0] entry_idx_o,
    output  logic [XLEN-1:0]        result_o,
    output  logic                   except_raised_o,
    output  except_code_t           except_code_o
);
    // INTERNAL SIGNALS
    // ----------------

    // Pipeline registers
    logic [XLEN-1:0]    pipe_res[0:PIPE_DEPTH];
    logic               pipe_valid[0:PIPE_DEPTH];

    // Output spill cell
    logic               out_reg_div_ready;

    // Divider
    // -------
    // TODO: add proper control
    assign  pipe_res[0] = (rs2_value_i != 'd0)  ? rs1_value_i / rs2_value_i : 'h0;

    // Pipeline registers
    // ------------------
    generate
        for (genvar i = 1; i <= PIPE_DEPTH; i++) begin: l_pipe_reg
            always_ff @( posedge clk_i or negedge rst_n_i ) begin
                if (!rst_n_i) begin
                    pipe_res[i]     <= '0;
                    pipe_valid[i]   <= 1'b0;
                end else if (flush_i) begin
                    pipe_res[i]     <= '0;
                    pipe_valid[i]   <= 1'b0;
                end else if (out_reg_div_ready) begin
                    pipe_res[i]     <= pipe_res[i-1];
                    pipe_valid[i]   <= pipe_valid[i-1];
                end
            end
        end
    endgenerate

    // Output spill cell
    // -----------------
    spill_cell_flush #(
        .DATA_T (logic[XLEN-1:0] ),
        .SKIP   (1'b0            )
    ) u_out_reg (
    	.clk_i   (clk_i                  ),
        .rst_n_i (rst_n_i                ),
        .flush_i (flush_i                ),
        .valid_i (pipe_valid[PIPE_DEPTH] ),
        .ready_i (ready_i                ),
        .valid_o (valid_o                ),
        .ready_o (out_reg_div_ready      ),
        .data_i  (pipe_res[PIPE_DEPTH]   ),
        .data_o  (result_o               )
    );
    
    // Output evaluation
    // -----------------
    assign  ready_o = out_reg_div_ready;

endmodule
