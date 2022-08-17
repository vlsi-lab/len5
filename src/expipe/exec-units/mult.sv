// Copyright 2021 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: mult.sv
// Author: Michele Caon
// Date: 10/11/2021

import len5_pkg::*;
import expipe_pkg::*;

module mult 
#(
    parameter RS_DEPTH      = 4,    // must be a power of 2,
    parameter PIPE_DEPTH    = 4,    // number of pipeline levels (>0)
    
    // EU-specific parameters
    parameter EU_CTL_LEN    = 4
)
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,

    // Handshake from/to the reservation station unit
    input   logic                   valid_i,
    input   logic                   ready_i,
    output  logic                   valid_o,
    output  logic                   ready_o,

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

    // MULT output
    logic [XLEN-1:0]        result;
    logic [(XLEN<<1)-1:0]   result_full;
    logic                   except_raised;

    // Cached result and operands
    logic                   cached_data_en;
    logic [XLEN-1:0]        cached_result_low;
    logic [XLEN-1:0]        cached_rs1_value;
    logic [XLEN-1:0]        cached_rs2_value;

    // Pipeline registers
    logic [XLEN-1:0]        pipe_result_d [PIPE_DEPTH-1:0];
    logic [$clog2(RS_DEPTH)-1:0] pipe_entry_idx_d [PIPE_DEPTH-1:0];
    logic                   pipe_except_raised_d [PIPE_DEPTH-1:0];

    // ---------------
    // MULT OPERATIONS
    // ---------------
    // NOTE: when a MULH[S[U]] is detected, the multipliers performs computes
    // the full product on 2*XLEN bits and cache the lower XLEN bits of the
    // result and the value of the source operands. If the next instruction is
    // a MUL on the same operand values, the lower part of the result is taken
    // from the cached result.

    always_comb begin : mult_ops
        // Default values
        result              = '0;
        result_full         = '0;
        except_raised       = 1'b0;

        unique case (ctl_i)
            MULT_MUL: begin
                if (rs1_value_i == cached_rs1_value && rs2_value_i == cached_rs2_value) begin
                    result          = cached_result_low;
                end else begin
                    result_full     = signed'(rs1_value_i) * signed'(rs2_value_i);
                    result          = result_full[XLEN-1:0];
                end
            end
            MULT_MULW: begin
                result_full         = rs1_value_i[(XLEN>>1)-1:0] * rs2_value_i[(XLEN>>1)-1:0];
                result              = signed'(result_full[(XLEN>>1)-1:0]);
            end
            MULT_MULH: begin
                result_full         = signed'(rs1_value_i) * signed'(rs2_value_i);
                result              = result_full[(XLEN<<1)-1:XLEN];
                cached_data_en      = valid_i && ready_o && !flush_i;
            end
            MULT_MULHU: begin
                result_full         = rs1_value_i * rs2_value_i;
                result              = result_full[(XLEN<<1)-1:XLEN];
                cached_data_en      = valid_i && ready_o && !flush_i;
            end
            MULT_MULHSU: begin
                result_full         = signed'(rs1_value_i) * rs2_value_i;
                result              = result_full[(XLEN<<1)-1:XLEN];
                cached_data_en      = valid_i && ready_o && !flush_i;
            end
            default: except_raised  = 1'b1;
        endcase
    end

    // Cached rs1, rs2 and lower result register
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : cached_rs1_reg
        if (!rst_n_i) begin
            cached_rs1_value    <= '0;
            cached_rs2_value    <= '0;
            cached_result_low   <= '0;
        end else if (cached_data_en) begin
            cached_rs1_value    <= rs1_value_i;
            cached_rs2_value    <= rs2_value_i;
            cached_result_low   <= result_full[XLEN-1:0];
        end
    end

    // ------------------
    // PIPELINE REGISTERS
    // ------------------

    assign  pipe_result_d[0]        = result;
    assign  pipe_entry_idx_d[0]     = entry_idx_i;
    assign  pipe_except_raised_d[0] = except_raised;

    // Generate PIPE_DEPTH-1 pipeline registers
    generate
        for (genvar i=1; i<PIPE_DEPTH; i=i+1) begin: pipe_reg
            always_ff @( posedge clk_i or negedge rst_n_i ) begin
                if (!rst_n_i) begin
                    pipe_result_d[i]        <= '0;
                    pipe_entry_idx_d[i]     <= '0;
                    pipe_except_raised_d[i] <= 1'b0;
                end else begin
                    pipe_result_d[i]        <= pipe_result_d[i-1];
                    pipe_entry_idx_d[i]     <= pipe_entry_idx_d[i-1];
                    pipe_except_raised_d[i] <= pipe_except_raised_d[i-1];
                end
            end
        end
    endgenerate

    // ---------------
    // OUTPUT REGISTER
    // ---------------
    // NOTE: use a spill cell to break the handshaking path

    // Interface data type
    typedef struct packed {
        logic [XLEN-1:0]        res;            // the ALU result
        logic [$clog2(RS_DEPTH)-1:0] entry_idx; // instr. index in the RS
        logic                   except_raised;  // exception flag
    } out_reg_data_t;

    out_reg_data_t  out_reg_data_in, out_reg_data_out;

    // Input data
    assign  out_reg_data_in.res             = pipe_result_d[PIPE_DEPTH-1];
    assign  out_reg_data_in.entry_idx       = pipe_entry_idx_d[PIPE_DEPTH-1];
    assign  out_reg_data_in.except_raised   = pipe_except_raised_d[PIPE_DEPTH-1];

    // Output data
    assign  result_o                        = out_reg_data_out.res;
    assign  entry_idx_o                     = out_reg_data_out.entry_idx;
    assign  except_raised_o                 = out_reg_data_out.except_raised;

    // Output register
    spill_cell_flush #(.DATA_T(out_reg_data_t), .SKIP(1'b0)) u_out_reg (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .flush_i        (flush_i),
        .valid_i        (valid_i),
        .ready_i        (ready_i),
        .valid_o        (valid_o),
        .ready_o        (ready_o),
        .data_i         (out_reg_data_in),
        .data_o         (out_reg_data_out)
    );

    // Exception handling
    // ------------------
    assign  except_code_o       = E_ILLEGAL_INSTRUCTION;

endmodule
