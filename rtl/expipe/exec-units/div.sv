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

module div #(
  parameter int unsigned PIPE_DEPTH = 4,  // number of pipeline levels (>0)

  // EU-specific parameters
  parameter int unsigned EU_CTL_LEN = 4
) (
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i,

  // Handshake from/to the reservation station unit
  input  logic valid_i,
  input  logic ready_i,
  output logic valid_o,
  output logic ready_o,

  // Data from/to the reservation station unit
  input  logic                   [    EU_CTL_LEN-1:0] ctl_i,
  input  expipe_pkg::rob_idx_t                        rob_idx_i,
  input  logic                   [len5_pkg::XLEN-1:0] rs1_value_i,
  input  logic                   [len5_pkg::XLEN-1:0] rs2_value_i,
  output expipe_pkg::rob_idx_t                        rob_idx_o,
  output logic                   [len5_pkg::XLEN-1:0] result_o,
  output logic                                        except_raised_o,
  output len5_pkg::except_code_t                      except_code_o
);

  import len5_pkg::*;
  import expipe_pkg::*;

  // MULT output
  logic     [XLEN-1:0] result;
  logic                except_raised;

  // Pipeline registers
  logic     [XLEN-1:0] pipe_result_d       [PIPE_DEPTH];
  rob_idx_t            pipe_rob_idx_d      [PIPE_DEPTH];
  logic                pipe_except_raised_d[PIPE_DEPTH];

  // --------------
  // DIV OPERATIONS
  // --------------
  // TODO: add proper operations support
  always_comb begin : div_ops
    // Default values
    result        = '0;
    except_raised = 1'b0;

    unique case (ctl_i)
      DIV_DIV: begin
        if (rs2_value_i != 0) result = rs1_value_i / rs2_value_i;
        else result = '0;
      end
      default: except_raised = 1'b1;
    endcase
  end

  // ------------------
  // PIPELINE REGISTERS
  // ------------------

  assign pipe_result_d[0]        = result;
  assign pipe_rob_idx_d[0]       = rob_idx_i;
  assign pipe_except_raised_d[0] = except_raised;

  // Generate PIPE_DEPTH-1 pipeline registers
  generate
    for (genvar i = 1; i < PIPE_DEPTH; i = i + 1) begin : gen_pipe_reg
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          pipe_result_d[i]        <= '0;
          pipe_rob_idx_d[i]       <= '0;
          pipe_except_raised_d[i] <= 1'b0;
        end else begin
          pipe_result_d[i]        <= pipe_result_d[i-1];
          pipe_rob_idx_d[i]       <= pipe_rob_idx_d[i-1];
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
    logic [XLEN-1:0] res;            // the ALU result
    rob_idx_t        rob_idx;        // instr. index in the RS
    logic            except_raised;  // exception flag
  } out_reg_data_t;
  out_reg_data_t out_reg_data_in, out_reg_data_out;

  // Input data
  assign out_reg_data_in.res           = pipe_result_d[PIPE_DEPTH-1];
  assign out_reg_data_in.rob_idx       = pipe_rob_idx_d[PIPE_DEPTH-1];
  assign out_reg_data_in.except_raised = pipe_except_raised_d[PIPE_DEPTH-1];

  // Output data
  assign result_o                      = out_reg_data_out.res;
  assign rob_idx_o                     = out_reg_data_out.rob_idx;
  assign except_raised_o               = out_reg_data_out.except_raised;

  // Output register
  spill_cell_flush #(
    .DATA_T(out_reg_data_t),
    .SKIP  (1'b0)
  ) u_out_reg (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .flush_i(flush_i),
    .valid_i(valid_i),
    .ready_i(ready_i),
    .valid_o(valid_o),
    .ready_o(ready_o),
    .data_i (out_reg_data_in),
    .data_o (out_reg_data_out)
  );

  // Exception handling
  // ------------------
  assign except_code_o = E_ILLEGAL_INSTRUCTION;

endmodule
