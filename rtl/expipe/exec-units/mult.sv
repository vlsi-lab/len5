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
// Author: Flavia Guella
// Date: 26/02/2024

module mult #(
  parameter int unsigned PIPE_DEPTH = 4,  // number of pipeline levels (>0)
  parameter bit SKIP_IN_REG = 1'b1,  // slip input register
  parameter bit SKIP_OUT_REG = 1'b1,  // skip output spillcell
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

  // MULT temporary inputs, on XLEN+1 bits to manage signed*signed, signed*unsigned, unsigned*unsigned
  logic [XLEN:0] mult_a, mult_b;
  logic     [          1:0] s;  // sign extension of the operands
  // MULT output
  logic     [     XLEN-1:0] result;
  logic     [(XLEN<<1)-1:0] result_full;
  logic                     except_raised;
  // Pipeline registers
  logic     [     XLEN-1:0] pipe_result_d                        [PIPE_DEPTH];
  rob_idx_t                 pipe_rob_idx_d                       [PIPE_DEPTH];
  logic                     pipe_except_raised_d                 [PIPE_DEPTH];
  logic                     pipe_valid_d                         [PIPE_DEPTH];
  // Ready signal from the spill cell
  logic                     ready_spill;

  // Input registers
  logic [XLEN-1:0] rs1_value_q, rs2_value_q;
  logic     [EU_CTL_LEN-1:0] ctl_q;
  rob_idx_t                  rob_idx_q;
  logic                      valid_q;  //, ready_q;


  //////////////////////////////
  // MULT operators selection //
  //////////////////////////////

  always_comb begin : mult_ops
    // Default values
    result        = '0;
    s[1:0]        = 2'b00;  //unsigned by default
    mult_a        = {s[0], rs1_value_q};
    mult_b        = {s[1], rs2_value_q};
    except_raised = 1'b0;

    unique case (ctl_q)
      MULT_MUL: begin
        s[0]   = rs1_value_q[XLEN-1];  // sign extension
        s[1]   = rs2_value_q[XLEN-1];
        mult_a = {s[0], rs1_value_q};
        mult_b = {s[1], rs2_value_q};
        result = result_full[XLEN-1:0];
      end
      MULT_MULW: begin
        s[0]   = rs1_value_q[(XLEN>>1)-1];  // sign extension of the halfword
        s[1]   = rs2_value_q[(XLEN>>1)-1];
        mult_a = {s[0], {(XLEN >> 1) {rs1_value_q[(XLEN>>1)-1]}}, rs1_value_q[(XLEN>>1)-1:0]};
        mult_b = {s[1], {(XLEN >> 1) {rs2_value_q[(XLEN>>1)-1]}}, rs2_value_q[(XLEN>>1)-1:0]};
        result = {{(XLEN >> 1) {result_full[(XLEN>>1)-1]}}, result_full[(XLEN>>1)-1:0]};
      end
      MULT_MULH: begin
        s[0]   = rs1_value_q[XLEN-1];  // sign extension
        s[1]   = rs2_value_q[XLEN-1];
        mult_a = {s[0], rs1_value_q};
        mult_b = {s[1], rs2_value_q};
        result = result_full[(XLEN<<1)-1:XLEN];
      end
      MULT_MULHU: begin
        mult_a = {s[0], rs1_value_q};  // unsigned
        mult_b = {s[1], rs2_value_q};
        result = result_full[(XLEN<<1)-1:XLEN];
      end
      MULT_MULHSU: begin
        s[0]   = rs1_value_q[XLEN-1];  // sign extension
        s[1]   = 1'b0;  // unsigned
        mult_a = {s[0], rs1_value_q};
        mult_b = {s[1], rs2_value_q};
        result = result_full[(XLEN<<1)-1:XLEN];
      end
      default: except_raised = 1'b1;
    endcase
  end


  ////////////////
  // Multiplier //
  ////////////////
  assign result_full = $signed(mult_a) * $signed(mult_b);

  /////////////////////
  // Input Registers //
  /////////////////////

  generate
    if (SKIP_IN_REG) begin : gen_in_reg
      assign rs1_value_q = rs1_value_i;
      assign rs2_value_q = rs2_value_i;
      assign ctl_q       = ctl_i;
      assign rob_idx_q   = rob_idx_i;
      assign valid_q     = valid_i;
    end else begin : gen_out_reg
      always_ff @(posedge clk_i or negedge rst_ni) begin : mult_input_reg
        if (!rst_ni) begin
          rs1_value_q <= '0;
          rs2_value_q <= '0;
          ctl_q       <= '0;
          rob_idx_q   <= '0;
          valid_q     <= '0;
          //ready_q     <= '0;
        end else if (flush_i) begin
          rs1_value_q <= '0;
          rs2_value_q <= '0;
          ctl_q       <= '0;
          rob_idx_q   <= '0;
          valid_q     <= '0;
          //ready_q     <= '0;
        end else begin
          rs1_value_q <= rs1_value_i;
          rs2_value_q <= rs2_value_i;
          ctl_q       <= ctl_i;
          rob_idx_q   <= rob_idx_i;
          valid_q     <= valid_i;
          //ready_q     <= ready_i;
        end
      end
    end
  endgenerate

  ////////////////////////
  // PIPELINE REGISTERS //
  ////////////////////////

  assign pipe_result_d[0]        = result;
  assign pipe_rob_idx_d[0]       = rob_idx_q;
  assign pipe_except_raised_d[0] = except_raised;

  // Generate PIPE_DEPTH-1 pipeline registers
  generate
    for (genvar i = 1; i < PIPE_DEPTH; i = i + 1) begin : gen_mult_pipe_reg
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          pipe_result_d[i]        <= '0;
          pipe_rob_idx_d[i]       <= '0;
          pipe_except_raised_d[i] <= 1'b0;
        end else if (flush_i) begin
          pipe_result_d[i]        <= '0;
          pipe_rob_idx_d[i]       <= '0;
          pipe_except_raised_d[i] <= 1'b0;
        end else if (pipe_valid_d[i-1] & ready_spill) begin
          pipe_result_d[i]        <= pipe_result_d[i-1];
          pipe_rob_idx_d[i]       <= pipe_rob_idx_d[i-1];
          pipe_except_raised_d[i] <= pipe_except_raised_d[i-1];
        end
      end
    end
  endgenerate

  ///////////////////////////////
  // Output handhsake register //
  ///////////////////////////////

  assign pipe_valid_d[0] = valid_q;
  // Generate PIPE_DEPTH-1 pipeline registers
  // Propagate the valid signal to be synchronized with the result
  generate
    for (genvar i = 1; i < PIPE_DEPTH; i = i + 1) begin : gen_mult_hs_pipe_reg
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          pipe_valid_d[i] <= '0;
        end else if (flush_i) begin
          pipe_valid_d[i] <= '0;
        end else if (ready_spill) begin
          pipe_valid_d[i] <= pipe_valid_d[i-1];
        end
      end
    end
  endgenerate

  // ---------------
  // Output register
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
    .SKIP  (SKIP_OUT_REG)
  ) u_out_reg (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .flush_i(flush_i),
    .valid_i(pipe_valid_d[PIPE_DEPTH-1]),  // valid from EU (downstream)
    .ready_i(ready_i),                     // ready from RS (upstream), CHECK if ready_i or ready_q
    .valid_o(valid_o),                     // valid to RS (upstream)
    .ready_o(ready_spill),                 // ready to EU (downstream)
    .data_i (out_reg_data_in),
    .data_o (out_reg_data_out)
  );

  // Output ready for RS
  assign ready_o       = ready_spill;

  // Exception handling
  // ------------------
  assign except_code_o = E_ILLEGAL_INSTRUCTION;

endmodule
