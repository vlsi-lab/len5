// Copyright 2024 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: mult.sv
// Author: Flavia Guella
// Date: 21/02/2024


/* Multiplier unit able to perform all mult operation of RV64M ISA:
-MUL
-MULW
-MULH
-MULHU
-MULHSU
The interface of the unit has to be adapted to that of the processor exe unit*/
// TODO: remove useless comments, add comments

module mult #(
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

  // High and low half of the two operands, extended
  logic [XLEN>>1:0] rs1_h, rs1_l, rs2_h, rs2_l;
  //High and low half sign-extension
  logic [1:0] s_l, s_h;  // s_h[0] is the sign of rs1_h, s_h[1] is the sign of rs2_h
  // Multiplier inputs, on 33 bits to accomodate unsigned*unsigned, signed*signed, signed*unsigned
  logic [XLEN>>1:0] mult_a, mult_b;
  // Shift operations and clear signals
  logic shift_right, shift_left, clear_acc;
  //mulw management
  logic              mulw_next;  // 1 if instruction to be executed is mulw
  logic              valid_i_p;  // valid_i sampled at the previous cycle
  // MULT  temporary outputs
  logic [XLEN+2-1:0] mult_result_ls;  // result of 33bit mult shifted left
  logic [XLEN+2-1:0] mult_result_1;  // muxed result of 33bit mult
  logic [XLEN+2-1:0] mult_result;  // result of 33bit mult
  logic [XLEN+1:0] mult_acc, mult_acc_next, acc_result;
  logic [XLEN+1:0] mult_acc_rs;  // result of accumulatorshifted right
  logic [XLEN+1:0] mult_acc_1, mult_acc_2;  // muxed result of accumulator
  logic except_raised;

  // FSM states
  typedef enum logic [2:0] {
    S_COMMON,
    S_AHBL_M,
    S_AHBL_MH,
    S_ALBH_M,
    S_ALBH_MH,
    S_AHBH_MH,
    S_WAIT
  } mult_state_t;

  mult_state_t mult_state, mult_next_state, mult_init_state;

  // Sign extend high and low part based on the instruction
  // Low part is always unsigned
  assign rs1_l = {
    s_l[0], rs1_value_i[(XLEN>>1)-1:0]
  };  // TODO: check if sign extension is required for MULW or if 0 is fine as well, save some logic
  assign rs2_l = {s_l[1], rs2_value_i[(XLEN>>1)-1:0]};
  assign rs1_h = {s_h[0], rs1_value_i[XLEN-1:XLEN>>1]};
  assign rs2_h = {s_h[1], rs2_value_i[XLEN-1:XLEN>>1]};

  /////////////////////////////
  // Operands sign extension //
  /////////////////////////////
  always_comb begin : sign_extend_init
    s_l[0]          = 1'b0;
    s_l[1]          = 1'b0;
    s_h[0]          = 0;
    s_h[1]          = 0;
    except_raised   = 1'b0;
    mulw_next       = 1'b0;
    mult_init_state = S_COMMON;
    unique case (ctl_i)
      MULT_MUL: begin
        s_h[0]          = rs1_value_i[XLEN-1];
        s_h[1]          = rs2_value_i[XLEN-1];
        mult_init_state = S_AHBL_M;
      end
      MULT_MULW: begin
        s_l[0]          = rs1_value_i[(XLEN>>1)-1];
        s_l[1]          = rs2_value_i[(XLEN>>1)-1];
        s_h[0]          = rs1_value_i[XLEN-1];
        s_h[1]          = rs2_value_i[XLEN-1];
        mult_init_state = S_COMMON;
        mulw_next       = 1'b1;
      end
      MULT_MULH: begin
        s_h[0]          = rs1_value_i[XLEN-1];
        s_h[1]          = rs2_value_i[XLEN-1];
        mult_init_state = S_AHBL_MH;
      end
      MULT_MULHU: begin
        s_h[0]          = 0;
        s_h[1]          = 0;
        mult_init_state = S_AHBL_MH;
      end
      MULT_MULHSU: begin
        s_h[0]          = rs1_value_i[XLEN-1];
        s_h[1]          = 0;
        mult_init_state = S_AHBL_MH;
      end
      default: except_raised = 1'b1;
    endcase
  end

  ///////////////////////
  // State progression //
  ///////////////////////
  always_comb begin : mult_state_prog
    case (mult_state)
      S_COMMON: begin     // initial state: computation starts (AL*BL) or unit stays in idle if valid_i_p=0
        if (valid_i_p)    // if ctl_i = MULT_MULW remains in S_COMMON, either waiting ready_i signal or computing new values
          mult_next_state = mult_init_state;  //S_COMMON works also as a WAIT state for MULW
        else mult_next_state = S_COMMON;
      end
      S_AHBL_M: begin  // AH*BL for MULT_MUL
        mult_next_state = S_ALBH_M;
      end
      S_AHBL_MH: begin  // AH*BL for MULT_MULH
        mult_next_state = S_ALBH_MH;
      end
      S_ALBH_M: begin  // AL*BH for MULT_MUL, result is valid
        if (!ready_i) mult_next_state = S_WAIT;
        else mult_next_state = S_COMMON;
      end
      S_ALBH_MH: begin  // AL*BH for MULT_MULH
        mult_next_state = S_AHBH_MH;
      end
      S_AHBH_MH: begin  // AH*BH for MULT_MULH, result is valid
        if (!ready_i) mult_next_state = S_WAIT;
        else mult_next_state = S_COMMON;
      end
      S_WAIT: begin  // wait for ready_i signal
        if (!ready_i) mult_next_state = S_WAIT;
        else mult_next_state = S_COMMON;
      end
      default: mult_next_state = S_COMMON;
    endcase
  end

  ////////////////////////////////////////////
  // MUL 64-bit multicycle datapath control //
  ////////////////////////////////////////////
  always_comb begin : control_s
    mult_a        = rs1_l;
    mult_b        = rs2_l;
    mult_acc_next = acc_result;
    shift_right   = 1'b0;
    shift_left    = 1'b0;
    clear_acc     = 1'b0;
    case (mult_state)
      S_COMMON: begin
        clear_acc = 1'b1;  // clear accumulator
      end
      S_AHBL_M: begin
        mult_a        = rs1_h;
        mult_b        = rs2_l;
        mult_acc_next = acc_result;
        shift_left    = 1'b1;  // shift left, albl + ahbl<<32
      end
      S_AHBL_MH: begin
        mult_a        = rs1_h;
        mult_b        = rs2_l;
        mult_acc_next = acc_result;
        shift_right   = 1'b1;  // shift right, albl>>32 + ahbl
      end
      S_ALBH_M: begin
        mult_a     = rs1_l;
        mult_b     = rs2_h;
        shift_left = 1'b1;  // shift left, albh<<32 + ahbl<<32 + albl
      end
      S_ALBH_MH: begin
        mult_a        = rs1_l;
        mult_b        = rs2_h;
        mult_acc_next = acc_result;
      end
      S_AHBH_MH: begin
        mult_a      = rs1_h;
        mult_b      = rs2_h;
        shift_right = 1'b1;  //shift right (ahbl+albh+albl)>>32
      end
      S_WAIT: begin
        mult_a = '0;
        mult_b = '0;
      end
      default: ;
    endcase

  end


  //////////////////////////////////////
  // Out hansdshake signal evaluation //
  //////////////////////////////////////
  always_comb begin : mult_out_eval
    valid_o = 1'b0;
    ready_o = 1'b1;
    case (mult_state)
      S_COMMON: begin
        if (valid_i_p) begin  // the input is valid can compute
          if (ctl_i == MULT_MULW) begin
            ready_o = ready_i;
            valid_o = 1'b1;
          end else ready_o = 1'b0;
        end  // if ! valid_i default values
      end
      S_AHBL_M: begin
        ready_o = 1'b0;
      end
      S_AHBL_MH: begin
        ready_o = 1'b0;
      end
      S_ALBH_M: begin
        ready_o = ready_i;
        valid_o = 1'b1;
      end
      S_ALBH_MH: begin
        ready_o = 1'b0;
      end
      S_AHBH_MH: begin
        ready_o = ready_i;
        valid_o = 1'b1;
      end
      S_WAIT: begin
        ready_o = ready_i;
        valid_o = 1'b1;
      end
      default: ;
    endcase
  end

  /////////////////
  // FSM control //
  /////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin : fsm_state
    if (!rst_ni) begin
      mult_state <= S_COMMON;
    end else if (flush_i) begin
      mult_state <= S_COMMON;
    end else begin
      mult_state <= mult_next_state;
    end
  end

  //////////////////////////
  // Accumulator register //
  //////////////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin : acc_reg
    if (!rst_ni) begin
      mult_acc <= '0;
    end else if (flush_i) begin
      mult_acc <= '0;
    end else begin
      mult_acc <= mult_acc_next;
    end
  end

  ////////////////////
  // Valid register //
  ////////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin : valid_i_reg
    if (!rst_ni) begin
      valid_i_p <= '0;
    end else if (flush_i) begin
      valid_i_p <= '0;
    end else begin
      valid_i_p <= valid_i;
    end
  end

  ///////////////////////
  // 33-bit multiplier //
  ///////////////////////
  assign mult_result     = $signed(mult_a) * $signed(mult_b);

  // shift operations
  assign mult_result_ls  = $signed(mult_result) << (XLEN >> 1);
  assign mult_acc_rs     = $signed(mult_acc) >>> (XLEN >> 1);

  //TODO: check if results bitwidth can be reduced
  // MUX selection of multiplication and accumulation results
  assign mult_result_1   = shift_left ? $signed(mult_result_ls) : mult_result;
  assign mult_acc_1      = shift_right ? mult_acc_rs : mult_acc;
  assign mult_acc_2      = clear_acc ? '0 : mult_acc_1;
  // Accumulate results for multicycle operations
  assign acc_result      = $signed(mult_result_1) + $signed(mult_acc_2);

  ///////////////////////
  // Output evaluation //
  ///////////////////////
  assign result_o        = mulw_next ? {{32{acc_result[31]}}, acc_result[31:0]} : acc_result[63:0];
  assign rob_idx_o       = rob_idx_i;
  assign except_raised_o = except_raised;
  assign except_code_o   = E_ILLEGAL_INSTRUCTION;

  // TODO: add spill cell if required to split critical path.
endmodule  // mult
