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

  import len5_pkg::*;  //X MIKE: perchè importarlo sotto e non sopra??
  import expipe_pkg::*;

  // High and low half of the two operands, sign-extended
  logic [XLEN>>1:0] rs1_h, rs1_l, rs2_h, rs2_l;
  //Sign extension of the high-part
  logic [1:0] s_l, s_h;  // s_h[0] is the sign of rs1_h, s_h[1] is the sign of rs2_h
  // Multiplier inputs, on 33 bits
  logic [XLEN>>1:0] mult_a, mult_b;
  // Shift operations and control signals
  logic shift_right, shift_left, clear_acc;
  //mulw management
  logic              mulw_next;
  logic              valid_i_p;
  // MULT  temporary outputs
  logic [XLEN+2-1:0] mult_result_ls;
  logic [XLEN+2-1:0] mult_result_1;
  logic [XLEN+2-1:0] mult_result;  // result of 33bit mult, save bit 64 as sign ext
  logic [XLEN+1:0] mult_acc, mult_acc_next, acc_result;
  logic [XLEN+1:0] mult_acc_rs;
  logic [XLEN+1:0] mult_acc_1, mult_acc_2;
  logic except_raised;

  // FSM states
  typedef enum logic [2:0] {
    S_COMMON,   // is it also the reset state, or should they differ?
    S_AHBL_M,
    S_AHBL_MH,
    S_ALBH_M,
    S_ALBH_MH,
    S_AHBH_MH,
    S_WAIT
  } mult_state_t;  // TODO: define this type in the package expipe_pkg

  mult_state_t mult_state, mult_next_state, mult_init_state;

  // Sign extend high and low part based on the instruction
  // Low part is always unsigned
  assign rs1_l = {s_l[0], rs1_value_i[(XLEN>>1)-1:0]};
  // X MIKE: MULW la fa unsigned o signed la mul tra le parti basse? Se signed da cambiare qui
  assign rs2_l = {s_l[1], rs2_value_i[(XLEN>>1)-1:0]};
  assign rs1_h = {s_h[0], rs1_value_i[XLEN-1:XLEN>>1]};
  assign rs2_h = {s_h[1], rs2_value_i[XLEN-1:XLEN>>1]};

  // X MIKE: sign extension calculation could be moved to a previous stage to shorten the critical path
  always_comb begin : sign_extend_init
    s_l[0]         = 1'b0;
    s_l[1]         = 1'b0;
    s_h[0]         = 0;
    s_h[1]         = 0;
    except_raised  = 1'b0;
    mulw_next      = 1'b0;
    mult_init_state = S_COMMON;
    unique case (ctl_i)
      MULT_MUL: begin
        s_h[0]         = rs1_value_i[XLEN-1];
        s_h[1]         = rs2_value_i[XLEN-1];
        mult_init_state = S_AHBL_M;
      end
      MULT_MULW: begin
        s_l[0]         = rs1_value_i[(XLEN>>1)-1];
        s_l[1]         = rs2_value_i[(XLEN>>1)-1];
        s_h[0]         = rs1_value_i[XLEN-1];
        s_h[1]         = rs2_value_i[XLEN-1];
        mult_init_state = S_COMMON;
        mulw_next      = 1'b1;
      end
      MULT_MULH: begin
        s_h[0]         = rs1_value_i[XLEN-1];
        s_h[1]         = rs2_value_i[XLEN-1];
        mult_init_state = S_AHBL_MH;
      end
      MULT_MULHU: begin
        s_h[0]         = 0;
        s_h[1]         = 0;
        mult_init_state = S_AHBL_MH;
      end
      MULT_MULHSU: begin
        s_h[0]         = rs1_value_i[XLEN-1];
        s_h[1]         = 0;
        mult_init_state = S_AHBL_MH;
      end
      default: except_raised = 1'b1;
    endcase
  end

  // State progression
  always_comb begin : mult_state_prog
    case (mult_state)
      S_COMMON: begin
        if (valid_i_p)    // if ctl_i = MULT_MULW remains in S_COMMON, either waiting ready_i signal or computing new values
          // ATTENZIONE: deve essere il valid_i campionato al ciclo
          // prima ad essere ad 1 non quello attuale
          mult_next_state = mult_init_state;  //S_COMMON works also as a WAIT state for MULW
        else mult_next_state = S_COMMON;
      end
      //S_ALBL_M: begin
      //    mult_next_state = S_AHBL_M;
      //end
      //S_ALBL_MW: begin  // check ready_i to correctly save result
      //    if (valid_i && ready_i)
      //        mult_next_state = mult_init_state;
      //    else if (!ready_i)
      //        mult_next_state = S_WAIT;
      //    else
      //        mult_next_state = S_IDLE;
      //end
      //S_ALBL_MH: begin
      //    mult_next_state = S_AHBL_MH;
      //end
      S_AHBL_M: begin
        mult_next_state = S_ALBH_M;
      end
      S_AHBL_MH: begin
        mult_next_state = S_ALBH_MH;
      end
      S_ALBH_M: begin
        if (!ready_i) mult_next_state = S_WAIT;
        else mult_next_state = S_COMMON;
      end
      S_ALBH_MH: begin
        mult_next_state = S_AHBH_MH;
      end
      S_AHBH_MH: begin
        if (!ready_i) mult_next_state = S_WAIT;
        else mult_next_state = S_COMMON;
      end
      S_WAIT: begin
        if (!ready_i) mult_next_state = S_WAIT;
        else mult_next_state = S_COMMON;
      end
      default: mult_next_state = S_COMMON;
    endcase
  end

  ///////////////////////////
  // MUL 64-bit multicycle //
  ///////////////////////////
  /* Domande per MIKE:
    1) gestione ready_o, valid_o manca? Qual è la policy per gestirli?
    2) Gestione input come valid, ready, flush, manca. Come vanno gestiti?
    */
  // Interemediate datapath signals management
  always_comb begin : control_s
    mult_a        = rs1_l;
    mult_b        = rs2_l;
    mult_acc_next = acc_result;
    shift_right  = 1'b0;
    shift_left   = 1'b0;
    clear_acc    = 1'b0;  // if uncommented set mult_acc_next = acc_result always
    //mulw_next = 1'b0;
    case (mult_state)
      S_COMMON: begin
        clear_acc = 1'b1;
        //if (ctl_i == MULT_MULW) // TODO: move to the initial process making a case on MULT_MULW
        //    mulw_next = 1'b1
      end
      S_AHBL_M: begin
        mult_a        = rs1_h;
        mult_b        = rs2_l;
        mult_acc_next = acc_result;
        shift_left   = 1'b1;
        //clear_acc = 1'b1;
      end
      S_AHBL_MH: begin
        mult_a        = rs1_h;
        mult_b        = rs2_l;
        mult_acc_next = acc_result;
        shift_right  = 1'b1;  // CHECK: shift right albl+0
        //clear_acc = 1'b1;
      end
      S_ALBH_M: begin
        mult_a      = rs1_l;
        mult_b      = rs2_h;
        //mult_acc_next = '0;
        shift_left = 1'b1;
      end
      S_ALBH_MH: begin
        mult_a        = rs1_l;
        mult_b        = rs2_h;
        mult_acc_next = acc_result;
        //clear_acc = 1'b1;
      end
      S_AHBH_MH: begin
        mult_a       = rs1_h;
        mult_b       = rs2_h;
        //mult_acc_next = '0;
        shift_right = 1'b1;  //check: shift right ahbl+albh+albl>>32
      end
      S_WAIT: begin
        mult_a = '0;
        mult_b = '0;
        //mulw_next = mulw; //keep previous value TOLTO PERCHè l'ho
        //messo nell'altro process,capire se funziona quando entro nel
        //wait o succedono casini
        //clear_acc = '0;
      end
      default: ;
    endcase

  end


  // Output evaluation
  always_comb begin : mult_out_eval
    valid_o = 1'b0;
    ready_o = 1'b1;
    case (mult_state)
      S_COMMON: begin
        if (valid_i_p) begin  // the input is valid can compute
          // ATTENZIONE: deve essere il valid_i del cc di prima ad
          // essere valido non quello di questo ciclo, se no che sto
          // campionando?
          if (ctl_i == MULT_MULW) begin
            ready_o = ready_i;
            valid_o = 1'b1;
          end else ready_o = 1'b0;
        end  // if ! valid_i default values


      end
      S_AHBL_M: begin
        ready_o = 1'b0;
        //valid_o = 1'b0;
      end
      S_AHBL_MH: begin
        ready_o = 1'b0;
        //valid_o = 1'b0;
      end
      S_ALBH_M: begin
        ready_o = ready_i;
        valid_o = 1'b1;
      end
      S_ALBH_MH: begin
        ready_o = 1'b0;
        //valid_o = 1'b0;
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
  always_ff @(posedge clk_i or negedge rst_ni) begin : acc_reg
    if (!rst_ni) begin
      mult_acc <= '0;
    end else if (flush_i) begin
      mult_acc <= '0;
    end else begin
      mult_acc <= mult_acc_next;
    end
  end
  /*
  always_ff @(posedge clk_i or negedge rst_ni) begin : mulw_reg
    if (!rst_ni) begin
      mulw <= '0;
    end else if (flush_i) begin
      mulw <= '0;
    end else begin
      mulw <= mulw_next;
    end
  end
  */
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
  assign mult_result      = $signed(mult_a) * $signed(mult_b);

  assign mult_result_ls   = $signed(mult_result) << (XLEN >> 1);
  assign mult_acc_rs      = $signed(mult_acc) >>> (XLEN >> 1);  //CHECK nel caso di MULHSU e MULHU
  // Accumulate results for multicycle operations
  // non cosi semplice, i risultati vanno man mano shiftati a sinistra o a destra, dipende dall'approccio che utiizzo
  //TODO stabilire le bit-width degli accumulatori.
  assign mult_result_1    = shift_left ? $signed(mult_result_ls) : mult_result;
  assign mult_acc_1       = shift_right ? mult_acc_rs : mult_acc;
  assign mult_acc_2       = clear_acc ? '0 : mult_acc_1;
  // Accumulate results for multicycle operations
  assign acc_result      = $signed(mult_result_1) + $signed(mult_acc_2);

  assign result_o        = mulw_next ? {{32{acc_result[31]}}, acc_result[31:0]} : acc_result[63:0];
  assign rob_idx_o       = rob_idx_i;
  assign except_raised_o = except_raised;
  assign except_code_o   = E_ILLEGAL_INSTRUCTION;
endmodule  // mult
