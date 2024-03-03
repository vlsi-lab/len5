// Inspired by https://github.com/openhwgroup/cva6/blob/master/core/mult.sv


module div #(  // TODO: call div
  // EU-specific parameters
  parameter int unsigned EU_CTL_LEN = 4,
  parameter bit SKIP_IN_REG = 1'b0  // skip input register
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
  //riscv::xlen_t
  //    operand_b,
  //    operand_a;  // input operands after input MUX (input silencing, word operations or full inputs)
  //riscv::xlen_t result;  // result before result mux


  logic [XLEN-1:0] div_a, div_b;
  logic word_op_d, word_op_q;  // save whether the operation was word or not
  logic except_raised_d, except_raised_q;
  logic [XLEN-1:0] result;  // temp result

  // Interface data type
  typedef struct packed {
    logic [XLEN-1:0]       rs1_value;  // first input operand
    logic [XLEN-1:0]       rs2_value;  // second input operand
    logic [EU_CTL_LEN-1:0] ctl;        // control bits
    rob_idx_t              rob_idx;    // instr. index in the RS
  } in_reg_data_t;
  in_reg_data_t in_reg_data_in, in_reg_data_out;
  // ready from downstream (EU) to spill cell, valid from upstream (RS) to EU
  logic ready_div, valid_div;

  // Connect inputs to spill cell
  assign in_reg_data_in.rs1_value = rs1_value_i;
  assign in_reg_data_in.rs2_value = rs2_value_i;
  assign in_reg_data_in.ctl       = ctl_i;
  assign in_reg_data_in.rob_idx   = rob_idx_i;

  // Input reservation station
  spill_cell_flush #(
    .DATA_T(in_reg_data_t),
    .SKIP  (SKIP_IN_REG)
  ) u_out_reg (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .flush_i(flush_i),
    .valid_i(valid_i),         // valid from EU (downstream)
    .ready_o(ready_o),         // ready to EU (downstream)
    .ready_i(ready_div),       // ready from RS (upstream), CHECK if ready_i or ready_q
    .valid_o(valid_div),       // valid to RS (upstream)
    .data_i (in_reg_data_in),
    .data_o (in_reg_data_out)
  );





  // ad-hoc encoding, bit 2 of ctl_i is the word operation bit
  assign word_op_d = in_reg_data_out.ctl[2];
  // Sign and operation management
  always_comb begin : sign_and_op
    div_a           = '0;
    div_b           = '0;
    except_raised_d = 1'b0;
    case (in_reg_data_out.ctl)
      DIV_DIV: begin
        div_a = in_reg_data_out.rs1_value;
        div_b = in_reg_data_out.rs2_value;
      end
      DIV_DIVW: begin
        div_a = {{32{in_reg_data_out.rs1_value[31]}}, in_reg_data_out.rs1_value[31:0]};
        div_b = {{32{in_reg_data_out.rs2_value[31]}}, in_reg_data_out.rs2_value[31:0]};
      end
      DIV_REM: begin
        div_a = in_reg_data_out.rs1_value;
        div_b = in_reg_data_out.rs2_value;
      end
      DIV_REMW: begin
        div_a = {{32{in_reg_data_out.rs1_value[31]}}, in_reg_data_out.rs1_value[31:0]};
        div_b = {{32{in_reg_data_out.rs2_value[31]}}, in_reg_data_out.rs2_value[31:0]};
      end
      DIV_DIVU: begin
        div_a = in_reg_data_out.rs1_value;
        div_b = in_reg_data_out.rs2_value;
      end
      DIV_DIVUW: begin
        div_a = {{32{1'b0}}, in_reg_data_out.rs1_value[31:0]};
        div_b = {{32{1'b0}}, in_reg_data_out.rs2_value[31:0]};
      end
      DIV_REMU: begin
        div_a = in_reg_data_out.rs1_value;
        div_b = in_reg_data_out.rs2_value;
      end
      DIV_REMUW: begin
        div_a = {{32{1'b0}}, in_reg_data_out.rs1_value[31:0]};
        div_b = {{32{1'b0}}, in_reg_data_out.rs2_value[31:0]};
      end
      default: except_raised_d = 1'b1;  // invalid operation
    endcase
  end



  ////////////////////
  // Serial divider //
  ////////////////////
  serdiv #(
    .STABLE_HANDSHAKE(1'b1)
  ) u_serdiv (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .id_i(in_reg_data_out.rob_idx),
    .op_a_i(div_a),
    .op_b_i(div_b),
    .opcode_i (in_reg_data_out.ctl[1:0]),   // 00: udiv, 10: urem, 01: div, 11: rem TODO:  manipulate ctl_i to get the opcode
    .in_vld_i(valid_div),
    .in_rdy_o(ready_div),
    .flush_i(flush_i),
    .out_vld_o(valid_o),
    .out_rdy_i(ready_i),
    .id_o(rob_idx_o),
    .res_o(result)
  );

  //////////////////////
  // Word op register //
  //////////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      word_op_q <= '0;
    end else if (flush_i) begin
      word_op_q <= '0;
    end else begin
      word_op_q <= word_op_d;
    end
  end

  // CHECK: maybe not needed valid_o also manages this,  check inside serdiv
  // Exception handling

  //assign except_raised = (div_b == '0) 1'b1 : 1'b0;
  //////////////////////////////////
  // Exception handling  register //
  //////////////////////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      except_raised_q <= '0;
    end else if (flush_i) begin
      except_raised_q <= '0;
    end else begin
      except_raised_q <= except_raised_d;
    end
  end

  // Result multiplexer
  // if it was a signed word operation the bit will be set and the result will be sign extended accordingly
  assign result_o        = (word_op_q) ? {{32{result[31]}}, result[31:0]} : result;
  assign except_raised_o = except_raised_q;
  assign except_code_o   = E_ILLEGAL_INSTRUCTION;
endmodule  // div
