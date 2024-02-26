// TODO: inspired by https://github.com/openhwgroup/cva6/blob/master/core/mult.sv


module div #(  // TODO: call div
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
  //riscv::xlen_t
  //    operand_b,
  //    operand_a;  // input operands after input MUX (input silencing, word operations or full inputs)
  //riscv::xlen_t result;  // result before result mux

  logic [XLEN-1:0] div_a, div_b;
  logic word_op_d, word_op_q;  // save whether the operation was word or not
  logic except_raised_d, except_raised_q;
  logic [XLEN-1:0] result;  // temp result

  // ad-hoc encoding, bit 2 of ctl_i is the word operation bit
  assign word_op_d = ctl_i[2];
  // Sign and operation management
  always_comb begin : sign_and_op
    div_a           = '0;
    div_b           = '0;
    except_raised_d = 1'b0;
    case (ctl_i)
      DIV_DIV: begin
        div_a = rs1_value_i;
        div_b = rs2_value_i;
      end
      DIV_DIVW: begin
        div_a = {{32{rs1_value_i[31]}}, rs1_value_i[31:0]};
        div_b = {{32{rs2_value_i[31]}}, rs2_value_i[31:0]};
      end
      DIV_REM: begin
        div_a = rs1_value_i;
        div_b = rs2_value_i;
      end
      DIV_REMW: begin
        div_a = {{32{rs1_value_i[31]}}, rs1_value_i[31:0]};
        div_b = {{32{rs2_value_i[31]}}, rs2_value_i[31:0]};
      end
      DIV_DIVU: begin
        div_a = rs1_value_i;
        div_b = rs2_value_i;
      end
      DIV_DIVUW: begin
        div_a = {{32{'0}}, rs1_value_i[31:0]};
        div_b = {{32{'0}}, rs2_value_i[31:0]};
      end
      DIV_REMU: begin
        div_a = rs1_value_i;
        div_b = rs2_value_i;
      end
      DIV_REMUW: begin
        div_a = {{32{'0}}, rs1_value_i[31:0]};
        div_b = {{32{'0}}, rs2_value_i[31:0]};
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
    .id_i(rob_idx_i),
    .op_a_i(div_a),
    .op_b_i(div_b),
    .opcode_i (ctl_i[1:0]),   // 00: udiv, 10: urem, 01: div, 11: rem TODO:  manipulate ctl_i to get the opcode
    .in_vld_i(valid_i),
    .in_rdy_o(ready_o),
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
    end else begin
      word_op_q <= word_op_d;
    end
  end

  //////////////////////
  // Word op register //
  //////////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      word_op_q <= 1'b0;
    end else if (flush_i) begin
      word_op_q <= 1'b0;
    end else begin
      word_op_q <= word_op_d;
    end
  end

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
