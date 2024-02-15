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
// File: branch_rs.sv
// Author: Michele Caon
// Date: 08/11/2019

module branch_rs #(
  parameter int unsigned DEPTH = 4,  // must be a power of 2
  localparam int unsigned RsIdxLen = $clog2(DEPTH)
) (
  input logic clk_i,
  input logic rst_n_i,
  input logic flush_i,

  /* Issue Stage */
  input  logic                                         issue_valid_i,
  output logic                                         issue_ready_o,
  input  expipe_pkg::branch_ctl_t                      issue_branch_type_i,
  input  expipe_pkg::op_data_t                         issue_rs1_i,
  input  expipe_pkg::op_data_t                         issue_rs2_i,
  input  logic                    [len5_pkg::XLEN-1:0] issue_imm_value_i,
  input  expipe_pkg::rob_idx_t                         issue_dest_rob_idx_i,
  input  logic                    [len5_pkg::XLEN-1:0] issue_curr_pc_i,
  input  logic                    [len5_pkg::XLEN-1:0] issue_pred_target_i,
  input  logic                                         issue_pred_taken_i,

  /* Common Data Bus (CDB) */
  input  logic                  cdb_ready_i,
  input  logic                  cdb_valid_i,  // to know if the CDB is carrying valid data
  output logic                  cdb_valid_o,
  input  expipe_pkg::cdb_data_t cdb_data_i,
  output expipe_pkg::cdb_data_t cdb_data_o,

  /* Branch unit */
  input  logic                                         bu_valid_i,
  input  logic                                         bu_ready_i,
  output logic                                         bu_valid_o,
  output logic                                         bu_ready_o,
  input  expipe_pkg::rob_idx_t                         bu_rob_idx_i,
  input  logic                                         bu_res_mis_i,        // mispredcition result
  input  logic                    [len5_pkg::XLEN-1:0] bu_link_addr_i,      // computed link address
`ifndef LEN5_C_EN
  input  logic                                         bu_except_raised_i,
`endif  /* LEN5_C_EN */
  output expipe_pkg::rob_idx_t                         bu_rob_idx_o,
  output logic                    [len5_pkg::XLEN-1:0] bu_rs1_o,
  output logic                    [len5_pkg::XLEN-1:0] bu_rs2_o,
  output logic                    [len5_pkg::XLEN-1:0] bu_imm_o,
  output logic                    [len5_pkg::XLEN-1:0] bu_curr_pc_o,
  output logic                    [len5_pkg::XLEN-1:0] bu_pred_target_o,
  output logic                                         bu_pred_taken_o,
  output expipe_pkg::branch_ctl_t                      bu_branch_type_o
);

  import len5_pkg::*;
  import expipe_pkg::*;
  // INTERNAL SIGNALS
  // ----------------

  // Head, tail, and execution counters
  logic head_cnt_en, head_cnt_clr;
  logic tail_cnt_en, tail_cnt_clr;
  logic ex_cnt_en, ex_cnt_clr;
  logic [RsIdxLen-1:0] tail_idx, ex_idx, head_idx;

  // Branch reservation station data
  bu_data_t data[DEPTH];
  bu_state_t curr_state[DEPTH], next_state[DEPTH];

  // Reservation station control
  logic push, pop, ex_accepted, save_res;
  logic fwd_rs1[DEPTH], fwd_rs2[DEPTH];
  bu_op_t bu_op[DEPTH];

  // -------------------------------
  // BRANCH UNIT BUFFER CONTROL UNIT
  // -------------------------------

  // Buffer control
  assign push         = issue_valid_i & issue_ready_o;
  assign pop          = cdb_valid_o & cdb_ready_i;
  assign ex_accepted  = bu_valid_o & bu_ready_i;
  assign save_res     = bu_valid_i & bu_ready_o;

  // Counters control
  assign head_cnt_clr = flush_i;
  assign tail_cnt_clr = flush_i;
  assign ex_cnt_clr   = flush_i;
  assign head_cnt_en  = pop;
  assign tail_cnt_en  = push;
  assign ex_cnt_en    = ex_accepted;

  // Operands forwarding control
  always_comb begin : p_fwd_rs
    foreach (data[i]) begin
      fwd_rs1[i] = cdb_valid_i & (cdb_data_i.rob_idx == data[i].rs1_rob_idx);
      fwd_rs2[i] = cdb_valid_i & (cdb_data_i.rob_idx == data[i].rs2_rob_idx);
    end
  end

  // State progression
  // NOTE: Mealy to avoid resampling data
  always_comb begin : p_state_prog
    // Default operation (no operation)
    foreach (bu_op[i]) bu_op[i] = BU_OP_NONE;

    foreach (curr_state[i]) begin
      case (curr_state[i])
        BU_S_EMPTY: begin  // push a new instruction
          if (push && tail_idx == i[RsIdxLen-1:0]) begin
            if (issue_rs1_i.ready && issue_rs2_i.ready) begin
              next_state[i] = BU_S_EX_REQ;
              bu_op[i]      = BU_OP_INSERT;
            end else if (!issue_rs1_i.ready && issue_rs2_i.ready) begin
              next_state[i] = BU_S_RS1_PENDING;
              bu_op[i]      = BU_OP_INSERT;
            end else if (issue_rs1_i.ready && !issue_rs2_i.ready) begin
              next_state[i] = BU_S_RS2_PENDING;
              bu_op[i]      = BU_OP_INSERT;
            end else begin
              next_state[i] = BU_S_RS12_PENDING;
              bu_op[i]      = BU_OP_INSERT;
            end
          end else next_state[i] = BU_S_EMPTY;
        end
        BU_S_RS12_PENDING: begin  // save rs1 and/or rs2 value from CDB
          if (fwd_rs1[i] && fwd_rs2[i]) begin
            bu_op[i]      = BU_OP_SAVE_RS12;
            next_state[i] = BU_S_EX_REQ;
          end else if (fwd_rs1[i]) begin
            bu_op[i]      = BU_OP_SAVE_RS1;
            next_state[i] = BU_S_RS2_PENDING;
          end else if (fwd_rs2[i]) begin
            bu_op[i]      = BU_OP_SAVE_RS2;
            next_state[i] = BU_S_RS1_PENDING;
          end else next_state[i] = BU_S_RS12_PENDING;
        end
        BU_S_RS1_PENDING: begin  // save rs2 value from CDB
          if (fwd_rs1[i]) begin
            bu_op[i]      = BU_OP_SAVE_RS1;
            next_state[i] = BU_S_EX_REQ;
          end else next_state[i] = BU_S_RS1_PENDING;
        end
        BU_S_RS2_PENDING: begin  // save rs2 value from CDB
          if (fwd_rs2[i]) begin
            bu_op[i]      = BU_OP_SAVE_RS2;
            next_state[i] = BU_S_EX_REQ;
          end else next_state[i] = BU_S_RS2_PENDING;
        end
        BU_S_EX_REQ: begin  // request branch resolution to branch logic
          if (save_res && bu_rob_idx_i == data[i].dest_rob_idx) begin
            bu_op[i]      = BU_OP_SAVE_RES;
            next_state[i] = BU_S_COMPLETED;
          end else if (ex_accepted && ex_idx == i[RsIdxLen-1:0]) next_state[i] = BU_S_EX_WAIT;
          else next_state[i] = BU_S_EX_REQ;
        end
        BU_S_EX_WAIT: begin  // wait for execution completion
          if (save_res && bu_rob_idx_i == data[i].dest_rob_idx) begin
            bu_op[i]      = BU_OP_SAVE_RES;
            next_state[i] = BU_S_COMPLETED;
          end else next_state[i] = BU_S_EX_WAIT;
        end
        BU_S_COMPLETED: begin
          if (pop && head_idx == i[RsIdxLen-1:0]) next_state[i] = BU_S_EMPTY;
          else next_state[i] = BU_S_COMPLETED;
        end
        default: next_state[i] = BU_S_HALT;
      endcase
    end
  end

  // State update
  always_ff @(posedge clk_i or negedge rst_n_i) begin : p_state_update
    if (!rst_n_i) foreach (curr_state[i]) curr_state[i] <= BU_S_EMPTY;
    else if (flush_i) foreach (curr_state[i]) curr_state[i] <= BU_S_EMPTY;
    else curr_state <= next_state;
  end

  // ------------------
  // BRANCH UNIT BUFFER
  // ------------------
  // Branch buffer update
  always_ff @(posedge clk_i or negedge rst_n_i) begin : p_bu_update
    if (!rst_n_i) begin
      foreach (data[i]) begin
        data[i] <= '0;
      end
    end else begin
      /* Performed the required action for each instruction */
      foreach (bu_op[i]) begin
        case (bu_op[i])
          BU_OP_INSERT: begin
            data[i].branch_type  <= issue_branch_type_i;
            data[i].curr_pc      <= issue_curr_pc_i;
            data[i].rs1_rob_idx  <= issue_rs1_i.rob_idx;
            data[i].rs1_value    <= issue_rs1_i.value;
            data[i].rs2_rob_idx  <= issue_rs2_i.rob_idx;
            data[i].rs2_value    <= issue_rs2_i.value;
            data[i].imm_value    <= issue_imm_value_i;
            data[i].dest_rob_idx <= issue_dest_rob_idx_i;
            data[i].target_link  <= issue_pred_target_i;
            data[i].taken        <= issue_pred_taken_i;
          end
          BU_OP_SAVE_RS12: begin
            data[i].rs1_value <= cdb_data_i.res_value;
            data[i].rs2_value <= cdb_data_i.res_value;
          end
          BU_OP_SAVE_RS1: begin
            data[i].rs1_value <= cdb_data_i.res_value;
          end
          BU_OP_SAVE_RS2: begin
            data[i].rs2_value <= cdb_data_i.res_value;
          end
          BU_OP_SAVE_RES: begin
            data[i].target_link  <= bu_link_addr_i;
            data[i].mispredicted <= bu_res_mis_i;
`ifndef LEN5_C_EN
            data[i].except_raised <= bu_except_raised_i;
`endif  /* LEN5_C_EN */
          end
          default: ;
        endcase
      end
    end
  end

  // -----------------
  // OUTPUT EVALUATION
  // -----------------

  /* Issue Stage */
  assign issue_ready_o        = curr_state[tail_idx] == BU_S_EMPTY;

  /* CDB */
  assign cdb_valid_o          = curr_state[head_idx] == BU_S_COMPLETED;
  assign cdb_data_o.rob_idx   = data[head_idx].dest_rob_idx;
  assign cdb_data_o.res_value = data[head_idx].target_link;
`ifndef LEN5_C_EN
  assign cdb_data_o.except_raised = data[head_idx].except_raised;
`else
  assign cdb_data_o.except_raised = 1'b0;
`endif  /* LEN5_C_EN */
  assign cdb_data_o.except_code = (data[head_idx].mispredicted) ? E_MISPREDICTION : E_I_ADDR_MISALIGNED;

  /* Branch Unit logic */
  assign bu_valid_o = curr_state[ex_idx] == BU_S_EX_REQ;
  assign bu_ready_o = 1'b1;
  assign bu_rs1_o = data[ex_idx].rs1_value;
  assign bu_rs2_o = data[ex_idx].rs2_value;
  assign bu_imm_o = data[ex_idx].imm_value;
  assign bu_curr_pc_o = data[ex_idx].curr_pc;
  assign bu_pred_target_o = data[ex_idx].target_link;
  assign bu_pred_taken_o = data[ex_idx].taken;
  assign bu_branch_type_o = data[ex_idx].branch_type;
  assign bu_rob_idx_o = data[ex_idx].dest_rob_idx;

  // --------
  // COUNTERS
  // --------

  // Head counter pointing to the oldest branch/jump instruction
  modn_counter #(
    .N(DEPTH)
  ) u_head_counter (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .en_i   (head_cnt_en),
    .clr_i  (head_cnt_clr),
    .count_o(head_idx),
    .tc_o   ()               // not needed
  );


  // Tail counter pointing to the first empty entry
  modn_counter #(
    .N(DEPTH)
  ) u_tail_counter (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .en_i   (tail_cnt_en),
    .clr_i  (tail_cnt_clr),
    .count_o(tail_idx),
    .tc_o   ()               // not needed
  );

  // Execution counter pointing to the executing branch/jump instruction
  modn_counter #(
    .N(DEPTH)
  ) u_addr_counter (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .en_i   (ex_cnt_en),
    .clr_i  (ex_cnt_clr),
    .count_o(ex_idx),
    .tc_o   ()             // not needed
  );

  // ----------
  // ASSERTIONS
  // ----------
`ifndef SYNTHESIS
`ifndef VERILATOR
  always @(posedge clk_i) begin
    foreach (curr_state[i]) begin
      assert property (@(posedge clk_i) disable iff (!rst_n_i) curr_state[i] == BU_S_HALT |->
        ##1 curr_state[i] != BU_S_HALT);
    end
  end
`endif  /* VERILATOR */
`endif  /* SYNTHESIS */
endmodule
