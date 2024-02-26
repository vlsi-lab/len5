// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: rob.sv
// Author: Michele Caon
// Date: 14/07/2022

/**
 * @brief Reaorder Buffer
 *
 * @details Based on a simple FIFO queue and expanded to support
 *          updates from the CDB.
 */
module rob #(
  parameter int DEPTH = 4
) (
  /* Clock and reset */
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i,

  /* Issue stage */
  input logic issue_valid_i,  // from upstream hardware
  output logic issue_ready_o,  // to upstream hardware
  input expipe_pkg::rob_entry_t issue_data_i,
  output expipe_pkg::rob_idx_t issue_tail_idx_o,  // the ROB entry where the new instruction is being allocated
  input expipe_pkg::rob_idx_t issue_rs1_rob_idx_i,
  input expipe_pkg::rob_idx_t issue_rs2_rob_idx_i,

  /* Operands forwarding logic */
  output logic                      opfwd_rs1_valid_o,
  output logic                      opfwd_rs1_ready_o,
  output logic [len5_pkg::XLEN-1:0] opfwd_rs1_value_o,
  output logic                      opfwd_rs2_valid_o,
  output logic                      opfwd_rs2_ready_o,
  output logic [len5_pkg::XLEN-1:0] opfwd_rs2_value_o,

  /* Store buffer */
  input  expipe_pkg::rob_idx_t sb_mem_idx_i,   // executing store ROB index
  output logic                 sb_mem_clear_o, // store is clear to execute

  /* Commit stage */
  output logic                   comm_valid_o,    // to downstream hardware
  input  logic                   comm_ready_i,    // from downstream hardware
  output expipe_pkg::rob_entry_t comm_data_o,
  output expipe_pkg::rob_idx_t   comm_head_idx_o, // ROB head idx to update register status

  /* Common data bus (CDB) */
  input  logic                  cdb_valid_i,
  input  expipe_pkg::cdb_data_t cdb_data_i,
  output logic                  cdb_ready_o
);

  import expipe_pkg::*;
  import len5_pkg::XLEN;
  import len5_pkg::REG_IDX_LEN;
  import len5_pkg::E_MISPREDICTION;

  // INTERNAL SIGNALS
  // ----------------
  // Head and tail counters
  logic [$clog2(DEPTH)-1:0] head_idx, tail_idx, clear_idx;
  logic head_cnt_en, tail_cnt_en, clear_cnt_en;
  logic head_cnt_clr, tail_cnt_clr, clear_cnt_clr;

  // FIFO data
  logic       data_valid[DEPTH];
  rob_entry_t data      [DEPTH];

  // FIFO control
  logic fifo_push, fifo_pop, update_res;

  // Clear instruction
  logic instr_clear, entry_clear, cdb_clear;

  // -----------------
  // FIFO CONTROL UNIT
  // -----------------

  // Push/pop/update control
  assign fifo_push = issue_valid_i && issue_ready_o;
  assign fifo_pop = comm_valid_o && comm_ready_i;
  assign update_res = cdb_valid_i;

  // Counters control
  assign head_cnt_clr = flush_i;
  assign tail_cnt_clr = flush_i;
  assign clear_cnt_clr = flush_i;
  assign head_cnt_en = fifo_pop;
  assign tail_cnt_en = fifo_push;
  assign clear_cnt_en = instr_clear;

  // Oldest instruction that is not "clear to commit"
  // NOTE: the instruction pointed by clear_idx can be committed if:
  // 1) it is valid
  // 2) no exception has been raised for it
  // 3) no misprediction has been raised for it
  // 4) its result is valid
  // This information is used by instructions committing to memory to know if
  // they can be executed out-of-order. Instruction marked as non-critical allow
  // out-of-order execution of subsequent memory instructions unconditionally.
  assign entry_clear = ~data[clear_idx].except_raised &
                       (data[clear_idx].except_code != E_MISPREDICTION) &
                       data[clear_idx].res_ready;
  assign cdb_clear   = cdb_valid_i &
                       cdb_data_i.rob_idx == clear_idx &
                       ~cdb_data_i.except_raised &
                       (cdb_data_i.except_code != E_MISPREDICTION);
  assign instr_clear = data_valid[clear_idx] & (~data[clear_idx].order_crit | entry_clear | cdb_clear);

  // -----------
  // FIFO UPDATE
  // -----------
  // NOTE: operations priority:
  // 1) push (from issue stage)
  // 2) pop
  // 3) update result (from CDB)
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_fifo_update
    if (!rst_ni) begin
      foreach (data[i]) begin
        data_valid[i] <= 1'b0;
        data[i]       <= '0;
      end
    end else if (flush_i) begin
      foreach (data[i]) begin
        data_valid[i] <= 1'b0;  // clearing valid is enough
      end
    end else begin
      foreach (data[i]) begin
        if (fifo_push && tail_idx == i[$clog2(DEPTH)-1:0]) begin
          data_valid[i] <= 1'b1;
          data[i]       <= issue_data_i;
        end else if (fifo_pop && head_idx == i[$clog2(DEPTH)-1:0]) begin
          data_valid[i] <= 1'b0;
        end else if (update_res && cdb_data_i.rob_idx == i[ROB_IDX_LEN-1:0]) begin
          data[i].res_ready     <= 1'b1;
          data[i].res_value     <= cdb_data_i.res_value;
          data[i].except_raised <= cdb_data_i.except_raised;
          data[i].except_code   <= cdb_data_i.except_code;
        end
      end

      // Clear status update
      if (data_valid[clear_idx]) begin
        data[clear_idx].mem_clear <= 1'b1;
      end
    end
  end

  // ------------
  // ROB COUNTERS
  // ------------
  // Head counter
  // Tracks the oldest instruction in the ROB
  modn_counter #(
    .N(DEPTH)
  ) u_head_counter (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .en_i   (head_cnt_en),
    .clr_i  (head_cnt_clr),
    .count_o(head_idx),
    .tc_o   ()               // not needed
  );

  // Tail counter
  // Tracks the first available empty entry in the ROB
  modn_counter #(
    .N(DEPTH)
  ) u_tail_counter (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .en_i   (tail_cnt_en),
    .clr_i  (tail_cnt_clr),
    .count_o(tail_idx),
    .tc_o   ()               // not needed
  );

  // Clear counter
  // Tracks the oldest instruction that is NOT "clear to commit"
  modn_counter #(
    .N(DEPTH)
  ) u_clear_counter (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .en_i   (clear_cnt_en),
    .clr_i  (clear_cnt_clr),
    .count_o(clear_idx),
    .tc_o   ()                // not needed
  );

  // --------------
  // OUTPUT CONTROL
  // --------------

  /* CDB */
  // NOTE: since the ROB entries are allocated at issue time, the ROB is
  // always ready to get the results from the CDB.
  assign cdb_ready_o = 1'b1;

  /* Issue stage */
  assign issue_ready_o = !data_valid[tail_idx];
  assign issue_tail_idx_o = tail_idx;

  /* Store buffer */
  assign sb_mem_clear_o    = data_valid[sb_mem_idx_i] & (data[sb_mem_idx_i].mem_clear | clear_idx == sb_mem_idx_i);

  /* Commit stage */
  assign comm_valid_o = data_valid[head_idx] & data[head_idx].res_ready;
  assign comm_data_o = data[head_idx];
  assign comm_head_idx_o = head_idx;
  assign opfwd_rs1_valid_o = data_valid[issue_rs1_rob_idx_i];
  assign opfwd_rs1_ready_o = data[issue_rs1_rob_idx_i].res_ready;
  assign opfwd_rs1_value_o = data[issue_rs1_rob_idx_i].res_value;
  assign opfwd_rs2_valid_o = data_valid[issue_rs2_rob_idx_i];
  assign opfwd_rs2_ready_o = data[issue_rs2_rob_idx_i].res_ready;
  assign opfwd_rs2_value_o = data[issue_rs2_rob_idx_i].res_value;

  // ----------
  // ASSERTIONS
  // ----------
`ifndef SYNTHESIS
`ifndef VERILATOR
  property p_fifo_push;
    @(posedge clk_i) disable iff (!rst_ni) sync_accept_on (flush_i)
      issue_valid_i && issue_ready_o |-> ##1 data_valid[$past(
        tail_idx
    )] == 1'b1 && data[$past(
        tail_idx
    )] == $past(
        issue_data_i
    );
  endproperty
  a_fifo_push :
  assert property (p_fifo_push)
  else
    $error(
        "%t: issue_valid_i: %b | past data_valid: %b | tail_idx: %h | past tail_idx: %h",
        $time,
        issue_valid_i,
        data_valid[$past(
            tail_idx
        )],
        tail_idx,
        $past(
            tail_idx
        )
    );

  property p_fifo_pop;
    @(posedge clk_i) disable iff (!rst_ni) sync_accept_on (flush_i)
      comm_valid_o && comm_ready_i |-> ##1 issue_ready_o == 1'b1 && data_valid[$past(
        head_idx
    )] == 1'b0;
  endproperty
  a_fifo_pop :
  assert property (p_fifo_pop);

  property p_ready_n;
    @(posedge clk_i) disable iff (!rst_ni) sync_accept_on (flush_i) !comm_ready_i && comm_valid_o |=> comm_valid_o;
  endproperty
  a_ready_n :
  assert property (p_ready_n);

  property p_push_pop;
    @(posedge clk_i) disable iff (!rst_ni) fifo_push && fifo_pop |-> head_idx != tail_idx;
  endproperty
  a_push_pop :
  assert property (p_push_pop);

  property p_cdb_valid;
    @(posedge clk_i) disable iff (!rst_ni) cdb_valid_i |-> data_valid[cdb_data_i.rob_idx];
  endproperty
  a_cdb_valid :
  assert property (p_cdb_valid);

  property p_flush;
    @(posedge clk_i) disable iff (!rst_ni) $rose(
        flush_i
    ) |=> comm_valid_o == 1'b0 && issue_ready_o == 1'b1;
  endproperty
  a_flush :
  assert property (p_flush);
`endif  /* VERILATOR */
`endif  /* SYNTHESIS */

endmodule
