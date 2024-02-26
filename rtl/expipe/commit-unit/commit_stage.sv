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
// File: commit_stage.sv
// Author: Michele Caon
// Date: 20/11/2019

module commit_stage (
  input logic clk_i,
  input logic rst_ni,

  // Flush signal
  output logic ex_mis_flush_o,  // flush after misprediction
  output logic except_flush_o,  // flush after exception

  // Data to frontend
  input  logic                      fe_ready_i,
  output logic                      fe_except_raised_o,
  output logic [len5_pkg::XLEN-1:0] fe_except_pc_o,

  // Issue logic <--> commit stage
  input  logic                                        issue_valid_i,
  output logic                                        issue_ready_o,
  input  expipe_pkg::rob_entry_t                      issue_data_i,
  output expipe_pkg::rob_idx_t                        issue_tail_idx_o,
  input  expipe_pkg::rob_idx_t                        issue_rs1_rob_idx_i,
  output logic                                        issue_rs1_ready_o,
  output logic                   [len5_pkg::XLEN-1:0] issue_rs1_value_o,
  input  expipe_pkg::rob_idx_t                        issue_rs2_rob_idx_i,
  output logic                                        issue_rs2_ready_o,
  output logic                   [len5_pkg::XLEN-1:0] issue_rs2_value_o,
  // resume execution after stall
  output logic                                        issue_resume_o,

  /* Common data bus (CDB) */
  input  logic                  cdb_valid_i,
  input  expipe_pkg::cdb_data_t cdb_data_i,
  output logic                  cdb_ready_o,

  // Commit logic <--> store buffer
  input  expipe_pkg::rob_idx_t sb_mem_idx_i,   // executing store ROB index
  output logic                 sb_mem_clear_o, // store is clear to execute

  // Commit logic <--> register files and status
  output logic int_rs_valid_o,
  output logic int_rf_valid_o,
  // output logic fp_rs_valid_o,
  // output logic fp_rf_valid_o,

  // Data to the register files
  output logic [len5_pkg::REG_IDX_LEN-1:0] rd_idx_o,   // the index of the destination register (rd)
  output logic [       len5_pkg::XLEN-1:0] rd_value_o, // the value to be stored in rd

  // CSRs
  output logic csr_valid_o,
  input csr_pkg::csr_t csr_data_i,
  input csr_pkg::csr_mtvec_t csr_mtvec_i,  // mtvec data
  output expipe_pkg::comm_csr_instr_t csr_comm_insn_o,  // committing instruction type
  output csr_pkg::csr_op_t csr_op_o,
  output logic [csr_pkg::CSR_ADDR_LEN-1:0] csr_addr_o,
  output logic [len5_pkg::REG_IDX_LEN-1:0] csr_rs1_idx_o,
  output logic [len5_pkg::XLEN-1:0] csr_data_o,
  output logic [len5_pkg::REG_IDX_LEN-1:0] csr_rd_idx_o
);

  import len5_config_pkg::*;
  import expipe_pkg::*;
  import len5_pkg::*;
  import csr_pkg::*;
  import fetch_pkg::resolution_t;

  // INTERNAL SIGNALS
  // ----------------

  // Input register data
  typedef struct packed {
    rob_entry_t data;
    rob_idx_t   rob_idx;
  } inreg_data_t;

  // Commit decoder
  comm_type_t             cd_comm_type;
  csr_op_t                cd_csr_op;

  // ROB <--> input register
  logic                   rob_reg_valid;
  logic                   reg_rob_ready;
  rob_entry_t             rob_reg_head_entry;
  rob_idx_t               rob_reg_head_idx;

  // ROB <--> Operands forwarding logic
  logic                   rob_opfwd_rs1_valid;
  logic                   rob_opfwd_rs1_ready;
  logic        [XLEN-1:0] rob_opfwd_rs1_value;
  logic                   rob_opfwd_rs2_valid;
  logic                   rob_opfwd_rs2_ready;
  logic        [XLEN-1:0] rob_opfwd_rs2_value;

  // Input register <--> commit CU
  logic                   inreg_cu_mispredicted;
  logic                   cu_inreg_ready;
  logic                   inreg_cu_valid;

  // Input registers <--> outputs
  logic                   inreg_buff_full;
  inreg_data_t            inreg_buff_data;

  // Committing instruction register
  logic comm_reg_en, comm_reg_clr;
  inreg_data_t comm_reg_data;
  csr_op_t     comm_reg_csr_op;
  logic        comm_reg_valid;

  // Commit adder
  logic [XLEN-1:0] adder_op, adder_out;

  // rd MUX
  comm_rd_sel_t                     cu_rd_sel;
  logic          [        XLEN-1:0] rd_value;

  // CSR MUX
  comm_csr_sel_t                    cu_csr_sel;
  logic          [CSR_ADDR_LEN-1:0] cu_csr_addr;
  logic          [        XLEN-1:0] csr_data;
  logic          [CSR_ADDR_LEN-1:0] csr_addr;

  // commit CU <--> others
  logic                             cu_csr_override;
  logic                             cu_mis_flush;
  logic                             cu_except_flush;

  // -------
  // MODULES
  // -------

  //     cdb    \                            /    COMMIT CU   \     / register file(s)
  //              } > ROB > ROB HEAD BUFFER { COMMIT REGISTER  } > { csrs
  // issue logic /                           \ COMMIT DECODER /     \ special cases

  // Reorder Buffer (ROB)
  // --------------------
  rob #(
    .DEPTH(ROB_DEPTH)
  ) u_rob (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),
    .flush_i            (cu_mis_flush),
    .issue_valid_i      (issue_valid_i),
    .issue_ready_o      (issue_ready_o),
    .issue_data_i       (issue_data_i),
    .issue_tail_idx_o   (issue_tail_idx_o),
    .issue_rs1_rob_idx_i(issue_rs1_rob_idx_i),
    .issue_rs2_rob_idx_i(issue_rs2_rob_idx_i),
    .opfwd_rs1_valid_o  (rob_opfwd_rs1_valid),
    .opfwd_rs1_ready_o  (rob_opfwd_rs1_ready),
    .opfwd_rs1_value_o  (rob_opfwd_rs1_value),
    .opfwd_rs2_valid_o  (rob_opfwd_rs2_valid),
    .opfwd_rs2_ready_o  (rob_opfwd_rs2_ready),
    .opfwd_rs2_value_o  (rob_opfwd_rs2_value),
    .sb_mem_idx_i       (sb_mem_idx_i),
    .sb_mem_clear_o     (sb_mem_clear_o),
    .comm_valid_o       (rob_reg_valid),
    .comm_ready_i       (reg_rob_ready),
    .comm_data_o        (rob_reg_head_entry),
    .comm_head_idx_o    (rob_reg_head_idx),
    .cdb_valid_i        (cdb_valid_i),
    .cdb_data_i         (cdb_data_i),
    .cdb_ready_o        (cdb_ready_o)
  );

  // ROB HEAD BUFFER
  // ---------------
  inreg_data_t inreg_data_in, inreg_data_out;

  assign inreg_data_in.data    = rob_reg_head_entry;
  assign inreg_data_in.rob_idx = rob_reg_head_idx;

  // Input spill cell
  spill_cell_ext #(
    .DATA_T(inreg_data_t),
    .SKIP  (COMMIT_SPILL_SKIP)
  ) u_input_reg (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .flush_i    (cu_mis_flush),
    .valid_i    (rob_reg_valid),
    .ready_i    (cu_inreg_ready),
    .valid_o    (inreg_cu_valid),
    .ready_o    (reg_rob_ready),
    .data_i     (inreg_data_in),
    .data_o     (inreg_data_out),
    .buff_full_o(inreg_buff_full),
    .buff_data_o(inreg_buff_data)
  );

  // OPERANDS FORWARDING LOGIC
  // -------------------------
  // The operands required by the issuing instruction are searched for in
  // the following order (from the most recent to the oldest).
  // 1) ROB -- most recent
  // 2) Commit stage buffer 0 (spill register)
  // 3) Commit stage buffer 1
  // 4) Commit stage committing instruction buffer -- oldest
  always_comb begin : op_fwd_logic
    // RS1
    if (cdb_valid_i && cdb_data_i.rob_idx == issue_rs1_rob_idx_i) begin
      issue_rs1_value_o = cdb_data_i.res_value;
      issue_rs1_ready_o = 1'b1;
    end else if (rob_opfwd_rs1_valid) begin
      issue_rs1_ready_o = rob_opfwd_rs1_ready;
      issue_rs1_value_o = rob_opfwd_rs1_value;
    end else if (inreg_buff_full && inreg_buff_data.rob_idx == issue_rs1_rob_idx_i) begin
      issue_rs1_ready_o = 1'b1;
      issue_rs1_value_o = inreg_buff_data.data.res_value;
    end else if (inreg_cu_valid && inreg_data_out.rob_idx == issue_rs1_rob_idx_i) begin
      issue_rs1_ready_o = 1'b1;
      issue_rs1_value_o = inreg_data_out.data.res_value;
    end else if (comm_reg_valid && comm_reg_data.rob_idx == issue_rs1_rob_idx_i) begin
      issue_rs1_ready_o = 1'b1;
      issue_rs1_value_o = comm_reg_data.data.res_value;
    end else begin
      issue_rs1_ready_o = 1'b0;
      issue_rs1_value_o = '0;
    end
    // RS2
    if (cdb_valid_i && cdb_data_i.rob_idx == issue_rs2_rob_idx_i) begin
      issue_rs2_value_o = cdb_data_i.res_value;
      issue_rs2_ready_o = 1'b1;
    end else if (rob_opfwd_rs2_valid) begin
      issue_rs2_ready_o = rob_opfwd_rs2_ready;
      issue_rs2_value_o = rob_opfwd_rs2_value;
    end else if (inreg_buff_full && inreg_buff_data.rob_idx == issue_rs2_rob_idx_i) begin
      issue_rs2_ready_o = 1'b1;
      issue_rs2_value_o = inreg_buff_data.data.res_value;
    end else if (inreg_cu_valid && inreg_data_out.rob_idx == issue_rs2_rob_idx_i) begin
      issue_rs2_ready_o = 1'b1;
      issue_rs2_value_o = inreg_data_out.data.res_value;
    end else if (comm_reg_valid && comm_reg_data.rob_idx == issue_rs2_rob_idx_i) begin
      issue_rs2_ready_o = 1'b1;
      issue_rs2_value_o = comm_reg_data.data.res_value;
    end else begin
      issue_rs2_ready_o = 1'b0;
      issue_rs2_value_o = '0;
    end
  end

  // COMMITTING INSTRUCTION REGISTER
  // -------------------------------
  always_ff @(posedge clk_i or negedge rst_ni) begin : comm_reg
    if (!rst_ni) begin
      comm_reg_data   <= 'h0;
      comm_reg_csr_op <= CSR_OP_CSRRW;
      comm_reg_valid  <= 1'b0;
    end else if (comm_reg_clr) begin
      comm_reg_data   <= 'h0;
      comm_reg_csr_op <= CSR_OP_CSRRW;
      comm_reg_valid  <= 1'b0;
    end else if (comm_reg_en) begin
      comm_reg_data   <= inreg_data_out;
      comm_reg_csr_op <= cd_csr_op;
      comm_reg_valid  <= inreg_cu_valid;
    end
  end

  // COMMIT DECODER
  // --------------
  commit_decoder u_comm_decoder (
    .instruction_i  (inreg_data_out.data.instruction),
    .except_raised_i(inreg_data_out.data.except_raised),
    .comm_type_o    (cd_comm_type),
    .csr_op_o       (cd_csr_op)
  );

  // COMMIT CONTROL UNIT
  // -------------------
  // NOTE: the commit CU is a Moore FSM that receives inputs from the commit
  //       logic input register (spill cell). Since its output will only be
  //       available the next cycle, the instruction is buffered inside the
  //       'comm_reg' register above.

  // Misprediction detection
  assign inreg_cu_mispredicted = inreg_data_out.data.except_code == E_MISPREDICTION;

  // Control unit
  commit_cu u_commit_cu (
    .clk_i             (clk_i),
    .rst_ni            (rst_ni),
    .comm_type_i       (cd_comm_type),
    .mispredict_i      (inreg_cu_mispredicted),
    .comm_reg_en_o     (comm_reg_en),
    .comm_reg_clr_o    (comm_reg_clr),
    .comm_rd_sel_o     (cu_rd_sel),
    .comm_csr_sel_o    (cu_csr_sel),
    .valid_i           (inreg_cu_valid),
    .ready_o           (cu_inreg_ready),
    .res_ready_i       (inreg_data_out.data.res_ready),
    .except_code_i     (inreg_data_out.data.except_code),
    .int_rs_valid_o    (int_rs_valid_o),
    .int_rf_valid_o    (int_rf_valid_o),
    // .fp_rs_valid_o     (fp_rs_valid_o),
    // .fp_rf_valid_o     (fp_rf_valid_o),
    .csr_valid_o       (csr_valid_o),
    .csr_override_o    (cu_csr_override),
    .csr_comm_insn_o   (csr_comm_insn_o),
    .csr_addr_o        (cu_csr_addr),
    .fe_ready_i        (fe_ready_i),
    .fe_except_raised_o(fe_except_raised_o),
    .ex_mis_flush_o    (cu_mis_flush),
    .except_flush_o    (cu_except_flush),
    .issue_resume_o    (issue_resume_o)
  );

  // Exception adder
  // ---------------
  // NOTE: may be replaced with an or if mtvec.base is aligned to 64 bytes
  assign adder_op  = (csr_mtvec_i.mode == 0) ? 'h0 :
      {{(XLEN - 2 - EXCEPT_TYPE_LEN) {1'b0}}, comm_reg_data.data.except_code, 2'b00};
  assign adder_out = {csr_mtvec_i.base, 2'b00} + adder_op;

  // rd MUX
  // ------
  always_comb begin : rd_value_mux
    case (cu_rd_sel)
      COMM_RD_SEL_EXCEPT: rd_value = adder_out;
      COMM_RD_SEL_CSR:    rd_value = csr_data_i;
      default:            rd_value = comm_reg_data.data.res_value;
    endcase
  end

  // CSR MUX
  // -------
  always_comb begin : csr_mux
    unique case (cu_csr_sel)
      COMM_CSR_SEL_INSN: begin
        csr_data = {{XLEN - ILEN{1'b0}}, comm_reg_data.data.instruction};
        csr_addr = cu_csr_addr;
      end
      COMM_CSR_SEL_PC: begin
        csr_data = comm_reg_data.data.instr_pc;
        csr_addr = cu_csr_addr;
      end
      COMM_CSR_SEL_EXCEPT: begin
        csr_data = {{XLEN - EXCEPT_TYPE_LEN{1'b0}}, comm_reg_data.data.except_code};
        csr_addr = cu_csr_addr;
      end
      COMM_CSR_SEL_INT: begin
        csr_data = {1'b1, {XLEN - EXCEPT_TYPE_LEN - 1{1'b0}}, comm_reg_data.data.except_code};
        csr_addr = cu_csr_addr;
      end
      COMM_CSR_SEL_ZERO: begin
        csr_data = 'h0;
        csr_addr = cu_csr_addr;
      end
      default: begin  // select zero
        csr_data = comm_reg_data.data.res_value;
        csr_addr = comm_reg_data.data.instruction.i.imm11;
      end
    endcase
  end
  assign csr_op_o       = (cu_csr_override) ? CSR_OP_SYSTEM : comm_reg_csr_op;

  // -----------------
  // OUTPUT EVALUATION
  // -----------------

  // Data to front-end
  assign fe_except_pc_o = adder_out;

  // Data to the register file(s)
  assign rd_idx_o       = comm_reg_data.data.rd_idx;
  assign rd_value_o     = rd_value;

  // Data to CSRs
  assign csr_addr_o     = csr_addr;
  assign csr_rs1_idx_o  = comm_reg_data.data.instruction.r.rs1;
  assign csr_data_o     = csr_data;
  assign csr_rd_idx_o   = comm_reg_data.data.rd_idx;

  // Data to others
  assign ex_mis_flush_o = cu_mis_flush;
  assign except_flush_o = cu_except_flush;

  // ----------
  // ASSERTIONS
  // ----------
`ifndef SYNTHESIS
`ifndef VERILATOR
  property p_no_except;
    @(posedge clk_i) disable iff (!rst_ni) ex_mis_flush_o |=> !fe_except_raised_o
  endproperty
  a_no_except :
  assert property (p_no_except)
  else $display("WARNING: Committing exception: %s", comm_reg_data.data.except_code.name());
  // ISR address
  property p_except;
    @(posedge clk_i) disable iff (!rst_ni) fe_except_raised_o |->
      fe_except_pc_o == ((comm_reg_data.data.except_code << 2) + (csr_mtvec_i.base << 2))
  endproperty
  a_except :
  assert property (p_except);
  // Detect deadlock (watchdog timer)
  property p_watchdog;
    @(posedge clk_i) disable iff (!rst_ni) u_commit_cu.curr_state == u_commit_cu.IDLE |->
      ##[1:100] u_commit_cu.curr_state != u_commit_cu.IDLE
  endproperty
  a_jb_instr :
  assert property (p_jb_instr);
  a_watchdog :
  assert property (p_watchdog)
  else
    $display(
        "IDLE timeout | pc: %h | instr: %h",
        comm_reg_data.data.instr_pc,
        comm_reg_data.data.instruction.raw
    );
`endif  /* VERILATOR */
`endif  /* SYNTHESIS */
endmodule
