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
// File: memory_bare_emu.sv
// Author: Michele Caon
// Date: 01/08/2022

`include "memory_class.svh"

module memory_bare_emu #(
  parameter int unsigned DUMP_PERIOD = 0,  // cycles, zero to disable
  parameter int unsigned PIPE_NUM = 0,  // number of pipeline registers
  parameter bit SKIP_INS_ANS_REG = 0,  // instruction from memory is directly passed to fetch
  parameter bit SKIP_DATA_ANS_REG = 0  // data from memory is directly passed to LSU
) (
  input logic clk_i,
  input logic rst_n_i,
  input logic flush_i,

  input string mem_file_i,
  input string mem_dump_file_i,

  // Instruction  port (read-only)
  input  logic                                        instr_valid_i,
  output logic                                        instr_valid_o,
  output logic                                        instr_ready_o,
  input  logic                                        instr_ready_i,
  input  logic                   [len5_pkg::XLEN-1:0] instr_addr_i,
  output logic                   [len5_pkg::ILEN-1:0] instr_rdata_o,
  output logic                                        instr_except_raised_o,
  output len5_pkg::except_code_t                      instr_except_code_o,

  // Load port interface
  input  logic                                                data_load_valid_i,
  output logic                                                data_load_valid_o,
  output logic                                                data_load_ready_o,
  input  logic                                                data_load_ready_i,
  input  logic                   [        len5_pkg::XLEN-1:0] data_load_addr_i,
  input  logic                   [                       7:0] data_load_be_i,
  input  logic                   [len5_pkg::BUFF_IDX_LEN-1:0] data_load_tag_i,
  output logic                   [        len5_pkg::XLEN-1:0] data_load_rdata_o,
  output logic                   [len5_pkg::BUFF_IDX_LEN-1:0] data_load_tag_o,
  output logic                                                data_load_except_raised_o,
  output len5_pkg::except_code_t                              data_load_except_code_o,

  // Store port interface
  input  logic                                                data_store_valid_i,
  output logic                                                data_store_valid_o,
  output logic                                                data_store_ready_o,
  input  logic                                                data_store_ready_i,
  input  logic                                                data_store_we_i,
  input  logic                   [        len5_pkg::XLEN-1:0] data_store_addr_i,
  input  logic                   [len5_pkg::BUFF_IDX_LEN-1:0] data_store_tag_i,
  input  logic                   [                       7:0] data_store_be_i,
  input  logic                   [        len5_pkg::XLEN-1:0] data_store_wdata_i,
  output logic                   [len5_pkg::BUFF_IDX_LEN-1:0] data_store_tag_o,
  output logic                                                data_store_except_raised_o,
  output len5_pkg::except_code_t                              data_store_except_code_o
);

  import len5_config_pkg::*;
  import memory_ans_pkg::*;
  import memory_pkg::*;
  import len5_pkg::*;
  import expipe_pkg::*;

  // INTERNAL SIGNALS
  // ----------------
  // Instruction and data memory
  memory_class i_mem, d_mem;  // memory objects (the memory array itself is a static member)
  int i_ret, dl_ret, ds_ret;  // memory emulator return value

  // Memory answer to the core
  instr_mem_ans_t  instr_ans_o;
  dload_mem_ans_t  data_load_ans_o;
  dstore_mem_ans_t data_store_ans_o;

  // Pipeline registers
  logic            instr_pipe_en;
  logic            instr_pipe_valid     [PIPE_NUM+1];
  instr_mem_ans_t  instr_pipe_reg       [PIPE_NUM+1];

  logic            data_load_pipe_en;
  logic            data_load_pipe_valid [PIPE_NUM+1];
  dload_mem_ans_t  data_load_pipe_reg   [PIPE_NUM+1];

  logic            data_store_pipe_en;
  logic            data_store_pipe_valid[PIPE_NUM+1];
  dstore_mem_ans_t data_store_pipe_reg  [PIPE_NUM+1];

  // Memory initialization
  // ---------------------
  initial begin
    $display($sformatf("Flashing memory image '%s'...", mem_file_i));
    i_mem = new(mem_file_i);
    d_mem = new(mem_file_i);
    if (i_mem.LoadMem() <= 0) begin
      $fatal("Unable to load instruction memory");
    end
  end

  // Memory dump
  // -----------
  // Dump the memory content in each cycle
  generate
    if (DUMP_PERIOD > 0) begin : gen_mem_dump
      initial begin
        while (1) begin
          repeat (DUMP_PERIOD) @(posedge clk_i);
          if (i_mem.PrintMem(mem_dump_file_i)) begin
            $fatal("Unable to dump memory content to file");
          end
        end
      end
    end
  endgenerate

  // INSTRUCTION REQUEST
  // -------------------
  always_comb begin : p_ins_mem_req
    instr_pipe_reg[0].read          = 'h0;
    instr_pipe_reg[0].except_raised = 1'b0;
    instr_pipe_reg[0].except_code   = E_UNKNOWN;

    if (instr_valid_i) begin  // Memory always ready to answer (instr_ready_o = 1)
      i_ret                  = i_mem.ReadW(instr_addr_i);
      instr_pipe_reg[0].read = i_mem.read_word;
    end

    // Exception handling
    case (i_ret)
      0: instr_pipe_reg[0].except_raised = 1'b0;
      1: begin  // address_misaligned
        instr_pipe_reg[0].except_raised = 1'b1;
        instr_pipe_reg[0].except_code   = E_I_ADDR_MISALIGNED;
      end
      2: begin  // access_fault
        instr_pipe_reg[0].except_raised = 1'b1;
        instr_pipe_reg[0].except_code   = E_I_ACCESS_FAULT;
      end
      default: begin
        instr_pipe_reg[0].except_raised = 1'b1;
        instr_pipe_reg[0].except_code   = E_UNKNOWN;
      end
    endcase
  end


  // DATA LOAD REQUEST
  // ------------
  always_ff @(negedge clk_i) begin : p_data_load_mem_req
    data_load_pipe_reg[0].tag           <= data_load_tag_i;
    data_load_pipe_reg[0].read          <= 'h0;
    data_load_pipe_reg[0].except_raised <= 1'b0;
    data_load_pipe_reg[0].except_code   <= E_UNKNOWN;

    if (data_load_valid_i) begin  // Memory always ready to answer (data_load_ready_o = 1)
      // Load the whole doubleword, then LEN5 internally select the wanted bytes
      dl_ret                     <= d_mem.ReadDW(data_load_addr_i);
      data_load_pipe_reg[0].read <= d_mem.read_doubleword;

      // Exception handling
      case (dl_ret)
        0: data_load_pipe_reg[0].except_raised <= 1'b0;
        1: begin : address_misaligned
          data_load_pipe_reg[0].except_raised <= 1'b1;
          data_load_pipe_reg[0].except_code   <= E_LD_ADDR_MISALIGNED;
        end
        2: begin : access_fault
          //`ifndef MEM_EMU_RAISE_READ_ACCESS_FAULT
          //          data_ans.except_raised <= 1'b0;
          //          data_ans.value         <= '0;
          //`else
          data_load_pipe_reg[0].except_raised <= 1'b1;
          data_load_pipe_reg[0].except_code   <= E_LD_ACCESS_FAULT;
          //`endif  /* MEM_EMU_RAISE_READ_ACCESS_FAULT */
        end
        default: begin
          data_load_pipe_reg[0].except_raised <= 1'b1;
          data_load_pipe_reg[0].except_code   <= E_UNKNOWN;
        end
      endcase
    end
  end

  // DATA STORE REQUEST
  // ------------
  always_ff @(negedge clk_i) begin : p_data_store_mem_req
    data_store_pipe_reg[0].tag           <= data_store_tag_i;
    data_store_pipe_reg[0].except_raised <= 1'b0;
    data_store_pipe_reg[0].except_code   <= E_UNKNOWN;
    if (data_store_valid_i && data_store_we_i) begin
      case (data_store_be_i)
        8'b0000_0001: begin
          d_mem.WriteB(data_store_addr_i, data_store_wdata_i[7:0]);
        end
        8'b0000_0011: begin
          ds_ret <= d_mem.WriteHW(data_store_addr_i, data_store_wdata_i[15:0]);
        end
        8'b0000_1111: begin
          ds_ret <= d_mem.WriteW(data_store_addr_i, data_store_wdata_i[31:0]);
        end
        8'b1111_1111: begin
          ds_ret <= d_mem.WriteDW(data_store_addr_i, data_store_wdata_i);
        end
        default: begin
          $fatal("Unsupported data store request");
        end
      endcase
    end
    // Exception handling
    case (ds_ret)
      0: data_store_pipe_reg[0].except_raised <= 1'b0;
      1: begin : address_misaligned
        data_store_pipe_reg[0].except_raised <= 1'b1;
        data_store_pipe_reg[0].except_code   <= E_ST_ADDR_MISALIGNED;
      end
      2: begin : access_fault
        //`ifndef MEM_EMU_RAISE_READ_ACCESS_FAULT
        //          data_ans.except_raised <= 1'b0;
        //          data_ans.value         <= '0;
        //`else
        data_store_pipe_reg[0].except_raised <= 1'b1;
        data_store_pipe_reg[0].except_code   <= E_ST_ACCESS_FAULT;
        //`endif  /* MEM_EMU_RAISE_READ_ACCESS_FAULT */
      end
      default: begin
        data_store_pipe_reg[0].except_raised <= 1'b1;
        data_store_pipe_reg[0].except_code   <= E_UNKNOWN;
      end
    endcase
  end

  // Memory pipeline registers
  // -------------------------
  // NOTE: These emulate high-latency memory accesses
  assign instr_pipe_valid[0]      = instr_valid_i;
  assign instr_pipe_en            = instr_ready_o;

  assign data_load_pipe_valid[0]  = data_load_valid_i;
  assign data_load_pipe_en        = data_load_ready_o;

  assign data_store_pipe_valid[0] = data_store_valid_i;
  assign data_store_pipe_en       = data_store_ready_o;

  generate
    for (genvar i = 1; i < PIPE_NUM + 1; i++) begin : gen_mem_pipe_reg
      always_ff @(posedge clk_i) begin : mem_pipe_reg
        if (!rst_n_i) begin
          instr_pipe_valid[i]      <= 1'b0;
          instr_pipe_reg[i]        <= '0;
          data_load_pipe_valid[i]  <= 1'b0;
          data_load_pipe_reg[i]    <= '0;
          data_store_pipe_valid[i] <= 1'b0;
          data_store_pipe_reg[i]   <= '0;
        end else if (flush_i) begin
          instr_pipe_valid[i]      <= 1'b0;
          instr_pipe_reg[i]        <= '0;
          data_load_pipe_valid[i]  <= 1'b0;
          data_load_pipe_reg[i]    <= '0;
          data_store_pipe_valid[i] <= 1'b0;
          data_store_pipe_reg[i]   <= '0;
        end else begin
          if (instr_pipe_en) begin
            instr_pipe_valid[i] <= instr_pipe_valid[i-1];
            instr_pipe_reg[i]   <= instr_pipe_reg[i-1];
          end
          if (data_load_pipe_en) begin
            data_load_pipe_valid[i] <= data_load_pipe_valid[i-1];
            data_load_pipe_reg[i]   <= data_load_pipe_reg[i-1];
          end
          if (data_store_pipe_en) begin
            data_store_pipe_valid[i] <= data_store_pipe_valid[i-1];
            data_store_pipe_reg[i]   <= data_store_pipe_reg[i-1];
          end
        end
      end
    end
  endgenerate

  // Output registers
  // ----------------
  spill_cell_flush #(
    .DATA_T(instr_mem_ans_t),
    .SKIP  (SKIP_INS_ANS_REG)
  ) u_ins_out_reg (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .flush_i(flush_i),
    .valid_i(instr_pipe_valid[PIPE_NUM]),
    .ready_i(instr_ready_i),
    .valid_o(instr_valid_o),
    .ready_o(instr_ready_o),
    .data_i (instr_pipe_reg[PIPE_NUM]),
    .data_o (instr_ans_o)
  );

  spill_cell_flush #(
    .DATA_T(dload_mem_ans_t),
    .SKIP  (SKIP_DATA_ANS_REG)
  ) u_data_load_out_reg (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .flush_i(flush_i),
    .valid_i(data_load_pipe_valid[PIPE_NUM]),
    .ready_i(data_load_ready_i),
    .valid_o(data_load_valid_o),
    .ready_o(data_load_ready_o),
    .data_i (data_load_pipe_reg[PIPE_NUM]),
    .data_o (data_load_ans_o)
  );

  spill_cell_flush #(
    .DATA_T(dstore_mem_ans_t),
    .SKIP  (SKIP_DATA_ANS_REG)
  ) u_data_store_out_reg (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .flush_i(flush_i),
    .valid_i(data_store_pipe_valid[PIPE_NUM]),
    .ready_i(data_store_ready_i),
    .valid_o(data_store_valid_o),
    .ready_o(data_store_ready_o),
    .data_i (data_store_pipe_reg[PIPE_NUM]),
    .data_o (data_store_ans_o)
  );

  // From struct instr_ans_t to output ports
  assign instr_rdata_o              = instr_ans_o.read;
  assign instr_except_raised_o      = instr_ans_o.except_raised;
  assign instr_except_code_o        = instr_ans_o.except_code;

  // From struct dload_ans_t to output ports
  assign data_load_tag_o            = data_load_ans_o.tag;
  assign data_load_rdata_o          = data_load_ans_o.read;
  assign data_load_except_raised_o  = data_load_ans_o.except_raised;
  assign data_load_except_code_o    = data_load_ans_o.except_code;

  // From struct dstore_ans_t to output ports
  assign data_store_tag_o           = data_store_ans_o.tag;
  assign data_store_except_raised_o = data_store_ans_o.except_raised;
  assign data_store_except_code_o   = data_store_ans_o.except_code;

endmodule
