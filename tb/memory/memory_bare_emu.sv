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
  input logic rst_ni,
  input logic instr_flush_i,

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
  import memory_pkg::*;
  import len5_pkg::*;
  import expipe_pkg::*;

  // INTERNAL SIGNALS
  // ----------------
  // Answer from the memory
  typedef struct packed {
    logic [len5_pkg::ILEN-1:0] read;           // instruction read
    logic                      except_raised;
    len5_pkg::except_code_t    except_code;
  } instr_mem_ans_t;

  typedef struct packed {
    logic [len5_pkg::BUFF_IDX_LEN-1:0] tag;            // instruction tag
    logic [len5_pkg::XLEN-1:0]         read;           // data read
    logic                              except_raised;
    len5_pkg::except_code_t            except_code;
  } dload_mem_ans_t;

  typedef struct packed {
    logic [len5_pkg::BUFF_IDX_LEN-1:0] tag;            // instruction tag
    logic                              except_raised;
    len5_pkg::except_code_t            except_code;
  } dstore_mem_ans_t;

  // Memory answer to the core
  instr_mem_ans_t                       instr_rsp;
  dload_mem_ans_t                       data_load_rsp;
  dstore_mem_ans_t                      data_store_rsp;
  logic            [len5_pkg::XLEN-1:0] instr_addr_q;
  logic            [len5_pkg::XLEN-1:0] data_load_addr_q;
  logic            [len5_pkg::XLEN-1:0] data_store_addr_q;

  // Memory object
  memory_class                          mem;
  int i_ret, dl_ret, ds_ret;  // memory emulator return value

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
    $display("[%8t] MEM EMU > Flashing memory image '%s'...", $time, mem_file_i);
    mem = new(mem_file_i);
    if (mem.LoadMem() <= 0) begin
      $fatal("Unable to load memory image");
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
          if (mem.PrintMem(mem_dump_file_i)) begin
            $fatal("[MEM EMU] Unable to dump memory content to file");
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
      i_ret                  = mem.ReadW(instr_addr_i);
      instr_pipe_reg[0].read = mem.read_word;
    end

    // Exception handling
    case (i_ret)
      0: instr_pipe_reg[0].except_raised = 1'b0;
      1: begin  // address_misaligned
        if (instr_addr_i != instr_addr_q)
          $display(
              "[%8t] MEM EMU > WARNING: misaligned INSTRUCTION access at %h", $time, instr_addr_i
          );
        instr_pipe_reg[0].except_raised = 1'b1;
        instr_pipe_reg[0].except_code   = E_I_ADDR_MISALIGNED;
      end
      2: begin  // access_fault
        if (instr_addr_i != instr_addr_q)
          $display(
              "[%8t] MEM EMU > WARNING: reading uninitialized INSTRUCTION at %h",
              $time,
              instr_addr_i
          );
        instr_pipe_reg[0].except_raised = 1'b1;
        instr_pipe_reg[0].except_code   = E_I_ACCESS_FAULT;
      end
      default: begin
        if (instr_addr_i != instr_addr_q)
          $display(
              "[%8t] MEM EMU > WARNING: unknown INSTRUCTION exception at %h", $time, instr_addr_i
          );
        instr_pipe_reg[0].except_raised = 1'b1;
        instr_pipe_reg[0].except_code   = E_UNKNOWN;
      end
    endcase
  end

  // Instruction address register
  always_ff @(posedge clk_i or negedge rst_ni) begin : instr_addr_reg
    if (!rst_ni) instr_addr_q <= '0;
    else instr_addr_q <= instr_addr_i;
  end


  // DATA LOAD REQUEST
  // -----------------
  always_ff @(posedge clk_i) begin : p_data_load_mem_req
    data_load_pipe_valid[0]             <= data_load_valid_i;
    data_load_pipe_reg[0].tag           <= data_load_tag_i;
    data_load_pipe_reg[0].read          <= 'h0;
    data_load_pipe_reg[0].except_raised <= 1'b0;
    data_load_pipe_reg[0].except_code   <= E_UNKNOWN;

    if (data_load_valid_i) begin  // Memory always ready to answer (data_load_ready_o = 1)
      data_load_addr_q <= data_load_addr_i;
      case (data_load_be_i)
        8'b0000_0001: begin
          dl_ret                     <= mem.ReadB(data_load_addr_i);
          data_load_pipe_reg[0].read <= {56'h0, mem.read_byte};
        end
        8'b0000_0011: begin
          dl_ret                     <= mem.ReadHW(data_load_addr_i);
          data_load_pipe_reg[0].read <= {48'h0, mem.read_halfword};
        end
        8'b0000_1111: begin
          dl_ret                     <= mem.ReadW(data_load_addr_i);
          data_load_pipe_reg[0].read <= {32'h0, mem.read_word};
        end
        8'b1111_1111: begin
          dl_ret                     <= mem.ReadDW(data_load_addr_i);
          data_load_pipe_reg[0].read <= mem.read_doubleword;
        end
        default: begin
          $fatal("Unsupported data load request");
        end
      endcase
    end
  end

  // Exception handling
  always_comb begin : load_exc_handling
    case (dl_ret)
      0: data_load_pipe_reg[0].except_raised = 1'b0;
      1: begin : address_misaligned
        if (data_load_pipe_valid[0] && data_load_addr_q != data_load_addr_i)
          $display(
              "[%8t] MEM EMU > WARNING: misaligned memory READ at %h", $time, data_load_addr_q
          );
        data_load_pipe_reg[0].except_raised = data_load_pipe_valid[0];
        data_load_pipe_reg[0].except_code   = E_LD_ADDR_MISALIGNED;
      end
      2: begin : access_fault
        if (data_load_pipe_valid[0] && data_load_addr_q != data_load_addr_i)
          $display(
              "[%8t] MEM EMU > WARNING: uninitialized memory READ at %h", $time, data_load_addr_q
          );
        data_load_pipe_reg[0].except_raised = data_load_pipe_valid[0];
        data_load_pipe_reg[0].except_code   = E_LD_ACCESS_FAULT;
      end
      default: begin
        if (data_load_pipe_valid[0] && data_load_addr_q != data_load_addr_i)
          $display(
              "[%8t] MEM EMU > WARNING: unknown memory READ exception at %h",
              $time,
              data_load_addr_q
          );
        data_load_pipe_reg[0].except_raised = data_load_pipe_valid[0];
        data_load_pipe_reg[0].except_code   = E_UNKNOWN;
      end
    endcase
  end

  // DATA STORE REQUEST
  // ------------------
  always_ff @(posedge clk_i) begin : p_data_store_mem_req
    data_store_pipe_valid[0]             <= data_store_valid_i;
    data_store_pipe_reg[0].tag           <= data_store_tag_i;
    data_store_pipe_reg[0].except_raised <= 1'b0;
    data_store_pipe_reg[0].except_code   <= E_UNKNOWN;

    if (data_store_valid_i && data_store_we_i) begin
      data_store_addr_q <= data_store_addr_i;
      case (data_store_be_i)
        8'b0000_0001: begin
          ds_ret <= mem.WriteB(data_store_addr_i, data_store_wdata_i[7:0]);
        end
        8'b0000_0011: begin
          ds_ret <= mem.WriteHW(data_store_addr_i, data_store_wdata_i[15:0]);
        end
        8'b0000_1111: begin
          ds_ret <= mem.WriteW(data_store_addr_i, data_store_wdata_i[31:0]);
        end
        8'b1111_1111: begin
          ds_ret <= mem.WriteDW(data_store_addr_i, data_store_wdata_i);
        end
        default: begin
          $fatal("Unsupported data store request");
        end
      endcase
    end
  end

  // Exception handling
  always_comb begin : store_exc_handling
    case (ds_ret)
      0: data_store_pipe_reg[0].except_raised = 1'b0;
      1: begin : address_misaligned
        if (data_store_pipe_valid[0] && data_store_addr_q != data_store_addr_i)
          $display(
              "[%8t] MEM EMU > WARNING: misaligned memory WRITE at %h", $time, data_store_addr_q
          );
        data_store_pipe_reg[0].except_raised = data_store_pipe_valid[0];
        data_store_pipe_reg[0].except_code   = E_ST_ADDR_MISALIGNED;
      end
      2: begin : access_fault
        if (data_store_pipe_valid[0] && data_store_addr_q != data_store_addr_i)
          $display(
              "[%8t] MEM EMU > WARNING: memory WRITE access exception at %h",
              $time,
              data_store_addr_q
          );
        data_store_pipe_reg[0].except_raised = data_store_pipe_valid[0];
        data_store_pipe_reg[0].except_code   = E_ST_ACCESS_FAULT;
      end
      default: begin
        if (data_store_pipe_valid[0] && data_store_addr_q != data_store_addr_i)
          $display(
              "[%8t] MEM EMU > WARNING: unknown memory WRITE exception at %h",
              $time,
              data_store_addr_q
          );
        data_store_pipe_reg[0].except_raised = data_store_pipe_valid[0];
        data_store_pipe_reg[0].except_code   = E_UNKNOWN;
      end
    endcase
  end

  // Memory pipeline registers
  // -------------------------
  // NOTE: These emulate high-latency memory accesses
  assign instr_pipe_valid[0] = instr_valid_i;
  assign instr_pipe_en       = instr_ready_o;
  assign data_load_pipe_en   = data_load_ready_o;
  assign data_store_pipe_en  = data_store_ready_o;

  generate
    for (genvar i = 1; i < PIPE_NUM + 1; i++) begin : gen_mem_pipe_reg
      always_ff @(posedge clk_i) begin : mem_pipe_reg
        if (!rst_ni) begin
          instr_pipe_valid[i]      <= 1'b0;
          instr_pipe_reg[i]        <= '0;
          data_load_pipe_valid[i]  <= 1'b0;
          data_load_pipe_reg[i]    <= '0;
          data_store_pipe_valid[i] <= 1'b0;
          data_store_pipe_reg[i]   <= '0;
        end else begin
          if (instr_flush_i) begin
            instr_pipe_valid[i] <= 1'b0;
            instr_pipe_reg[i]   <= '0;
          end else if (instr_pipe_en) begin
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
    .rst_ni (rst_ni),
    .flush_i(instr_flush_i),
    .valid_i(instr_pipe_valid[PIPE_NUM]),
    .ready_i(instr_ready_i),
    .valid_o(instr_valid_o),
    .ready_o(instr_ready_o),
    .data_i (instr_pipe_reg[PIPE_NUM]),
    .data_o (instr_rsp)
  );

  spill_cell_flush #(
    .DATA_T(dload_mem_ans_t),
    .SKIP  (SKIP_DATA_ANS_REG)
  ) u_data_load_out_reg (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .flush_i(1'b0),
    .valid_i(data_load_pipe_valid[PIPE_NUM]),
    .ready_i(data_load_ready_i),
    .valid_o(data_load_valid_o),
    .ready_o(data_load_ready_o),
    .data_i (data_load_pipe_reg[PIPE_NUM]),
    .data_o (data_load_rsp)
  );

  spill_cell_flush #(
    .DATA_T(dstore_mem_ans_t),
    .SKIP  (SKIP_DATA_ANS_REG)
  ) u_data_store_out_reg (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .flush_i(1'b0),
    .valid_i(data_store_pipe_valid[PIPE_NUM]),
    .ready_i(data_store_ready_i),
    .valid_o(data_store_valid_o),
    .ready_o(data_store_ready_o),
    .data_i (data_store_pipe_reg[PIPE_NUM]),
    .data_o (data_store_rsp)
  );

  // From struct instr_ans_t to output ports
  assign instr_rdata_o              = instr_rsp.read;
  assign instr_except_raised_o      = instr_rsp.except_raised;
  assign instr_except_code_o        = instr_rsp.except_code;

  // From struct dload_ans_t to output ports
  assign data_load_tag_o            = data_load_rsp.tag;
  assign data_load_rdata_o          = data_load_rsp.read;
  assign data_load_except_raised_o  = data_load_rsp.except_raised;
  assign data_load_except_code_o    = data_load_rsp.except_code;

  // From struct dstore_ans_t to output ports
  assign data_store_tag_o           = data_store_rsp.tag;
  assign data_store_except_raised_o = data_store_rsp.except_raised;
  assign data_store_except_code_o   = data_store_rsp.except_code;

endmodule
