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
// File: len5_utils.svh
// Author: Michele Caon
// Date: 23/02/2024

`ifndef LEN5_UTILS_SVH
`define LEN5_UTILS_SVH

`define TOP u_datapath

// ----------
// DATA TYPES
// ----------
typedef struct packed {
  // Global metrics
  longint unsigned cpu_cycles;
  longint unsigned retired_instr;

  // Instruction stats
  longint unsigned retired_jump;
  longint unsigned retired_branch;
  longint unsigned retired_load;
  longint unsigned retired_store;

  // Memory requests
  longint unsigned instr_req;
  longint unsigned read_req;
  longint unsigned write_req;
} len5_data_t;

// ---------
// FUNCTIONS
// ---------
// Check if an instruction is committing
function bit tb_get_len5_committing();
  return `TOP.u_backend.u_commit_stage.csr_comm_insn_o != expipe_pkg::COMM_CSR_INSTR_TYPE_NONE;
endfunction: tb_get_len5_committing

// Get CPU ID (hart ID)
function logic [len5_pkg::XLEN-1:0] tb_get_len5_cpu_id();
  return `TOP.u_backend.u_csrs.mhartid;
endfunction: tb_get_len5_cpu_id

// Get committing instruction program counter
function logic [len5_pkg::XLEN-1:0] tb_get_len5_commit_pc();
  return `TOP.u_backend.u_commit_stage.comm_reg_data.data.instr_pc;
endfunction: tb_get_len5_commit_pc

// Get retiring instruction
function logic [len5_pkg::ILEN-1:0] tb_get_len5_commit_instr();
  return `TOP.u_backend.u_commit_stage.comm_reg_data.data.instruction.raw;
endfunction: tb_get_len5_commit_instr

// Get stats from LEN5
function len5_data_t tb_get_len5_data(longint unsigned mem_instr, longint unsigned mem_read, longint unsigned mem_write);
  len5_data_t data;
  data.cpu_cycles = unsigned'(`TOP.u_backend.u_csrs.mcycle);
  data.retired_instr = unsigned'(`TOP.u_backend.u_csrs.minstret);
  data.retired_jump = unsigned'(u_datapath.u_backend.u_csrs.hpmcounter3);
  data.retired_branch = unsigned'(u_datapath.u_backend.u_csrs.hpmcounter4);
  data.retired_load = unsigned'(u_datapath.u_backend.u_csrs.hpmcounter5);
  data.retired_store = unsigned'(u_datapath.u_backend.u_csrs.hpmcounter6);
  data.instr_req = mem_instr;
  data.read_req = mem_read;
  data.write_req = mem_write;
  return data;
endfunction: tb_get_len5_data

// Print LEN5 report
function void tb_print_len5_report(len5_data_t data);
  longint unsigned tot_jump_branch;
  longint unsigned tot_load_store;
  longint unsigned tot_mem;

  $display("\033[1m### EXECUTION REPORT\033[0m");
  $display(" ## retired instructions:                  %6d", data.retired_instr);
  $display("    - total CPU cycles:                    %6d", data.cpu_cycles);
  $display("    - average IPC:                         %6.2f", real'(data.retired_instr) / data.cpu_cycles);
  if (!LEN5_CSR_HPMCOUNTERS_EN) begin
    $display(" ## NOTE: extra performance counters not available since 'LEN5_CSR_HPMCOUNTERS_EN' is not defined");
  end else begin
    tot_jump_branch = data.retired_jump + data.retired_branch;
    tot_load_store = data.retired_load + data.retired_store;
    $display("  # retired jump/branch instructions:      %6d (%0.1f%%)", tot_jump_branch, real'(tot_jump_branch) * 100.0 / data.retired_instr);
    $display("    - jumps:                               %6d (%0.1f%%)", data.retired_jump, real'(data.retired_jump) * 100.0 / tot_jump_branch);
    $display("    - branches:                            %6d (%0.1f%%)", data.retired_branch, real'(data.retired_branch) * 100.0 / tot_jump_branch);
    $display("  # retired load/store instructions:       %6d (%0.1f%%)", tot_load_store, real'(tot_load_store) * 100.0 / data.retired_instr);
    $display("    - loads:                               %6d (%0.1f%%)", data.retired_load, real'(data.retired_load) * 100.0 / tot_load_store);
    $display("    - stores:                              %6d (%0.1f%%)", data.retired_store, real'(data.retired_store) * 100.0 / tot_load_store);
  end
  tot_mem = data.instr_req + data.read_req + data.write_req;
  $display(" ## memory requests:                       %6d", tot_mem);
  $display("    - instruction fetches:                 %6d (%0.1f%%)", data.instr_req, real'(data.instr_req) * 100.0 / tot_mem);
  $display("    - read requests:                       %6d (%0.1f%%)", data.read_req, real'(data.read_req) * 100.0 / tot_mem);
  $display("    - write requests:                      %6d (%0.1f%%)", data.write_req, real'(data.write_req) * 100.0 / tot_mem);
endfunction: tb_print_len5_report

`endif // LEN5_UTILS_SVH
