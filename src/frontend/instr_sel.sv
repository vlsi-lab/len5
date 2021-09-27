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
// File: instr_sel.sv
// Author: Marco Andorno
// Date: 03/10/2019

import len5_pkg::*;

module instr_sel
(
  input   var icache_out_t                cache_out_i,
  input   var icache_out_t                line_reg_i,
  input   var icache_out_t                line_bak_i,
  input   logic [ICACHE_OFFSET-1:0]   pc_i,
  input   logic [ICACHE_OFFSET-1:0]   prev_pc_i,
  input   pc_src_t                    pc_sel_i,
  input   line_src_t                  line_sel_i,

  output  logic [ILEN-1:0]            instruction_o
);

  // Logic declarations
  logic [ICACHE_OFFSET-1:0] selected_pc;
  icache_out_t selected_line;

  // PC mux
  always_comb begin
    case (pc_sel_i)
      current_pc: selected_pc = pc_i;
      prev_pc:    selected_pc = prev_pc_i;
      line_pc:    selected_pc = line_reg_i.pc[ICACHE_OFFSET+OFFSET-1:OFFSET];
      default:    selected_pc = prev_pc_i;
    endcase
  end

  // Line mux
  always_comb begin
    case (line_sel_i)
      cache_out:  selected_line = cache_out_i;
      line_reg:   selected_line = line_reg_i;
      line_bak:   selected_line = line_bak_i;
      default:    selected_line = line_reg_i;
    endcase
  end

  // Instruction mux
  assign instruction_o = selected_line.line[selected_pc];

endmodule
