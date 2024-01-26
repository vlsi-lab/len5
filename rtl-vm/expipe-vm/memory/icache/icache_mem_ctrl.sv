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
// File: icache_mem_ctrl.sv
// Author: Matteo Perotti
// Date: 29/10/2019
// Description: it set the physical commands of the memory


import len5_pkg::*;
import memory_pkg::*;

module icache_mem_ctrl (
    // From the CU
    input  icache_ctrl_e        cond_ctrl_i,    // Memory ctrl to be enabled
    // From the ctrl enable block
    input  logic                mem_ctrl_en_i,  // Enable the selected memory ctrl
    // From the replacement block
    input  icache_replace_vec_t replace_vec_i,  // The replacement vector
    // To the SSRM
    output icache_mem_ctrl_t    mem_ctrl_o      // Physical memory control
);

  localparam N_WAY = ICACHE_L1_ASSOCIATIVITY;

  always_comb begin
    // Default assignment
    mem_ctrl_o = '0;
    if (mem_ctrl_en_i) begin
      case (cond_ctrl_i)
        ReadSet: begin
          for (int k = 0; k < N_WAY; k++) begin
            mem_ctrl_o.dmem_vec[k].cs  = 1'b1;
            mem_ctrl_o.dmem_vec[k].be  = '1;
            mem_ctrl_o.tvmem_vec[k].cs = 1'b1;
            mem_ctrl_o.tvmem_vec[k].be = '1;
          end
        end
        WriteLineAndTag: begin
          for (int k = 0; k < N_WAY; k++) begin
            mem_ctrl_o.dmem_vec[k].cs  = (replace_vec_i[k]) ? 1'b1 : 1'b0;
            mem_ctrl_o.dmem_vec[k].we  = 1'b1;
            mem_ctrl_o.dmem_vec[k].be  = '1;
            mem_ctrl_o.tvmem_vec[k].cs = (replace_vec_i[k]) ? 1'b1 : 1'b0;
            mem_ctrl_o.tvmem_vec[k].we = 1'b1;
            mem_ctrl_o.tvmem_vec[k].be = '1;
          end
        end
        InvalidSet: begin
          for (int k = 0; k < N_WAY; k++) begin
            mem_ctrl_o.tvmem_vec[k].cs = 1'b1;
            mem_ctrl_o.tvmem_vec[k].we = 1'b1;
            mem_ctrl_o.tvmem_vec[k].be = '1;  // to be optimized: clear only the valid
          end
        end
      endcase
    end
  end

endmodule
