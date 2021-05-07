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
// File: icache_data_sel.sv
// Author: Matteo Perotti
// Date: 29/10/2019
// Description: select the correct data to feed the memory

//import mmm_pkg::*;
import len5_pkg::*;
import memory_pkg::*;

module icache_data_sel (
  // From the CU
  input icache_addr_src_e  icache_addr_src_i,
  // From the Front-End
  input var icache_L1_addr_t   vaddr_d_i,
  // From the vaddr register
  input var icache_L1_addr_t   vaddr_q_i,
  // From the Flush counter
  input icache_idx_addr_t  flush_addr_i,
  // To the cache
  output icache_idx_addr_t icache_addr_o,
  output logic             icache_valid_bit_o
);

  icache_idx_addr_t vaddr_d_idx, vaddr_q_idx;

  assign vaddr_d_idx = vaddr_d_i.idx;
  assign vaddr_q_idx = vaddr_q_i.idx;

  // MUX
  always_comb begin
    icache_addr_o      = vaddr_d_idx;
    icache_valid_bit_o = 1'b0;
    case (icache_addr_src_i)
      FlushCnt: begin
        icache_addr_o = flush_addr_i;
      end
      VaddrD: begin
        icache_addr_o = vaddr_d_idx;
      end
      VaddrQ: begin
        icache_addr_o = vaddr_q_idx;
        icache_valid_bit_o = 1'b1;
      end
    endcase
  end

endmodule
