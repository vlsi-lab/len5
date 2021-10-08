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
// File: ssram.sv
// Author: Matteo Perotti
// Date: 08/09/2019
// Synchronous Static RAM with byte enables and separate r/w channels (behavioural model)

module ssram #(
  parameter NUM_WORDS = 1024,                   // power of 2
  parameter DATA_LEN = 64                       // power of 2, greater than 8
)
(
  // main
  input  logic                         clk_i,   // main clock
  // ctrl
  input  logic                         cs_i,    // chip select
  input  logic                         we_i,    // write enable
  input  logic [(DATA_LEN+7)/8-1:0]    be_i,    // byte enable*
  // data
  input  logic [$clog2(NUM_WORDS)-1:0] addr_i,  //9:0 address channel
  input  logic [DATA_LEN-1:0]          wdata_i, // write data channel
  output logic [DATA_LEN-1:0]          rdata_o  // read data channel
);

  logic [DATA_LEN-1:0] ssram_cell [NUM_WORDS];

  // the sram is synchronous
  always_ff @(posedge clk_i) begin
    // the chip is enabled
    if (cs_i) begin
      // do a synch write
      if (we_i) begin
        // write only the enabled bytes
        for (int k = 0; k < $size(be_i); k++) begin
          if (be_i[k]) begin
            // first bytes
            if (k < $size(be_i)-1) ssram_cell[addr_i][8*k+:8] <= wdata_i[8*k+:8];
            else ssram_cell[addr_i][8*k+:(DATA_LEN-8*($size(be_i)-1))] <= wdata_i[8*k+:(DATA_LEN-8*($size(be_i)-1))];
          end
        end
      end else rdata_o <= ssram_cell[addr_i];
    end else   rdata_o <= 'x;
  end

  // for other situations, the behaviour is undefined

endmodule

// * Byte Enable [N] corresponds to the Byte [N]
//   RISC-V is little endian -> Byte [0] is the LSB

