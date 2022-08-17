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
// File: fifo_nohs.sv
// Author: Michele Caon
// Date: 17/08/2022

/**
 * @brief	FIFO without handshaking
 *
 * @details	FIFO buffer without valid/ready interface. The push/pop operations
 *          are externally controlled through dedicated signals. No check is
 *          performed on the push operation: if the FIFO is full, the oldest
 *          data is overwritten, so choose the FIFO size carefully.
 */

module fifo_nohs #(
    parameter type  DATA_T  = logic[8:0],
    parameter int   DEPTH   = 4
) (
    /* Clock and reset */
    input   logic       clk_i,
    input   logic       rst_n_i,
    input   logic       flush_i,

    /* Control */
    input   logic       push_i,
    input   logic       pop_i,

    /* Data */
    input   DATA_T      data_i,
    output  DATA_T      data_o
);

    // INTERNAL SIGNALS
    // ----------------

    // Head and tail counters
    logic [$clog2(DEPTH)-1:0]   head_cnt, tail_cnt;
    logic                       head_cnt_en, tail_cnt_en;
    logic                       head_cnt_clr, tail_cnt_clr;

    // FIFO data
    DATA_T                      data[DEPTH];
    logic                       data_valid[DEPTH];

    // ----------------------
    // HEAD AND TAIL COUNTERS
    // ----------------------

    modn_counter #(
        .N (DEPTH)
    ) u_head_counter (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .en_i    (head_cnt_en   ),
        .clr_i   (head_cnt_clr  ),
        .count_o (head_cnt      ),
        .tc_o    () // not needed
    );

    modn_counter #(
        .N (DEPTH)
    ) u_tail_counter (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .en_i    (tail_cnt_en   ),
        .clr_i   (tail_cnt_clr  ),
        .count_o (tail_cnt      ),
        .tc_o    () // not needed
    );

    // -----------------
    // FIFO CONTROL UNIT
    // -----------------

    // Counters control
    assign  head_cnt_clr    = flush_i;
    assign  tail_cnt_clr    = flush_i;
    assign  head_cnt_en     = pop_i;
    assign  tail_cnt_en     = push_i;

    // -----------
    // FIFO UPDATE
    // -----------
    // NOTE: operations priority:
    // 1) push
    // 2) pop
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : fifo_update
        if (!rst_n_i) begin
            foreach (data[i]) begin
                data_valid[i]   <= 1'b0;
                data[i]         <= '0;
            end
        end else if (flush_i) begin
            foreach (data[i]) begin
                data_valid[i]   <= 1'b0;    // clearing valid is enough
            end
        end else begin
            foreach (data[i]) begin
                if (push_i && tail_cnt == i) begin
                    data_valid[i]    <= 1'b1;
                    data[i]          <= data_i;
                end else if (pop_i && head_cnt == i) begin
                    data_valid[i]    <= 1'b0;
                end
            end
        end
    end

    // --------------
    // OUTPUT CONTROL
    // --------------

    assign  data_o      = data[head_cnt];

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    property p_fifo_full;
        @(posedge clk_i) disable iff (!rst_n_i || flush_i)
        (tail_cnt == head_cnt) && data_valid[head_cnt] |-> 
        !push_i
    endproperty
    a_fifo_full: assert property (p_fifo_full);
    `endif /* SYNTHESIS */

endmodule