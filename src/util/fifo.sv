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
// File: fifo.sv
// Author: Michele Caon
// Date: 11/07/2022

/**
 * @brief	FIFO queue
 *
 * @details	FIFO queue handled with head and tail counters.
 */

module fifo #(
    parameter type  DATA_T  = logic[8:0],
    parameter int   DEPTH   = 4
) (
    /* Clock and reset */
    input   logic       clk_i,
    input   logic       rst_n_i,
    input   logic       flush_i,

    /* Handshaking */
    input   logic       valid_i,    // from upstream hardware
    input   logic       ready_i,    // from downstream hardware
    output  logic       valid_o,    // to downstream hardware
    output  logic       ready_o,    // to upstream hardware

    /* Data */
    input   DATA_T      data_i,
    output  DATA_T      data_o
);

    // INTERNAL SIGNALS
    // ----------------

    // Head and tail counters
    logic [$clog2(DEPTH)-1:0]   head_idx, tail_idx;
    logic                       head_cnt_en, tail_cnt_en;
    logic                       head_cnt_clr, tail_cnt_clr;

    // FIFO data
    DATA_T                      data[DEPTH];
    logic                       data_valid[DEPTH];

    // FIFO control
    logic                       fifo_push, fifo_pop;

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

    // Push/pop control
    assign  fifo_push   = valid_i && ready_o;
    assign  fifo_pop    = valid_o && ready_i;

    // Counters control
    assign  head_cnt_clr    = flush_i;
    assign  tail_cnt_clr    = flush_i;
    assign  head_cnt_en     = fifo_pop;
    assign  tail_cnt_en     = fifo_push;

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
                if (fifo_push && tail_idx == i) begin
                    data_valid[i]    <= 1'b1;
                    data[i]          <= data_i;
                end else if (fifo_pop && head_idx == i) begin
                    data_valid[i]    <= 1'b0;
                end
            end
        end
    end

    // --------------
    // OUTPUT CONTROL
    // --------------

    // NOTE: output valid when head entry is valid
    //       output ready when tail entry is or will be empty
    assign  valid_o     = data_valid[head_cnt];
    assign  ready_o     = !data_valid[tail_cnt];
    assign  data_o      = data[head_cnt];

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    property p_fifo_push;
        @(posedge clk_i) disable iff (!rst_n_i || flush_i)
        valid_i && ready_o |-> ##1
        valid_o ##0
        data_valid[$past(tail_cnt)] == 1'b1 ##0
        data[$past(tail_cnt)] == $past(data_i);
    endproperty
    a_fifo_push: assert property (p_fifo_push)
    else $error("valid_o: %b | past data_valid: %b | past data: %h | past data_i: %h", valid_o, data_valid[$past(tail_cnt)], data[$past(tail_cnt)], $past(data_i));

    property p_fifo_pop;
        @(posedge clk_i) disable iff (!rst_n_i || flush_i)
        valid_o && ready_i |-> ##1
        ready_o == 1'b1 ##0
        data_valid[$past(head_cnt)] == 1'b0;
    endproperty
    a_fifo_pop: assert property (p_fifo_pop);

    property p_ready_n;
        @(posedge clk_i) disable iff (!rst_n_i || flush_i)
        !ready_i && valid_o |-> ##1
        valid_o;
    endproperty
    a_ready_n: assert property (p_ready_n);
    `endif /* SYNTHESIS */

endmodule