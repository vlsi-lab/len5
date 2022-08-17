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
// File: issue_cu.sv
// Author: Michele Caon
// Date: 17/08/2022

module issue_cu (
    input   logic       clk_i,
    input   logic       rst_n_i,
    input   logic       flush_i,

    // Issue
    input   logic       issue_stall_i,      // stall is possible
    input   logic       issue_queue_ready_i,
    
    // Commit logic
    input   logic       comm_resume_i,      // resume after stall

    // Fetch stage
    output  logic       fetch_ready_o
);
    // INTERNAL SIGNALS
    // ----------------

    // CU states
    typedef enum logic [1:0] {
        RESET,
        RUN,
        WAIT
    } cu_state_t;
    cu_state_t      curr_state, next_state;

    // ------------
    // CONTROL UNIT
    // ------------

    // State rogression
    always_comb begin : cu_state_prog
        case (curr_state)
            RESET:                  next_state  = RUN;
            RUN: begin
                if (issue_stall_i)  next_state  = WAIT;
                else                next_state  = RUN;
            end
            WAIT: begin
                if (comm_resume_i)  next_state  = RUN;
                else                next_state  = WAIT;
            end
            default:                next_state  = RESET;
        endcase
    end

    // Output evaluation
    always_comb begin : cu_out_eval
        // Default values
        fetch_ready_o   = 1'b0;

        case (curr_state)
            RESET:;
            RUN: begin
                fetch_ready_o   = issue_queue_ready_i & !issue_stall_i;   // MEALY
            end 
            WAIT:;
            default:; 
        endcase
    end

    // State update
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : cu_state_update
        if (!rst_n_i)        curr_state  <= RESET;
        else begin 
            if (flush_i)    curr_state  <= RESET;
            else            curr_state  <= next_state;
        end
    end
  
endmodule