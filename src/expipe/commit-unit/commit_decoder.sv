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
// File: commit_decoder.sv
// Author: Michele Caon
// Date: 20/11/2019

// THIS FILE IS ONYL A TEMPLATE, THE COMMIT LOGIC IS NOT IMPLEMENTED YET, SINCE IT REQUIRES ALL THE PROCESSOR PARTS TO BE FUNCTIONAL

/* Include instruction macros */
`include "instr_macros.svh"

import expipe_pkg::*;
import csr_pkg::*;
import len5_pkg::ILEN;
import len5_pkg::OPCODE_LEN;
import len5_pkg::instr_t;

module commit_decoder 
(
    // Data from the commit logic
    input   instr_t         instruction_i,
	input   logic           except_raised_i,

    // Control to the commit logic
    output  comm_type_t     comm_type_o,
    output  csr_op_t        csr_op_o
);
    // INTERNAL SIGNALS
    // ----------------
    logic       sel_system_dec;
    comm_type_t comm_type_normal;
    comm_type_t comm_type_system;

    // --------------------
    // COMMIT DOCODER LOGIC
    // --------------------
    // Main opcode decoder
    always_comb begin: comm_decoder
        // Default
        comm_type_normal    = COMM_TYPE_NONE;
        sel_system_dec      = 1'b0;

        // Hanle exceptions
        if (except_raised_i)    comm_type_normal = COMM_TYPE_EXCEPT;

        // No exceptions raised
        else begin
            case (instruction_i.r.opcode)
                // Intructions committing to the integer RF
                // ----------------------------------------
                `OPCODE_OP_IMM,
                `OPCODE_OP_IMM_32,
                `OPCODE_OP,
                `OPCODE_OP_32,
                `OPCODE_LUI,
                `OPCODE_AUIPC,
                `OPCODE_LOAD:       comm_type_normal    = COMM_TYPE_INT_RF;

                // Store instructions
                // ------------------
                `OPCODE_STORE:      comm_type_normal    = COMM_TYPE_STORE;

                // Jump instructions
                // ----------------- 
                `OPCODE_JAL,
                `OPCODE_JALR:       comm_type_normal    = COMM_TYPE_JUMP;
                
                // Branch instructions
                // -------------------
                `OPCODE_BRANCH:     comm_type_normal    = COMM_TYPE_BRANCH;

                // SYSTEM instructions
                // -------------------
                `OPCODE_SYSTEM:     sel_system_dec      = 1'b1;

                // Fence instructions
                // ------------------
                `OPCODE_MISC_MEM:   comm_type_normal    = COMM_TYPE_FENCE;

                default:            comm_type_normal    = COMM_TYPE_EXCEPT;
            endcase
        end
    end

    // System instruction decoder
    always_comb begin : system_dec
        csr_op_o    = CSR_OP_CSRRW;
        unique case (instruction_i.i.funct3)
            // CSR INSTRUCTIONS
            `FUNCT3_CSRRW: begin
                comm_type_system    = COMM_TYPE_CSR;
                csr_op_o    = CSR_OP_CSRRW;
            end
            `FUNCT3_CSRRS: begin
                comm_type_system    = COMM_TYPE_CSR;
                csr_op_o    = CSR_OP_CSRRS;
            end
            `FUNCT3_CSRRC: begin
                comm_type_system    = COMM_TYPE_CSR;
                csr_op_o    = CSR_OP_CSRRC;
            end
            `FUNCT3_CSRRWI: begin
                comm_type_system    = COMM_TYPE_CSR;
                csr_op_o    = CSR_OP_CSRRWI;
            end
            `FUNCT3_CSRRSI: begin
                comm_type_system    = COMM_TYPE_CSR;
                csr_op_o    = CSR_OP_CSRRSI;
            end
            `FUNCT3_CSRRCI: begin
                comm_type_system    = COMM_TYPE_CSR;
                csr_op_o    = CSR_OP_CSRRCI;
            end

            `FUNCT3_ZERO: begin
                unique case ({instruction_i.r.funct7, instruction_i.r.rs2, instruction_i.r.rs1})
                    {`ECALL_IMM, `ECALL_RS1}: begin // ECALL
                        comm_type_system    = COMM_TYPE_ECALL;
                    end
                    {`EBREAK_IMM, `EBREAK_RS1}: begin // EBREAK
                        comm_type_system    = COMM_TYPE_EBREAK;
                    end
                    {`FUNCT7_MRET, `MRET_RS2, `MRET_RS1}: begin // MRET
                        comm_type_system    = COMM_TYPE_MRET;
                    end
                    {`FUNCT7_WFI, `WFI_RS2, `WFI_RS1}: begin // WFI
                        comm_type_system    = COMM_TYPE_WFI;
                    end
                    default: begin
                        comm_type_system    = COMM_TYPE_EXCEPT;
                    end
                endcase
            end
            default: comm_type_system   = COMM_TYPE_EXCEPT;
        endcase
    end

    // -----------------
    // OUTPUT EVALUATION
    // -----------------
    // Commit type MUX
    assign  comm_type_o = (sel_system_dec) ? comm_type_system : comm_type_normal;
    
endmodule
