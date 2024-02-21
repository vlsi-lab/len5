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
// File: len5_tb.cpp
// Author: Michele Caon
// Date: 30/01/2024

#include <cstdlib>
#include <getopt.h>
#include <verilated.h>
#include <verilated_fst_c.h>

#include "Vtb_bare.h"
#include "tb_macros.hh"

// Default parameters
#define RESET_CYCLES 10
#define BOOT_PC 0x180
#define MEM_DUMP_FILE "mem_dump.txt"
#define FST_FILENAME "logs/waves.fst"
#define MAX_SIM_TIME 1e10

// Logger
TbLogger logger;

// Simulation cycles
vluint64_t sim_cycles = 0;

// Function prototypes
void clkGen(Vtb_bare *dut);
void rstDut(Vtb_bare *dut, vluint64_t sim_time);

// Main function
int main(int argc, char **argv, char **env) {
    // TODO: parse command line arguments with getopt
    logger.setLogLvl(LOG_HIGH);

    // Create simulation context
    VerilatedContext *cntx = new VerilatedContext;
    cntx->commandArgs(argc, argv);
    cntx->traceEverOn(true);

    // Pass simulation context to the logger
    logger.setSimContext(cntx);

    // Instantiate the DUT
    Vtb_bare *dut = new Vtb_bare(cntx);

    // FST trace file
    VerilatedFstC *m_trace = new VerilatedFstC;
    dut->trace(m_trace, 10);
    m_trace->open(FST_FILENAME);

    // Print simulation configuration
    TB_CONFIG("Log level set to %u", logger.getLogLvl());
    TB_CONFIG("Boot PC: 0x%x", BOOT_PC);
    TB_CONFIG("Reset cycles: %u", RESET_CYCLES);
    TB_CONFIG("Memory dump file: %s", MEM_DUMP_FILE);
    TB_CONFIG("Max simulation time: %u", MAX_SIM_TIME);
    TB_CONFIG("FST filename: %s", FST_FILENAME);

    // Initialize the DUT
    dut->rst_ni = 0;
    dut->clk_i = 1;
    
    // Start simulation
    long unsigned int sim_time = 0;
    long unsigned int sim_cycles = 0;
    TB_LOG(LOG_LOW, "Starting simulation...");
    while (!cntx->gotFinish() && cntx->time() < MAX_SIM_TIME)
    {
        // Generate clock and reset
        rstDut(dut, cntx->time());
        clkGen(dut);

        // Evaluate simulation step
        dut->eval();

        // Dump waveforms
        m_trace->dump(cntx->time());

        // Increment simulation time
        cntx->timeInc(1);
        if (dut->clk_i == 1) sim_cycles++;
    }

    // Run post-simulation tasks
    dut->final();

    // Close FST trace file
    m_trace->close();

    // Clean up and exit
    TB_LOG(LOG_LOW, "Simulation finished.");
    delete dut;
    delete m_trace;
    delete cntx;
    return 0;
}

// Clock generator
void clkGen(Vtb_bare *dut) {
    dut->clk_i ^= 1;
}

// Reset generator
void rstDut(Vtb_bare *dut, vluint64_t sim_time) {
    dut->rst_ni = 1;
    if (sim_time > 1 && sim_time < (RESET_CYCLES << 1))
    {
        dut->rst_ni = 0;
    }
}