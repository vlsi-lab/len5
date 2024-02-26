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
#define FST_FILENAME "logs/waves.fst"
#define TRACE_FILENAME "logs/trace.log" // DO NOT CHANGE before changing in `tb_bare.sv` as well
#define MAX_SIM_TIME 1e9

// Logger
TbLogger logger;

// Simulation cycles
vluint64_t sim_cycles = 0;

// Function prototypes
void initDut(Vtb_bare *dut, uint8_t trace_en);
void clkGen(Vtb_bare *dut);
void rstDut(Vtb_bare *dut, vluint64_t sim_time);

// Main function
int main(int argc, char *argv[]) {
    // Define command line options
    const option longopts[] = {
        {"max_cycles",  required_argument, NULL, 'c'},
        {"dump_waves",  required_argument, NULL, 'w'},
        {"dump_trace",  required_argument, NULL, 't'},
        {"log_level",   required_argument, NULL, 'l'},
        {"help",        no_argument,       NULL, 'h'},
        {NULL, 0, NULL, 0}
    };

    // Parse command line options
    // --------------------------
    bool              dump_waves = false;
    bool              dump_trace = false;
    unsigned long int max_cycles = ((unsigned long int) MAX_SIM_TIME) >> 1;
    int     opt;
    while ((opt = getopt_long(argc, argv, "l:w:t:h", longopts, NULL)) >= 0) {
        switch (opt) {
            case 'c':
                max_cycles = strtoul(optarg, NULL, 0);
                break;
            case 'l':
                logger.setLogLvl(optarg);
                break;
            case 'w':
                if (!strcmp(optarg, "true") || !strcmp(optarg, "1")) {
                    dump_waves = true;
                }
                break;
            case 't':
                if (!strcmp(optarg, "true") || !strcmp(optarg, "1")) {
                    dump_trace = true;
                }
                break;
            case 'h':
                printf("Usage: %s [OPTIONS]\n", argv[0]);
                printf("Options:\n");
                printf("  -c, --max_cycles <cycles>        Set maximum simulation cycles\n");
                printf("  -l, --log_level <level>          Set log level (0-3)\n");
                printf("  -w, --dump_waves <true|false>    Enable waveform dump\n");
                printf("  -t, --dump_trace <true|false>    Enable instruction trace dump\n");
                printf("  -h, --help                       Show this help message\n");
                exit(EXIT_SUCCESS);
                break;
            default:
                // Skip SystemVerilog arguments
                fprintf(stderr, "ERROR: Unrecognized option. Use -h or --help for help\n", argv[optind]);
                exit(EXIT_FAILURE);
        }
    }

    // Create simulation context
    VerilatedContext *cntx = new VerilatedContext;
    cntx->commandArgs(argc, argv);

    // Create log directory
    Verilated::mkdir("logs");
    
    // Pass simulation context to the logger
    logger.setSimContext(cntx);

    // Instantiate the DUT
    Vtb_bare *dut = new Vtb_bare(cntx);

    // FST trace file
    if (dump_waves) cntx->traceEverOn(true);
    VerilatedFstC *m_trace = new VerilatedFstC;
    if (dump_waves) {
        dut->trace(m_trace, 10);
        m_trace->open(FST_FILENAME);
    }

    // Print simulation configuration
    TB_CONFIG("Log level set to %u", logger.getLogLvl());
    TB_CONFIG("Reset cycles: %u", RESET_CYCLES);
    TB_CONFIG("Max simulation time: %u", max_cycles);
    TB_CONFIG("Wave dump: %s", dump_waves ? "ENABLED" : "DISABLED");
    if (dump_waves) TB_CONFIG("Wave dump file: %s", FST_FILENAME);
    TB_CONFIG("Instruction trace dump: %s", dump_trace ? "ENABLED" : "DISABLED");
    if (dump_trace) TB_CONFIG("Instruction trace file: %s", TRACE_FILENAME);

    // Initialize the DUT
    initDut(dut, dump_trace);
    
    // Start simulation
    long unsigned int sim_time = 0;
    long unsigned int sim_cycles = 0;
    TB_LOG(LOG_LOW, "Starting simulation...");
    while (!cntx->gotFinish() && cntx->time() < (max_cycles << 1))
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

    // Print simulation results
    if (cntx->gotFinish()) {
        TB_SUCCESS(LOG_LOW, "Simulation completed successfully.");
    } else {
        TB_ERR("Simulation timeout expired. Exiting...");
    }

    // Clean up and exit
    m_trace->close();
    delete dut;
    delete m_trace;
    delete cntx;
    return 0;
}

// Initialize DUT
void initDut(Vtb_bare *dut, uint8_t trace_en) {
    dut->rst_ni = 0;
    dut->clk_i = 1;
    dut->trace_en_i = trace_en;
    dut->eval();
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