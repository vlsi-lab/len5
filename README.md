# LEN5-core - Active repository
![logo](/doc/logo/len5-logo-full.png)

## Contributing
Before creating a merge request with the changes that you would like to merge, launch the following target:
```bash
make check
```
This runs HDL code linting and formatting, builds the test projects from `sw/applications`/`, builds the hardware simulation model with Verilator, and runs the RTL simulation on every test application compiled with different optimization levels. If this target fails, it means that _you broke something and shall dive deeper to understand what and why_. When this is the case, an RTL simulation alongside a Spike simulation with traces enabled is good starting point.

## Quick Start
1. Compile the RTL simulation model using Verilator:
   ```bash
   make verilator-build
   ```
2. Compile the firmware:
   ```bash
   make app # PROJECT=<a directory in sw/applications>
   ```
   Alternatively, benchmarks can be run using:
   ```bash
   make run-benchmark # SUITE=embench
   ```
   Each benchmark suite, contains several tests. The available suites are:
      - [embench](https://www.embench.org/)
   
   To generate charts, run:
   ```bash
   make charts
   ```
   The output charts will be stored in the configured build directory.


3. Run the RTL simulation using Verilator
   ```bash
   make verilator-sim # optionally specify FIRMWARE|MAX_CYCLES|LOG_LEVEL|DUMP_WAVES|TRACE_WAVES
   ```
4. [*optional*] Open the waveforms with GTKWave
   ```bash
   make verilator-waves
   ```

### Simulation with the Spike ISA simulator
An application built using step 2. above can be also simulated using the Spike ISA simulator. To do this, make sure that `spike` is in your `PATH` and run:
```bash
make spike-sim
```
This starts Spike in debug mode. You can progress one instruction at a time by pressing enter, or type `help` to get a list of all the other supported actions.
> **NOTE:** platform-dependent features like the UART emulator will **NOT** work in Spike. So don't expect any output from `printf` or similar. The intended use is to help tracking down issues in the RTL by using Spike as a reference model to check the content of the register file and memory at a given point in the program execution. Remember that LEN5 is out-of-order, so don't expect its register file content to match Spike's one at any time.

It is possible to generate a full execution trace with:
```bash
make spike-trace
```
The trace is saved in `build/sim-common/spike-trace.log`.
Similarly, LEN5 testbench can dump an execution trace from the RTL simulation. This can be obtained by setting the `DUMP_TRACE` variable when calling:
```bash
make verilator-sim DUMP_TRACE=true
```
The trace is saved in `build/sim-common/sim-trace.log`

The `spike-check` target can be used to compare the trace logs from Spike and the RTL simulation and produce a summary of the differences (using `diff`). This target is also used by `make check` to verify that the simulation trace matches the one from the RTL simulation.

## TODO
- [ ] Improve this file with info and instructions
- [x] Fix RTL simulation
- [ ] Support interrupts
- [ ] Improve support for CSR instruction
- [ ] Add OBI bus bridge
- [x] Map some benchmark
- [ ] Implement multiple issue (ideally 4-way)
