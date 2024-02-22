# LEN5-core - Active repository
![logo](/doc/logo/len5-logo-full.png)

## Quick Start
1. Compile the RTL simulation model using Verilator:
   ```bash
   make verilator-build
   ```
2. Compile the firmware:
   ```bash
   make app # PROJECT=<a directory in sw/applications>
   ```
3. Run the RTL simulation using Verilator
   ```bash
   make verilator-sim # optionally specify FIRMWARE|MAX_CYCLES|LOG_LEVEL
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
The trace is saved in `build/spike-trace.log`.

## TODO
- [ ] Improve this file with info and instructions
- [ ] Fix RTL simulation
- [ ] Support interrupts
- [ ] Improve support for CSR instruction
- [ ] Add OBI bus bridge
- [ ] Map some benchmark
- [ ] Implement multiple issue (ideally 4-way)
