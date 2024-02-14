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

## TODO
- [ ] Improve this file with info and instructions
- [ ] Fix RTL simulation
- [ ] Support interrupts
- [ ] Improve support for CSR instruction
- [ ] Add OBI bus bridge
- [ ] Map some benchmark
- [ ] Implement multiple issue (ideally 4-way)
