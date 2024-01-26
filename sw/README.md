Software for LEN5
=================
This repository contains the essential files to build software for [LEN5](https://git.vlsilab.polito.it/risc-v/len5/len5-core-active).

## Included files
Both low-level software and code examples are included. In particular:
- [`src`](./src/): this directory contains LEN5 startup code (`crt0.S`), interrupt vector and exception handling routines (`irq.S`), and a ridiculously small set of system calls implemented in a ridiculously simple way (`syscall.c`).
- [`include`](./include/): the header files for the source code in `src` can be found here.
- [`test-programs`](./test-programs/): some very simple programs, meant to be a quick yet incomplete way to test LEN5. Every source file in this directory (more specifically, in `test-programs/src`) gets automagically converted into a 'test' that can be executed on the core or in QEMU (see [this](https://git.vlsilab.polito.it/risc-v/riscv-qemu-tutorial) tutorial for additional details on RISC-V emulation on QEMU).
- The [`len5-sim.ld`](len5-sim.ld) and [`len5-qemu.ld`](len5-qemu.ld) linker scripts define the memory map for LEN5 and QEMU, and shall be used to link programs targetting the core.

## Instructions

### Prerequisites
A RISC-V toolchain supporting the `rv64i` instruction set architecture (ISA) and the `lp64` application binary interface (ABI) shall be available in the `PATH`.

### Test programs
The included [`makefile`](makefile) builds a list of tests based on the basename of the source code found in `test-programs/src`. Each `test` gets compiled and linked into a LEN5 and a QEMU ELF executables. Both executables are then stripped and copied to a raw memory image that can be loaded into the main memory and executed. The [LEN5](https://git.vlsilab.polito.it/risc-v/len5/len5-core-active) repository contains the necessary scripts to automatically compile a `test` and execute and simulate it on LEN5 using Modelsim or QuestaSim. 

When called without arguments, `make` will build the low-level support software and _all_ the test programs found inside `test-programs/src`.

To build the `hello` test from `test-programs/src/hello.c`, simply use the following command:
```bash
make tests/hello
```
This command will build all the necessary files in the `build` directory.

### Build external programs
A static library containing all the support software is compiled and placed into `build/lib`. This library can be used to build external projects. To prevent GCC from optimizing out the functions defined inside the library and link to the default startup files and standard library, it is recommended to use the `--whole-archive` linker option. Refer to the included [`makefile`](makefile) for details.