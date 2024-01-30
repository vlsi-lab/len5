#!/bin/bash

# This script generates the SystemVerilog package containing the instruction
# definitions.

ROOT_DIR=$(realpath "$(dirname $0)/../..")
CUSTOM_DIR=$ROOT_DIR/sw/opcodes/
RISCV_OPCODES_DIR=$ROOT_DIR/sw/vendor/riscv-opcodes
INSTR_PKG=$ROOT_DIR/rtl/packages/instr_pkg.sv
PKG_NAME=$(basename $INSTR_PKG .sv)

# Generate the SystemVerilog package
make -C $RISCV_OPCODES_DIR EXTENSIONS="rv_i rv32_i rv64_i rv_m rv32_m rv64_m rv_zicsr rv_system" inst.sverilog

# Move the generated package to the correct location
echo "\
// Copyright $(date +%Y) Politecnico di Torino.
// Solderpad Hardware License, Version 2.1, see LICENSE.md for details.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// File: instr_pkg.sv
// Author: Michele Caon
// Date: $(date +%d/%m/%y)
// Description: RISC-V instruction package (autogenerated)\
" > $INSTR_PKG
cat $RISCV_OPCODES_DIR/inst.sverilog >> $INSTR_PKG
sed -i "s/package riscv_instr/package $PKG_NAME/g" $INSTR_PKG

exit 0
