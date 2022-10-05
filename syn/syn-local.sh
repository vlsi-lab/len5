#!/bin/bash

# Start synthesis locally

# Root directory
LEN5_ROOT_DIR="$(realpath $(dirname $0)/..)"
SYN_DIR=$LEN5_ROOT_DIR/syn

# Initialize Synopsys DC
source /eda/scripts/init_design_vision

# Set TERM environment variable
export TERM=xterm-256color

# Launch synthesis
cd $SYN_DIR
clear 
rm -rf work
rm -rf logs
rm -rf reports
mkdir work
mkdir logs
mkdir reports
dc_shell-xg-t -f syn.tcl

unset TERM