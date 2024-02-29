# Copyright 2023 EPFL and Politecnico di Torino.
# Solderpad Hardware License, Version 2.1, see LICENSE.md for details.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# File: throughput-analysis.py
# Author: Michele Caon
# Date: 02/11/2023
# Description: Script to run throughput analysis on Verilator model

import argparse
import sys
import os
import test_scheduler as ts

# Parse command line arguments
cmd_parser = argparse.ArgumentParser(description="Test scheduler")
cmd_parser.add_argument("cfg", 
                        help="Configuration file")
cmd_parser.add_argument("report_csv",
                        help="Output throughput report CSV file.",
                        nargs="?",
                        default=f"{os.getcwd()}/throughput.csv")
args = cmd_parser.parse_args()

# Initialize test scheduler
report_dir = os.path.dirname(args.report_csv)
report_file = os.path.basename(args.report_csv)
sched = ts.test_scheduler(args.cfg)
sched.run_throughput(report_dir, report_file)

# Exit
sys.exit(0)
