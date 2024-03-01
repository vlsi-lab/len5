# Copyright 2023 EPFL and Politecnico di Torino.
# Solderpad Hardware License, Version 2.1, see LICENSE.md for details.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# File: test_scheduler.py
# Author: Michele Caon
# Date: 02/11/2023
# Description: Test scheduler for throughput and power analysis

import argparse
import subprocess
import sys
import os
import re
import csv
import pandas as pd

# Kernel test class
class app_test:
    """Test class."""
    data_types = ["int32", "int16", "int8"]

    # Initialize test properties
    def __init__(self, name: str, data_type: str, num_outs: int, kernel_params: str = ""):
        self.data: dict = {}
        self.data["app_name"] = name
        if not data_type in self.data_types:
            raise ValueError("Invalid data type")
        self.data["data_type"] = data_type
        self.data["num_outs"] = num_outs
        s = name.split("-", 1)
        self.data["memory_type"] = s[0]
        self.data["kernel_name"] = s[1]
        self.data["kernel_params"] = kernel_params

    # Append additional data
    def append_data(self, data: dict):
        """Append additional data."""
        self.data.update(data)

class test_scheduler:
    """Test scheduler class."""

    # Initialize the configuration file
    def __init__(self, config_file: str):
        self.config_file = config_file
        self.tests: app_test = []
        self.report_file: str = None

    # Configuration file parser
    def config_parser(self, pwr: bool = False) -> int:
        """Parse the configuration file."""
        
        # Load test lines
        with open(self.config_file, "r") as cf:
            tests = cf.readlines()

        # Discard empty or commented lines
        tests = [t.strip() for t in tests if t.strip() and not t.startswith("#")]

        # Parse tests
        for t in tests:
            # Get the app anme, data type, and number of output samples from the first three parameters
            if pwr:
                app_name, data_type = t.split(" ")[:2]
                num_outs = 0
                # All the remaining parameters are kernel parameters
                kernel_params = " ".join(t.split(" ")[2:])
            else:
                app_name, data_type, num_outs = t.split(" ")[:3]
                num_outs = int(num_outs)
                kernel_params = " ".join(t.split(" ")[3:])

            # Create test
            self.tests.append(app_test(app_name, data_type, num_outs, kernel_params))

        # Return the number of tests
        return len(self.tests)

    # Print tests
    def print_tests(self):
        """Print the tests."""
        for t in self.tests:
            print(f"Test name: {t.data['app_name']}")
            print(f"- data type: {t.data['data_type']}")
            print(f"- kernel parameters: {t.data['kernel_params']}")
            print()


    # Build test application
    def build_test(self, test: app_test, cdefs: str = ""):
        """Build the test application."""
        try:
            subprocess.run(["make", "app", f"PROJECT={test.data['app_name']}", f"KERNEL_PARAMS={test.data['data_type']} {test.data['kernel_params']}", f"CDEFS={cdefs}"], check=True, capture_output=True)
        except subprocess.CalledProcessError as e:
            print(f"\n### ERROR: failed to build '{test.data['app_name']}'", file=sys.stderr)
            print(e.stderr.decode("utf-8"), file=sys.stderr)
            sys.exit(1)


    # Run RTL simulation with verilator and capture stdout
    def run_verilator(self, test: app_test) -> str:
        try:
            sim_out = subprocess.run(["make", "verilator-opt", "MAX_CYCLES=2000000"], check=True, capture_output=True)
        except subprocess.CalledProcessError as e:
            print(f"\n### ERROR: failed to simulate '{test.data['app_name']}'", file=sys.stderr)
            print(e.stderr.decode("utf-8"), file=sys.stderr)
            sys.exit(1)
        return sim_out.stdout.decode("utf-8")

    # Run postlayout simulation using Questasim
    def run_postlayout(self, test: app_test, sim_args: str = ""):
        arg_list = [arg for arg in sim_args.split(" ") if arg]
        try:
            subprocess.run(["make", "questasim-postlayout-run"] + arg_list, check=True)
        except subprocess.CalledProcessError as e:
            print(f"\n### ERROR: failed to simulate '{test.data['app_name']}'", file=sys.stderr)
            print(e.stderr.decode("utf-8"), file=sys.stderr)
            sys.exit(1)

    # Perform power analysis using PrimePower
    def run_primepower(self, vcd_file: str):
        try:
            subprocess.run(["make", "power-analysis", f"PWR_VCD={os.path.abspath(vcd_file)}"], check=True)
        except subprocess.CalledProcessError as e:
            print("\n### ERROR: failed to run power analysis", file=sys.stderr)
            print(e.stderr.decode("utf-8"), file=sys.stderr)
            sys.exit(1)

    # Run RTL simulations on Verilator and extract throughput metrics
    def run_throughput(self, report_dir: str, report_name: str):
        """Run throughput simulations with Verilator."""
        # Parse the configuration file
        print(f"### Parsing configuration file '{self.config_file}'...")
        num_tests = self.config_parser()
        print(f"- {num_tests} tests found")

        # Initialize report file
        report_file = os.path.join(report_dir, report_name)
        self.init_throughput_report(report_file)

        # Run tests
        curr_test = 0
        for t in self.tests:
            curr_test += 1
            print(f"### [{curr_test}/{num_tests}] - {t.data['app_name']}")
            print(f"    - data type: {t.data['data_type']}")
            print(f"    - kernel parameters: {t.data['kernel_params']}")
            
            # Build test application
            print(f"  # Building test {t.data['app_name']}...")
            self.build_test(t)

            # Simulate the application with Verilator
            print(f"  # Simulating test {t.data['app_name']} with Verilator...")
            sim_out = self.run_verilator(t)

            # Parse the simulation output
            print("  # Parsing simulation output...")
            cycles = self.parse_sim_output(sim_out)
            print(f"    - NM-Carus cycles: {cycles[0]}")
            print(f"    - NM-Caesar cycles: {cycles[1]}")
            print(f"    - CPU cycles: {cycles[2]}")
            t.append_data({
                "carus_cycles": cycles[0], 
                "caesar_cycles": cycles[1], 
                "cpu_cycles": cycles[2]
            })

            # Append simulation results to timing report
            self.add_throughput_report(t)


    # Run power simulation (Questasim + PrimePower) and extract power metrics
    def run_power(self, log_dir: str, report_dir: str, report_name: str):
        """Run power simulations with Questasim and PrimePower."""

        report_file = os.path.join(report_dir, report_name)
        self.init_power_report(report_file)

        # Parse the configuration file
        print(f"### Parsing configuration file '{self.config_file}'...")
        num_tests = self.config_parser(pwr=True)
        print(f"- {num_tests} tests found")

        # Run tests
        curr_test = 0
        for t in self.tests:
            curr_test += 1
            cdefs = "POWER_SIM"
            print(f"### [{curr_test}/{num_tests}] - {t.data['app_name']}")
            print(f"    - data type: {t.data['data_type']}")
            print(f"    - kernel parameters: {t.data['kernel_params']}")
            print(f"    - CDEFS: {cdefs}")

            # Build test application
            print(f"  # Building test {t.data['app_name']}...")
            self.build_test(t, cdefs)

            # Run post-layout simulation
            print(f"  # Simulating test {t.data['app_name']} with Questasim...")
            self.run_postlayout(t, "VCD_MODE=2")
            
            # Prepare test output directory
            out_dir = os.path.join(report_dir, t.data['app_name'])
            os.makedirs(out_dir, exist_ok=True)

            # Initialize power
            cpu_pwr = (0.0, 0.0, 0.0, 0.0)
            carus_pwr = (0.0, 0.0, 0.0, 0.0)
            caesar_pwr = (0.0, 0.0, 0.0, 0.0)

            # Check whether testing NM-Caesar or NM-Carus
            if "caesar-" in t.data['app_name']:
                # Run power analysis on the VCD file
                vcd_file = os.path.join(log_dir, "waves-0.vcd")
                print(f"  # Running power analysis on {vcd_file}...")
                self.run_primepower(vcd_file)

                # Move power report to the report directory
                pwr_csv = os.path.join("implementation", "power_analysis", "reports", "power.csv")
                pwr_csv_new = os.path.join(out_dir, f"power-{t.data['data_type']}.csv")
                os.rename(pwr_csv, pwr_csv_new)

                # Extract power consumption
                caesar_pwr = self.get_power("caesar", pwr_csv_new)

            elif "carus-" in t.data['app_name']:
                # Run power analysis on NM-Carus VCD file
                vcd_file = os.path.join(log_dir, "waves-0.vcd")
                print(f"  # Running NM-Carus power analysis on {vcd_file}...")
                self.run_primepower(vcd_file)
                pwr_csv = os.path.join("implementation", "power_analysis", "reports", "power.csv")
                pwr_csv_new = os.path.join(out_dir, f"power-carus-{t.data['data_type']}.csv")
                os.rename(pwr_csv, pwr_csv_new)
                carus_pwr = self.get_power("carus", pwr_csv_new)

                # Run power analysis on CPU VCD file
                vcd_file = os.path.join(log_dir, "waves-1.vcd")
                print(f"  # Running CPU power analysis on {vcd_file}...")
                self.run_primepower(vcd_file)
                pwr_csv = os.path.join("implementation", "power_analysis", "reports", "power.csv")
                pwr_csv_new = os.path.join(out_dir, f"power-cpu-{t.data['data_type']}.csv")
                os.rename(pwr_csv, pwr_csv_new)
                cpu_pwr = self.get_power("cpu", pwr_csv_new)

            else:
                print(f"ERROR: invalid test name '{t.data['app_name']}'", file=sys.stderr)
                sys.exit(1)

            # Report power consumption
            print(f"    - CPU power: {cpu_pwr[0]*1000:.4} mW")
            print(f"    - NM-Carus power: {carus_pwr[0]*1000:.4} mW")
            print(f"    - NM-Caesar power: {caesar_pwr[0]*1000:.4} mW")
            t.append_data({
                "cpu_pwr": cpu_pwr[0],
                "carus_pwr": carus_pwr[0],
                "carus_ctl_pwr": carus_pwr[1],
                "carus_comp_pwr": carus_pwr[2],
                "carus_mem_pwr": carus_pwr[3],
                "caesar_pwr": caesar_pwr[0],
                "caesar_ctl_pwr": caesar_pwr[1],
                "caesar_comp_pwr": caesar_pwr[2],
                "caesar_mem_pwr": caesar_pwr[3]
            })

            # Append simulation results to power report
            self.add_power_report(t)


    def get_power(self, mode: str, csv_file: str) -> (float, float, float, float):
        """Analyse power report."""
        # Cehck for valid mode
        if not mode in ["cpu", "carus", "caesar"]:
            print(f"ERROR: invalid mode '{mode}'", file=sys.stderr)
            sys.exit(1)

        # Load CSV file
        power_data = pd.read_csv(csv_file, index_col=0, header=0)
        pwr_rows = []
        if mode == "cpu":
            # Add CPU contributions from the CSV file
            pwr_rows = [
                "u_core_v_mini_mcu/cpu_subsystem_i",                            # system CPU
                "u_core_v_mini_mcu/memory_subsystem_i",                         # all SRAM banks
                "u_core_v_mini_mcu/system_bus_i",                               # system bus
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/boot_rom_i",       # Boot ROM
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/soc_ctrl_i",       # SoC control registers
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/power_manager_i",  # Power manager
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/fast_intr_ctrl_i", # fast interrupt controller
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/dma_i",            # DMA
                "u_core_v_mini_mcu/peripheral_subsystem_i/rv_plic_i",           # PLIC
            ]
            ctl_pwr_rows = []
            comp_pwr_rows = []
            mem_pwr_rows = []
        elif mode == "carus":
            # Add NM-Carus contributions from the CSV file
            pwr_rows = [
                "u_heeperator_peripherals/gen_carus_0__u_nm_carus_wrapper",     # NM-Carus
                "u_core_v_mini_mcu/cpu_subsystem_i",                            # system CPU (idle)
                "u_core_v_mini_mcu/system_bus_i",                               # system bus
                "heeperator_bus",                                               # external bus
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_0__ram_i",       # SRAM bank 0 (.text)
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_1__ram_i",       # SRAM bank 1 (.data)
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_2__ram_i",       # SRAM interleaved bank 0
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_3__ram_i",       # SRAM interleaved bank 1
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_4__ram_i",       # SRAM interleaved bank 2
                # "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_5__ram_i",     # Replaced by NM-Carus
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/boot_rom_i",       # Boot ROM
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/soc_ctrl_i",       # SoC controller
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/power_manager_i",  # Power manager
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/fast_intr_ctrl_i", # fast interrupt controller (DMA)
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/dma_i",            # DMA
                "u_core_v_mini_mcu/peripheral_subsystem_i/rv_plic_i",           # PLIC
            ]
            ctl_pwr_rows = ["carus_ctl"]
            comp_pwr_rows = ["carus_vector"]
            mem_pwr_rows = ["carus_vrf"]
        elif mode == "caesar":
            # Add NM-Caesar contributions from the CSV file
            pwr_rows = [
                "u_heeperator_peripherals/gen_caesar_0__u_nm_caesar_wrapper",   # NM-Caesar
                "u_core_v_mini_mcu/cpu_subsystem_i",                            # system CPU (idle)
                "u_core_v_mini_mcu/system_bus_i",                               # system bus
                "heeperator_bus",                                               # external bus
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_0__ram_i",       # SRAM bank 0 (.text)
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_1__ram_i",       # SRAM bank 1 (.data)
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_2__ram_i",       # SRAM interleaved bank 0
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_3__ram_i",       # SRAM interleaved bank 1
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_4__ram_i",       # SRAM interleaved bank 2
                "u_core_v_mini_mcu/memory_subsystem_i/gen_sram_5__ram_i",       # NM-Caesar replaces one bank for leakage, but leakage is 1000x lower than active power, so it's negligible
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/boot_rom_i",       # Boot ROM
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/soc_ctrl_i",       # SoC controller
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/power_manager_i",  # Power manager
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/fast_intr_ctrl_i", # fast interrupt controller (DMA)
                "u_core_v_mini_mcu/ao_peripheral_subsystem_i/dma_i",            # DMA
                "u_core_v_mini_mcu/peripheral_subsystem_i/rv_plic_i",           # PLIC
            ]
            ctl_pwr_rows = ["caesar_ctl"]
            comp_pwr_rows = ["caesar_alu"]
            mem_pwr_rows = ["caesar_mem0", "caesar_mem1"]
        # Compute power consumption
        pwr: float = 0.0
        ctl_pwr: float = 0.0
        comp_pwr: float = 0.0
        mem_pwr: float = 0.0
        for row in pwr_rows:
            pwr += power_data.loc[row, "TOTAL_POWER"]
        for row in ctl_pwr_rows:
            ctl_pwr += power_data.loc[row, "TOTAL_POWER"]
        for row in comp_pwr_rows:
            comp_pwr += power_data.loc[row, "TOTAL_POWER"]
        for row in mem_pwr_rows:
            mem_pwr += power_data.loc[row, "TOTAL_POWER"]
        return (pwr, ctl_pwr, comp_pwr, mem_pwr)


    # Parse Verilator simulation output   
    def parse_sim_output(self, sim_out: str) -> (int, int, int):
        """Parse the simulation output."""
        # Look for NM-Carus and NM-Caesar number of cycles
        carus_regex = re.compile(r"- NM-Carus kernel execution time: (\d+) cycles\n")
        caesar_regex = re.compile(r"- NM-Caesar kernel execution time: (\d+) cycles\n")
        cpu_regex = re.compile(r"CPU: (\d+)\n")
        carus_cycles = carus_regex.search(sim_out)
        caesar_cycles = caesar_regex.search(sim_out)
        cpu_cycles = cpu_regex.search(sim_out)
        if not (carus_cycles and caesar_cycles):
            print("ERROR: could not find NM-Carus and NM-Caesar cycles", file=sys.stderr)
            sys.exit(1)
        carus_cycles = int(carus_cycles.group(1))
        caesar_cycles = int(caesar_cycles.group(1))
        if cpu_cycles is None:
            cpu_cycles = 0
        else:
            cpu_cycles = int(cpu_cycles.group(1))
        return (carus_cycles, caesar_cycles, cpu_cycles)

    # Initialize throughput CSV report
    def init_throughput_report(self, report_file: str):
        """Initialize the timing report."""
        with open(report_file, "w", encoding='utf8') as rf:
            self.report_file = report_file
            writer = csv.writer(rf)
            writer.writerow([
                "Memory type",
                "Kernel",
                "Data type",
                "Output samples",
                "CPU cycles",
                "NM-Carus cycles",
                "NM-Caesar cycles",
                "Kernel parameters"
            ])

    # Add entry to throughput CSV report
    def add_throughput_report(self, t: app_test):
        """Add a test report."""
        with open(self.report_file, "a", encoding='utf8') as rf:
            writer = csv.writer(rf)
            writer.writerow([
                t.data['memory_type'],
                t.data['kernel_name'],
                t.data['data_type'],
                t.data['num_outs'],
                t.data['cpu_cycles'],
                t.data['carus_cycles'],
                t.data['caesar_cycles'],
                t.data['kernel_params']
            ])

    # Initialize power CSV report
    def init_power_report(self, report_file: str):
        """Initialize the power report."""
        with open(report_file, "w", encoding='utf8') as rf:
            self.report_file = report_file
            writer = csv.writer(rf)
            writer.writerow([
                "Memory type",
                "Kernel",
                "Data type",
                "Output samples",
                "CPU power",
                "NM-Carus power",
                "NM-Carus control power",
                "NM-Carus compute power",
                "NM-Carus memory power",
                "NM-Caesar power",
                "NM-Caesar control power",
                "NM-Caesar compute power",
                "NM-Caesar memory power",
                "Kernel parameters"
            ])

    # Add entry to power CSV report
    def add_power_report(self, t: app_test):
        """Add a test report."""
        with open(self.report_file, "a", encoding='utf8') as rf:
            writer = csv.writer(rf)
            writer.writerow([
                t.data['memory_type'],
                t.data['kernel_name'],
                t.data['data_type'],
                t.data['num_outs'],
                t.data['cpu_pwr'],
                t.data['carus_pwr'],
                t.data['carus_ctl_pwr'],
                t.data['carus_comp_pwr'],
                t.data['carus_mem_pwr'],
                t.data['caesar_pwr'],
                t.data['caesar_ctl_pwr'],
                t.data['caesar_comp_pwr'],
                t.data['caesar_mem_pwr'],
                t.data['kernel_params']
            ])

if __name__ == "__main__":
    # Command line arguments
    cmd_parser = argparse.ArgumentParser(description="Test scheduler")
    cmd_parser.add_argument("cfg", 
                            help="Configuration file")
    cmd_parser.add_argument("out_dir", 
                            help="Output directory",
                            nargs="?",
                            default=os.getcwd())
    
    # Parse command line arguments
    args = cmd_parser.parse_args()

    # Define output file path
    thr_report_file = os.path.join(args.out_dir, "throughput.csv")

    ts = test_scheduler(args.cfg)
    ts.run_timing(thr_report_file)

    sys.exit(0)
