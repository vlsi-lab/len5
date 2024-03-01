import argparse
import multiprocessing
import sys
import getopt
import os
import subprocess
import time
from typing import List, Dict

PATIENCE=120
OPT = None

def benchmark_runner(num, suite, output_queue):
    """Function to simulate work and output to stdout."""
    output_tuple = (num, "")
    BUILD_DIR = os.path.join(os.getcwd(), f"build")

    # Source toolchain
    command = "source /software/scripts/init_len5"
    subprocess.run(command, shell=True, capture_output=True, text=True)

    # First compile the benchmark
    command = f"make benchmark COPT=-O{OPT} BUILD_DIR={BUILD_DIR} BENCHMARK={num} SUITE={suite}"
    result = subprocess.run(command, capture_output=True, text=True, shell=True)

    # Basic error handling
    if (result.returncode != 0):
        sys.stdout.write(result.stderr)
        return

    # Then run the simulation
    command = f"make verilator-opt BUILD_DIR={BUILD_DIR} MAX_CYCLES=10000000000"
    result = subprocess.run(command, capture_output=True, text=True, shell=True, timeout=PATIENCE)

    # Basic error handling
    if (result.returncode != 0):
        sys.stdout.write(result.stderr)
        return
    
    output_tuple = (num, result.stdout)

    # Store the output in the queue
    output_queue.put(output_tuple)

    return

def get_benchmarks(suite) -> List[str]:
    """Reads the directories present in the benchmarks directory."""
    cwd = os.getcwd()
    benchmarks_dir = os.path.join(cwd, "sw/benchmarks", suite)

    if (suite == "embench"):
        benchmarks_dir = os.path.join(benchmarks_dir, "src")

    if not os.path.exists(benchmarks_dir):
        print(f"Error: {benchmarks_dir} does not exist")
        sys.exit(2)
    else:
        benchmarks =  os.listdir(benchmarks_dir) 
        
        return benchmarks

def parse_retired_instructions(stdout) -> int:
    # Find the line containing "Instructions: "
    start_index = stdout.find("Instructions: ")
    if start_index == -1:
        return 0  # Return 0 if the line is not found

    # Extract the substring containing the number of instructions
    start_index += len("Instructions: ")
    end_index = stdout.find("\n", start_index)
    instructions_str = stdout[start_index:end_index].strip('"')
    # Convert the extracted substring to an integer and return it
    try:
        instructions = int(instructions_str)
        return instructions
    except ValueError:
        return 0  # Return 0 if conversion fails

def parse_cycles(stdout) -> int:
    # Find the line containing "Cycles: "
    start_index = stdout.find("Cycles: ")
    if start_index == -1:
        return 0  # Return 0 if the line is not found

    # Extract the substring containing the number of cycles
    start_index += len("Cycles: ")
    end_index = stdout.find("\n", start_index)
    cycles_str = stdout[start_index:end_index].strip('"')

    # Convert the extracted substring to an integer and return it
    try:
        cycles = int(cycles_str)
        return cycles
    except ValueError:
        return 0  # Return 0 if conversion fails

def init_table() -> Dict[str, Dict]:
    """Initializes a dictionary to store the results of the benchmarks."""
    table = {}

    return table

def update_table(table, benchmark, instructions, cycles):
    """Updates the table with the results of a benchmark."""
    if benchmark not in table:
        table[benchmark] = {}

    table[benchmark]["instructions"] = instructions
    table[benchmark]["cycles"] = cycles
    table[benchmark]["ipc"] = instructions / cycles

    return table

def print_table_to_file(table, suite):
    """Prints the table to a file."""
    cwd = os.getcwd()
    output_dir = os.path.join(cwd, "sw/benchmarks", suite, "output")
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    output_file = os.path.join(output_dir, "results.txt")
    with open(output_file, "w") as file:
        for benchmark, results in table.items():
            file.write(f"{benchmark}:\t")
            file.write(f"Instructions: {results['instructions']}\t")
            file.write(f"Cycles: {results['cycles']}\t")
            file.write(f"IPC: {results['ipc'] : .2f}\n")
            file.write(80*"-"+ "\n")

def print_table_to_file_csv(table, suite):
    """Prints the table to a file."""
    cwd = os.getcwd()
    output_dir = os.path.join(cwd, "sw/benchmarks", suite, "output")
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    output_file = os.path.join(output_dir, "benchmarks.csv")

    with open(output_file, "w") as file:
        file.write(f"Benchmark,Instructions,Cycles,IPC\n")
        for benchmark, results in table.items():
            file.write(f"{benchmark},")
            file.write(f"{results['instructions']},")
            file.write(f"{results['cycles']},")
            file.write(f"{results['ipc'] : .2f}\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Benchmark runner for LEN5")
    parser.add_argument("-O",
                        help="Benchmark Optimization level")
    parser.add_argument("-P",
                        help="Timeout for the simulation of each benchmark")
    parser.add_argument("-s",
                        help="Benchmark suite name")

    args = parser.parse_args()

    if (not args.O):
        print("Optimization level MUST be explicitly set. Use -O <level> to set it.")
        sys.exit(2)
    else:
        OPT = args.O
    
    if (not args.s):
        print("Usage: python benchmarks.py -s <suite>")
        sys.exit(2)
    else:
        SUITE = args.s

    if (args.P):
        PATIENCE = int(args.P)

    output_queue = multiprocessing.Queue()
    processes = []
    SUITE = "embench"

    table = init_table()

    
    benchmarks = get_benchmarks(SUITE)

    # Spawn multiple subprocesses
    for i in benchmarks:
        print(f"Running benchmark {i}")
        try:
            benchmark_runner(i, SUITE, output_queue)

            output = output_queue.get()
            print(f"Benchmark {output[0]} finished")
            update_table(table, output[0],
                        parse_retired_instructions(output[1]),
                        parse_cycles(output[1]))

            # Print updated table to file
            print_table_to_file(table, SUITE)
            print_table_to_file_csv(table, SUITE)
        except Exception as e:
            # If benchmark crashes, don't add to the table
            print(f"Exception: {i}: {e}")
            continue