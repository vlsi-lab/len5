import multiprocessing
import sys
import getopt
import os
from typing import List, Dict

def benchmark_runner(num, output_queue):
    """Function to simulate work and output to stdout."""
    output = f"Worker {num} starting\n"
    sys.stdout.write(output)
    output_queue.put(output)

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



if __name__ == "__main__":
    output_queue = multiprocessing.Queue()
    processes = []
    num_processes = 5
    SUITE = "embench"

    try:
        opts, args = getopt.getopt(sys.argv[1:], "s:", ["suite="])
    except getopt.GetoptError:
        print("Usage: python benchmarks.py -s <suite>")
        sys.exit(2)
    
    for opt, arg in opts:
        if opt in ("-s", "--suite"):
            SUITE = arg

    print(get_benchmarks(SUITE))    

    # # Spawn multiple subprocesses
    # for i in range(num_processes):
    #     p = multiprocessing.Process(target=benchmark_runner, args=(i, output_queue))
    #     processes.append(p)
    #     p.start()

    # # Wait for all processes to finish
    # for p in processes:
    #     p.join()

    # # Retrieve output from the queue
    # while not output_queue.empty():
    #     output = output_queue.get()
    #     print(output, end='')

    # print("All processes are done")
