import os
import shutil
import sys
from typing import List, Dict

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

def copy_directories(dest_dir_b):
    # Iterate through all directories in src_dir_a
    EMBENCH_PATH = "sw/benchmarks/embench"
    XHEEP_PATH = "sw/applications"

    for dir in get_benchmarks("embench"):
        # Extract the directory name
        dirpath = os.path.join(os.getcwd(), EMBENCH_PATH, "src", dir)
        dir_name = os.path.basename(dirpath)
        
        # Define source and destination directories
        src_subdir_x = dirpath
        src_support = os.path.join(EMBENCH_PATH, 'support')
        dest_subdir_x = os.path.join(dest_dir_b, XHEEP_PATH, dir_name)
        
        # If src_subdir_x exists, copy its content to dest_subdir_x
        if os.path.exists(src_subdir_x):
            dest_subdir_x_exists = os.path.exists(dest_subdir_x)
            if not dest_subdir_x_exists:
                os.makedirs(dest_subdir_x)
            for item in os.listdir(src_subdir_x):
                src_item = os.path.join(src_subdir_x, item)
                dest_item = os.path.join(dest_subdir_x, item)
                if os.path.isfile(src_item):
                    shutil.copy(src_item, dest_item)
                elif os.path.isdir(src_item) and not os.path.exists(dest_item):
                    shutil.copytree(src_item, dest_item)
                    
            # Copy content of A/support/* to B/src/x
            if os.path.exists(src_support) and not dest_subdir_x_exists:
                for item in os.listdir(src_support):
                    src_item = os.path.join(src_support, item)
                    dest_item = os.path.join(dest_subdir_x, item)
                    if os.path.isfile(src_item):
                        shutil.copy(src_item, dest_item)
                    elif os.path.isdir(src_item) and not os.path.exists(dest_item):
                        shutil.copytree(src_item, dest_item)

# Example usage:
if __name__ == "__main__":
    dest_dir_b = sys.argv[1] # Path to the xheep applications directory
    copy_directories(dest_dir_b)
    print("Directories copied successfully.")
