#|/bin/bash

##################################
# ----- ATTACH GDB TO QEMU ----- #
##################################
# This scripts launches a GDB debug session by connecting to the debug server
# running on QEMU at :1234. After starting the QEMU VM, it generates a GDB
# macro files and launched GDB.

# PARAMETERS
# ----------

# Directory structure
ROOT_DIR=$(realpath $(dirname $0)/..)
BUILD_DIR=$ROOT_DIR/build
TEST_DIR=$BUILD_DIR/sw/tests

# GDB macro file
GDB_CMD_FILE=$TEST_DIR/gdb.cmd

# Default executable file
EXEC_FILE=$TEST_DIR/qemu/hello.elf

# Launch QEMU
RUN_ONLY=0
LAUNCH_QEMU=0

####################################
# ----- FUNCTION DEFINITIONS ----- #
####################################

# Print usage message
print_usage () {
    [ ! "$1" = "" ] && { printf -- "\nERROR: %s\n\n" "$1" 1>&2; }
    printf -- "USAGE: $0 [OPTIONS] [SRC_DIR] [TOP_MODULE_FILE] [SIM_ARGS]\n"
    printf -- "OPTIONS:\n"
    printf -- "\n"
    printf -- "-h:      print this message and exit.\n"
    printf -- "-q:      also launch QEMU (serial won't be visible).\n"
    printf -- "-r:      only run the executable (do not start GDB).\n"
}

####################
# ----- BODY ----- #
####################

# Parse command-line options
# --------------------------
while getopts 'hqr' opt; do
    case $opt in
        h) # Print usage message
            print_usage
            exit 0
            ;;
        q) # also launch QEMU
            LAUNCH_QEMU=1
            ;;
        r) # only run the executable on QEMU
            RUN_ONLY=1
            ;;
        *) # Invalid option
            print_usage "Invalid option"
            exit 1
            ;;
    esac
done
shift $((OPTIND-1))

# Parse command-line arguments
# ----------------------------
if [ $# -gt 0 ]; then
    EXEC_FILE=$1
fi

# Launch the specified executable on QEMU
# ---------------------------------------
# Run only
if [ $RUN_ONLY -ne 0 ]; then
    qemu-system-riscv64 \
        -nographic \
        -machine \
        virt \
        -bios \
        none \
        -m \
        256M \
        -kernel \
        $EXEC_FILE

    exit 0
fi

# Debug
if [ $LAUNCH_QEMU -ne 0 ]; then
    qemu-system-riscv64 \
        -nographic \
        -machine \
        virt \
        -bios \
        none \
        -m \
        256M \
        -s \
        -S \
        -kernel \
        $EXEC_FILE &

    # Poll QEMU to check if it has been successfully launched
    QEMU_PID=$!
    kill -0 $QEMU_PID
    if [ $? -ne 0 ]; then
        printf -- "ERROR: failed to launch QEMU"
    fi
fi

# Crete GDB command file
echo "\
target remote :1234
layout asm
layout regs
break _start
break main
continue
" > $GDB_CMD_FILE

# Launch GDB
riscv64-unknown-elf-gdb -q --tui --command $GDB_CMD_FILE $EXEC_FILE

# Kill QEMU
if [ $LAUNCH_QEMU -ne 0 ]; then
    kill -15 $QEMU_PID
fi

# Exit
exit 0