#!/bin/bash

########################
# ----- SETTINGS ----- #
########################

# Get the LEN5 root directory
LEN5_ROOT_DIR="$(realpath --relative-to=$PWD $(dirname $(realpath $0))/..)"

# Compiler/assembler settings
ISA_STRING="rv64im"
ABI_STRING="lp64"

# File containing AWK program to construct memory file
AWK_FORMAT="${LEN5_ROOT_DIR}/scripts/awk-mem-format.txt"

####################################
# ----- FUNCTION DEFINITIONS ----- #
####################################

# Usage message
function print_usage () {
    [ $# -ne 0 ] && { printf -- "ERROR: %s\n\n" 1>&2; exit 1; }
    printf -- "USAGE: $0 [OPTIONS] SRC_FILE\n"
    printf -- "\n"
    printf -- "Compile SRC_FILE into an object file, and produce a .txt file compatible with\n"
    printf -- "the memory format expected by LEN5 testbench.\n"
    printf -- "\n"
    printf -- "OPTIONS:\n"
    printf -- "-h:      print this message and exit.\n"
    printf -- "-o NAME: write output to NAME{.o, .bin, .txt}.\n"
}

################################
# ----- PARSE PARAMETERS ----- #
################################

while getopts 'ho:' opt; do
    case $opt in
        h) # Print usage message
            print_usage
            exit 0
            ;;
        o) # Set output basename
            OUT_BASENAME=$OPTARG
            ;;

        *) # Invalid option
            print_usage "Invalid option"
            exit 1
            ;;
    esac
done
shift $((OPTIND-1))

# Check the number of parameters
if [ $# -lt 1 ]; then 
    printf -- "ERROR: no input source file provided\n"
    exit 1
fi

# Get input source file
SRC_FILE=$1
SRC_EXT="${SRC_FILE##*.}"
[ "$OUT_BASENAME" = "" ] && OUT_BASENAME=$(basename -s .${SRC_EXT} ${SRC_FILE})

# Output file names
OUT_DIR=${LEN5_ROOT_DIR}/test-files/$OUT_BASENAME
OBJ_FILE="${OUT_DIR}/${OUT_BASENAME}.o"     # object
MEM_FILE="${OUT_DIR}/${OUT_BASENAME}.mem"   # Verilog
DUMP_FILE="${OUT_DIR}/${OUT_BASENAME}.dump" # objdump
TXT_FILE="${OUT_DIR}/${OUT_BASENAME}.txt"   # text

####################
# ----- BODY ----- #
####################

# Create output directorY
mkdir -p ${OUT_DIR}

# Compile and assemble the input file without linking it
if [ "${SRC_EXT}" = "asm" -o "${SRC_EXT}" = "s" ]; then
    printf -- "Assembling '%s' into '%s'...\n" "${SRC_FILE}" "${OBJ_FILE}"
    riscv64-unknown-elf-as -march=${ISA_STRING} -mabi=${ABI_STRING} "${SRC_FILE}" -o "${OBJ_FILE}"
    [ $? -ne 0 ] && { printf -- "ERROR while compiling source file\n"; exit 1 ; }
elif [ "$SRC_EXT" = "c" ]; then
    printf -- "Compiling and assembling '%s' into '%s'...\n" "${SRC_FILE}" "${OBJ_FILE}"
    riscv64-unknown-elf-gcc -march=${ISA_STRING} -mabi=${ABI_STRING} -o "${OBJ_FILE}" -c "${SRC_FILE}"
    [ $? -ne 0 ] && { printf -- "ERROR while compiling source file\n"; exit 1 ; }
else
    printf -- "ERROR: unsupported source file format '.%s'\n" "${SRC_EXT}"
    exit 1
fi

# Generate Verilog memory map (use with $readmemh())
printf -- "Extracting .text section of '%s' into '%s'...\n" "${OBJ_FILE}" "${MEM_FILE}"
riscv64-unknown-elf-objcopy -O verilog --verilog-data-width=8 -j .text "${OBJ_FILE}" "${MEM_FILE}"
[ $? -ne 0 ] && { printf -- "ERROR while extracting .text section\n"; exit 1 ; }

# Generate objdump
printf -- "Dumping .text section of '%s' into '%s'...\n" "${OBJ_FILE}" "${DUMP_FILE}"
riscv64-unknown-elf-objdump --visualize-jumps -M numeric -M no-aliases -d -j .text ${OBJ_FILE} > ${DUMP_FILE}
[ $? -ne 0 ] && { printf -- "ERROR while dumping .text section\n"; exit 1 ; }

# Remove header and comment instruction
printf -- "Creating text version of '%s' into '%s'...\n" "${DUMP_FILE}" "${TXT_FILE}"
awk '/[ ]+[0-9a-f]+:[\t].{4}[0-9a-f]{8}/' $DUMP_FILE | awk -f "${AWK_FORMAT}" > ${TXT_FILE}

exit 0

xxd -g1 -c4 "${BIN_FILE}" | awk -n -f "${AWK_FORMAT}" > "${TXT_FILE}"
[ $? -ne 0 ] && { printf -- "ERROR while dumping .text section\n"; exit 1 ; }

# Exit with success
exit 0