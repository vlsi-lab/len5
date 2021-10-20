#!/bin/bash

########################
# ----- SETTINGS ----- #
########################

# Compiler/assembler settings
ISA_STRING="rv64im"

# File containing AWK program to construct memory file
AWK_FORMAT="awk-format.txt"

################################
# ----- PARSE PARAMETERS ----- #
################################

# Check the number of parameters
if [ $# -lt 1 ]; then 
    printf -- "ERROR: no input source file provided\n"
    exit 1
fi

# Get input source file
SRC_FILE=$1
SRC_EXT="${SRC_FILE##*.}"

# Object file name
OBJ_FILE="${SRC_FILE%%.*}.o"

# Assemble output file name
[ $# -gt 1 ] && BIN_FILE=$2 || BIN_FILE="${SRC_FILE%%.*}.bin"

# Assemble text file name
TXT_FILE="${BIN_FILE%%.*}.txt"

####################
# ----- BODY ----- #
####################

# Compile and assemble the input file without linking it
if [ "${SRC_EXT}" = "asm" ]; then
    printf -- "Assembling '%s' into '%s'...\n" "${SRC_FILE}" "${OBJ_FILE}"
    riscv64-unknown-elf-as -march=${ISA_STRING} "${SRC_FILE}" -o "${OBJ_FILE}"
    [ $? -ne 0 ] && { printf -- "ERROR while compiling source file\n"; exit 1 ; }
elif [ "$SRC_EXT" = "c" ]; then
    printf -- "Compiling and assembling '%s' into '%s'...\n" "${SRC_FILE}" "${OBJ_FILE}"
    riscv64-unknown-elf-gcc -march=${ISA_STRING} -o "${OBJ_FILE}" -c "${SRC_FILE}"
    [ $? -ne 0 ] && { printf -- "ERROR while compiling source file\n"; exit 1 ; }
else
    printf -- "ERROR: unsupported source file format '.%s'\n" "${SRC_EXT}"
    exit 1
fi

# Generate a binary file containing only the text section
printf -- "Extracting .text section of '%s' into '%s'...\n" "${OBJ_FILE}" "${BIN_FILE}"
riscv64-unknown-elf-objcopy -O binary -j .text "${OBJ_FILE}" "${BIN_FILE}"
[ $? -ne 0 ] && { printf -- "ERROR while extracting .text section\n"; exit 1 ; }

# If the file is not aligned on 64 bits, add a nop
BIN_SIZE=$(du -sb src/store.bin | cut -f1)
[ $(($BIN_SIZE%8)) -ne 0 ] && echo -n -e \\x13\\x00\\x00\\x00 >> ${BIN_FILE}

# Dump the assembled file to an ASCII hex file
printf -- "Dumping binary code '%s' into '%s'...\n" "${BIN_FILE}" "${TXT_FILE}"
xxd -g1 -c4 -b "${BIN_FILE}" | awk -f "${AWK_FORMAT}" > "${TXT_FILE}"
[ $? -ne 0 ] && { printf -- "ERROR while dumping .text section\n"; exit 1 ; }

# Exit with success
exit 0