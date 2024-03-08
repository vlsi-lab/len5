#!/bin/bash

########################################
# ----- COMPARE EXECUTION TRACES ----- #
########################################

# Compare the Spike and simulation execution traces
# Usage: cmp-trace.sh sim_trace spike_trace

SIM_TRACE=$1
SPIKE_TRACE=$2

DIFF_FILE=$(dirname $SIM_TRACE)/trace.diff
SCRIPT_DIR=$(dirname $0)

# Scan simulation trace line by line
# Format: 'core   <num>: <addr> (<instr>)'
#         'core   <num>: <opt_level> <addr> (<instr>) Rd: <reg> Rd_Value: <val>'  

# Strip trace files
# -----------------
# Create stripped version of Spike trace file to match the format above
FILENAME_PATH=${SPIKE_TRACE##*/}
SPIKE_TRACE_BASE=${FILENAME_PATH%%.*}
SPIKE_TRACE_EXT=${SPIKE_TRACE##*.}
SPIKE_TRACE_STRIPPED=$(dirname $SPIKE_TRACE)/$SPIKE_TRACE_BASE-stripped.$SPIKE_TRACE_EXT

# Remove all lines with '>>>>' from Spike trace file
sed '/>>>>/d' $SPIKE_TRACE > $SPIKE_TRACE_STRIPPED
[ $? -ne 0 ] && { echo "ERROR: Failed to process $SPIKE_TRACE"; exit 1; }
echo "### Stripped Spike trace saved to $SPIKE_TRACE_STRIPPED"

# Delete the first 5 instructions from Spike trace
sed -i '1,10d' $SPIKE_TRACE_STRIPPED
[ $? -ne 0 ] && { echo "ERROR: Failed to process $SPIKE_TRACE_STRIPPED"; exit 1; }

# Remove the 'core <num>:' part from both trace files
sed 's/core [ ]*[0-9]*: //g' $SIM_TRACE > $SIM_TRACE.tmp
[ $? -ne 0 ] && { echo "ERROR: Failed to process $SIM_TRACE"; exit 1; }
sed 's/core [ ]*[0-9]*: //g' $SPIKE_TRACE_STRIPPED > $SPIKE_TRACE_STRIPPED.tmp
[ $? -ne 0 ] && { echo "ERROR: Failed to process $SPIKE_TRACE_STRIPPED"; exit 1; }

# Trace of an instruction is print on two lines
# First line : instruction commited
# Second line : commit log
# Only keep the PC, the raw instruction, the eventual destination register and its result
sed -i '1d; n; d' $SIM_TRACE.tmp
sed -i '1d; n; d' $SPIKE_TRACE_STRIPPED.tmp

awk '{if ($4=="x0" || $4=="") {print $2, $3} else {print $2, $3, $4, $5}}' $SIM_TRACE.tmp > $SIM_TRACE.tmp2
awk '{if (substr($4,1,1) == "x") {print $2, $3, $4, $5} else {print $2, $3}}' $SPIKE_TRACE_STRIPPED.tmp > $SPIKE_TRACE_STRIPPED.tmp2

# Append line number to each line in both trace files
awk '{print NR, $0}' $SIM_TRACE.tmp2 > $SIM_TRACE.tmp
awk '{print NR, $0}' $SPIKE_TRACE_STRIPPED.tmp2 > $SPIKE_TRACE_STRIPPED.tmp
# Remove every line after matching "jump pc+0", or the last instruction in Spike exit function
if grep -q "(0x0000006f)" $SIM_TRACE.tmp; then
    sed -i '/(0x0000006f)/,$d' $SIM_TRACE.tmp
else
    echo "## WARNING : No jump pc+0 found in simulation trace"
fi

if grep -q "(0x0000006f)" $SPIKE_TRACE_STRIPPED.tmp; then
    sed -i '/(0x0000006f)/,$d' $SPIKE_TRACE_STRIPPED.tmp
else
    echo "## WARNING : No jump pc+0 found in Spike trace"
fi

# Check correctness
# -----------------
# Check if the last executed instruction is the same in both traces
if [ $(wc -l $SIM_TRACE.tmp | awk '{print $1}') -lt $(wc -l $SPIKE_TRACE_STRIPPED.tmp | awk '{print $1}') ]; then
    echo " ## WARNING: simulation trace has less lines than Spike trace" >&2
else
    SPIKE_LAST_LINE=$(tail -n 1 $SPIKE_TRACE_STRIPPED.tmp | awk '{print $1}')
    SPIKE_LAST_ADDR=$(tail -n 1 $SPIKE_TRACE_STRIPPED.tmp | awk '{print $2}')
    echo " ## Last program counter in Spike trace:      $SPIKE_LAST_ADDR"
    SIM_LAST_ADDR=$(sed -n "/$SPIKE_LAST_LINE/p" $SIM_TRACE.tmp | awk '{print $2}')
    if [ -z "$SIM_LAST_ADDR" ]; then
        echo -e "\e[1;31m### ERROR: Last program counter not found in simulation trace\e[0m" >&2
    else
        echo " ## Last program counter in simulation trace: $SIM_LAST_ADDR"
        if [ "$SIM_LAST_ADDR" != "$SPIKE_LAST_ADDR" ]; then
            echo -e "\e[1;33m ## WARNING: Last program counter differs between traces\e[0m" >&2
        else
            # Remove trailing lines from simulation trace
            sed -i "$((SPIKE_LAST_LINE+1)),$ d" $SIM_TRACE.tmp
        fi
    fi
fi

# Compare the two trace files
sed -i 's/[[:space:]]*$//' $SIM_TRACE.tmp
sed -i 's/[[:space:]]*$//' $SPIKE_TRACE_STRIPPED.tmp
diff $SIM_TRACE.tmp $SPIKE_TRACE_STRIPPED.tmp > $DIFF_FILE
echo "### Execution trace comparison saved to $DIFF_FILE"

# Print comparison outcome
EXIT_CODE=0
if [ $(wc -l $DIFF_FILE | awk '{print $1}') -eq 0 ]; then
    echo -e "\e[1;32m ## SUCCESS: Execution traces match\e[0m"
else
    # Print the first 10 differences
    echo -e "\e[1;31m### ERROR: Execution traces differ\e[0m" >&2
    echo " ## First 10 differences:"
    head -n 11 $DIFF_FILE
    EXIT_CODE=1
fi

# Remove temporary files
#rm $SIM_TRACE.tmp2 $SPIKE_TRACE_STRIPPED.tmp2 $SIM_TRACE.tmp $SPIKE_TRACE_STRIPPED.tmp

exit $EXIT_CODE
