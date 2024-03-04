#!/bin/bash

########################################
# ----- COMPARE EXECUTION TRACES ----- #
########################################

# Compare the Spike and simulation execution traces
# Usage: cmp-trace.sh sim_trace spike_trace

SIM_TRACE=$1
SPIKE_TRACE=$2

DIFF_FILE=$(dirname $SIM_TRACE)/trace.diff

# Scan simulation trace line by line
# Format: 'core   <num>: <addr> (<instr>)'

# Strip trace files
# -----------------
# Create stripped version of Spike trace file to match the format above
SPIKE_TRACE_BASE=$(basename ${SPIKE_TRACE%%.*})
SPIKE_TRACE_EXT=${SPIKE_TRACE##*.}
SPIKE_TRACE_STRIPPED=$(dirname $SPIKE_TRACE)/$SPIKE_TRACE_BASE-stripped.$SPIKE_TRACE_EXT

# Remove all lines with '>>>>' from Spike trace file
sed '/>>>>/d' $SPIKE_TRACE > $SPIKE_TRACE_STRIPPED
[ $? -ne 0 ] && { echo "ERROR: Failed to process $SPIKE_TRACE"; exit 1; }
echo "### Stripped Spike trace saved to $SPIKE_TRACE_STRIPPED"

# Delete the first 5 lines from Spike trace
sed -i '1,5d' $SPIKE_TRACE_STRIPPED
[ $? -ne 0 ] && { echo "ERROR: Failed to process $SPIKE_TRACE_STRIPPED"; exit 1; }

# Remove the 'core <num>:' part from both trace files
sed 's/core [ ]*[0-9]*: //g' $SIM_TRACE > $SIM_TRACE.tmp
[ $? -ne 0 ] && { echo "ERROR: Failed to process $SIM_TRACE"; exit 1; }
sed 's/core [ ]*[0-9]*: //g' $SPIKE_TRACE_STRIPPED > $SPIKE_TRACE_STRIPPED.tmp
[ $? -ne 0 ] && { echo "ERROR: Failed to process $SPIKE_TRACE_STRIPPED"; exit 1; }

# Only keep the first two columns from both trace files
awk '{print $1, $2}' $SIM_TRACE.tmp > $SIM_TRACE.tmp2
awk '{print $1, $2}' $SPIKE_TRACE_STRIPPED.tmp > $SPIKE_TRACE_STRIPPED.tmp2

# Append line number to each line in both trace files
awk '{print NR, $0}' $SIM_TRACE.tmp2 > $SIM_TRACE.tmp
awk '{print NR, $0}' $SPIKE_TRACE_STRIPPED.tmp2 > $SPIKE_TRACE_STRIPPED.tmp

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
rm $SIM_TRACE.tmp2 $SPIKE_TRACE_STRIPPED.tmp2 $SIM_TRACE.tmp $SPIKE_TRACE_STRIPPED.tmp

exit $EXIT_CODE
