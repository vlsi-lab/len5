#!/bin/bash

########################################
# ----- COMPARE EXECUTION TRACES ----- #
########################################

# Compare the Spike and simulation execution traces
# Usage: cmp-trace.sh sim_trace spike_trace

SIM_TRACE=$1
SPIKE_TRACE=$2

# Scan simulation trace line by line
# Format: 'core   <num>: <addr> (<instr>)'

# Remove all lines with '>>>>' from Spike trace file
sed -i '/>>>>/d' $SPIKE_TRACE

# Delete the first 5 lines from Spike trace
sed -i '1,5d' $SPIKE_TRACE

# Remove the 'core <num>:' part from both trace files
sed 's/core [ ]*[0-9]*: //g' $SIM_TRACE > $SIM_TRACE.tmp
sed 's/core [ ]*[0-9]*: //g' $SPIKE_TRACE > $SPIKE_TRACE.tmp

# Only keep the first two columns from both trace files
awk '{print $1, $2}' $SIM_TRACE.tmp > $SIM_TRACE.tmp2
awk '{print $1, $2}' $SPIKE_TRACE.tmp > $SPIKE_TRACE.tmp2

# Append line number to each line in both trace files
awk '{print NR, $0}' $SIM_TRACE.tmp2 > $SIM_TRACE.tmp
awk '{print NR, $0}' $SPIKE_TRACE.tmp2 > $SPIKE_TRACE.tmp
rm $SIM_TRACE.tmp2 $SPIKE_TRACE.tmp2

# Compare the two trace files
diff $SIM_TRACE.tmp $SPIKE_TRACE.tmp > $(dirname $SIM_TRACE)/trace.diff
echo "Execution trace comparison saved to $(dirname $SIM_TRACE)/trace.diff"
rm $SIM_TRACE.tmp $SPIKE_TRACE.tmp

# Print the first 10 differences
echo "First 10 differences:"
head -n 10 $(dirname $SIM_TRACE)/trace.diff
