#!/bin/bash

# Check for required arguments
if [ $# -ne 3 ]; then
  echo "Usage: $0 <benchmark_suite> <benchmark_tests> <max_cycles>"
  exit 1
fi

BENCHMAKR_SUITE=$1
BENCHMARK_DIR_PATH=$2
MAX_CYCLES=$3
 
# Get benchmark tests
BENCHMARK_DIR_NAME=$(basename $BENCHMARK_DIR_PATH)
BENCHMARK_TESTS=$(find $BENCHMARK_DIR_PATH -type d -exec basename {} \; | sed "s/^${BENCHMARK_DIR_NAME}//")

# Creation of log file
BUILD_DIR=$(realpath .)/build
CHECK_LOG=$BENCHMAKR_SUITE-check.log
CHECK_LOG=$BUILD_DIR/sim-common/$CHECK_LOG
# Check log header
echo -e "### Log check of benchmark suite $BENCHMAKR_SUITE" > $CHECK_LOG

# Optimization levels
COPT_LEVELS="-O0 -O1 -O2"

# Loop tests informations
LOOP_COUNT=1
FAIL_COUNT=0
COPT_LEVELS_COUNT=$(echo $COPT_LEVELS | wc -w)
BENCHMARK_TESTS_COUNT=$(echo $BENCHMARK_TESTS | wc -w)
TOTAL_TESTS=$(($COPT_LEVELS_COUNT * $BENCHMARK_TESTS_COUNT))

# Loop through optimization levels
for COPT in $COPT_LEVELS; do 
# Loop through benchmark tests
  for B in $BENCHMARK_TESTS; do 
    echo -e "\e[1;37;43mRunning benchmark "$B" with COPT $COPT\e[0m";
    echo "Test number/Total number of tests : $LOOP_COUNT/$TOTAL_TESTS"
    LOOP_COUNT=$(expr $LOOP_COUNT + 1)
    make benchmark-spike SUITE=$BENCHMAKR_SUITE BENCHMARK=$B COPT=$COPT && make spike-check MAX_CYCLES=$MAX_CYCLES
    # Check if the test failed
    if [ $? -ne 0 ]; then 
      FAILED_TEST=" ### FAIL : benchmark $B with COPT=$COPT;"
      echo $FAILED_TEST >> $CHECK_LOG 
      FAILED_TESTS=$FAILED_TESTS+$FAILED_TEST
      FAIL_COUNT=$(expr $FAIL_COUNT + 1)
    fi
  done 
done

# Display results
if [ $FAIL_COUNT -eq 0 ]; then 
	echo -e "\e[1;32;49m### SUCCESS: $BENCHMAKR_SUITE benchmark passed !\e[0m"
    echo -e "## All tests passed : $TOTAL_TESTS/$TOTAL_TESTS]"
    echo "... No failed tests" >> $CHECK_LOG
else 
	echo -e "\e[1;31;41m### ERROR: $BENCHMAKR_SUITE benchmark failed !\e[0m"
  echo -e "## Number of failed tests : $FAIL_COUNT/$TOTAL_TESTS"
  IFS=";" read -r -a fails <<< "$FAILED_TESTS"
  for F in "${fails[@]}"; do
      echo "$F"
  done
fi

exit 0