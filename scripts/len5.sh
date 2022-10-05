#!/bin/bash

####################
# ----- INFO ----- #
####################

# Compile LEN5 source files and optionally simulate the requested file.

#############################
# ----- CONFIGURATION ----- #
#############################

# PARAMETERS
# ----------

# Paths
LEN5_ROOT_DIR="$(realpath $(dirname $0)/..)"
BUILD_DIR="$LEN5_ROOT_DIR/build"

# Command line arguments
PRINT_CMD_LINE=0
CMD_LINE=$@

# Remote execution
FORCE_LOCAL_EXEC=0
REMOTE_EXEC=0
REMOTE_USER=""
# REMOTE_PORT=10033 # vlsi21
REMOTE_PORT=50050 # saruman > centos-8-eda
# REMOTE_HOST=vlsiwall.polito.it
REMOTE_HOST=saruman.polito.it
REMOTE_ROOT_DIR="~/sim/len5"
SSH_KEY=~/.ssh/vlsi_rsa
SSH_OPT="-p $REMOTE_PORT -i $SSH_KEY"
RSYNC_OPT="-rtl --del"

# Compilation options
LAUNCH_SIM=0
CUSTOM_SRC=0
BUILD_TARGET=modules

# Simulation options
TOP_MODULE_FILE=$LEN5_ROOT_DIR/tb/tb_bare.sv
SIM_WAVE_ZOOM=1000 # ns
SIM_OPT="-sv_seed random" # default simulator options
POST_SIM_SCRIPT=""
VSIM_GUI=0
VSIM_DISABLE_OPT=1
NUM_CYCLES=10000

# Compile and simulate script
HEADER_MSG="# Auto-generated by $0 -- $(date)"
CMD_LINE_MSG="# command line: $(basename $0) $@"
RUN_SCRIPT=""

# Synthesis
LAUNCH_SYN=0
SYN_DIR=$LEN5_ROOT_DIR/syn
SYN_SCRIPT=$SYN_DIR/syn-local.sh

####################################
# ----- FUNCTION DEFINITIONS ----- #
####################################

# Print usage message
print_usage() {
    [ ! "$1" = "" ] && { printf -- "\nERROR: %s\n\n" "$1" 1>&2; }
    printf -- "USAGE: $0 [OPTIONS] [SRC_DIR] [TOP_MODULE_FILE] [SIM_ARGS]\n"
    printf -- "OPTIONS:\n"
    printf -- "\n"
    printf -- "General:\n"
    printf -- "-h:      print this message and exit.\n"
    printf -- "-B DIR:  use DIR as simulation working directory.\n"
    printf -- "-g FILE: auto-generate compile-and-run script FILE.\n"
    printf -- "-r STR:  compile [and simulate] on a remote server.\n"
    printf -- "-L:      force local execution (overrides '-r').\n"
    printf -- "-R STR:  set SSH options to 'STR' Default: '%s'.\n" "$SSH_OPT"
    printf -- "-d:      clean build subdirectories (shortcut for '-cb clean').\n"
    printf -- "-D:      clean build directory (shortcut for '-cb clean-all').\n"
    printf -- "\n"
    printf -- "Compilation:\n"
    printf -- "-b TGT:  build target TGT. Default: '%s'.\n" $BUILD_TARGET
    printf -- "-a:      shortcut for '-b all' (also compile testbench and SW).\n"
    printf -- "-t:      shortcut for '-b tb' (also compile testbench).\n"
    printf -- "-n:      compile dry run (pass '-n' to make).\n"
    printf -- "-f OPTS: add OPTS to 'vlog' command-line arguments.\n"
    printf -- "-l LIB:  use custom library path LIB.\n"
    printf -- "\n"
    printf -- "Simulation (ignored with '-c'):\n"
    printf -- "-s:      launch simulation after compilation.\n"
    printf -- "-T:      list available tests (alias for '-b print-tests').\n"
    printf -- "-m TEST: compile and simulate TEST (see -T).\n"
    printf -- "-W FILE: load waveforms from FILE. Implies '-x'.\n"
    printf -- "-N NUM:  simulate NUM cycles; infinite if 0. Default: %d.\n" $NUM_CYCLES
    printf -- "-x:      launch simulation with GUI (ignores '-o').\n"
    printf -- "-o:      remove '-voptargs=+acc' from simulation options.\n"
    printf -- "-p FILE: pass '-do FILE' to the simulator AFTER the 'run' command.\n"
    printf -- "-v LVL:  set UVM verbosity level to NUM (accepted: [0:5])"
    printf -- "\n"
    printf -- "Synthesis:\n"
    printf -- "-S:      launch synthesis after compilation (implies 'r').\n"
}

# Log message
function log() {
    [ ! -f $LOG_FILE ] && return
    if [ $# -eq 0 ]; then
        printf -- "\n"
    else
        printf -- "### INFO > " | tee /dev/tty >> $LOG_FILE
        printf -- "$@" | tee /dev/tty >> $LOG_FILE
        printf -- "\n" | tee /dev/tty >> $LOG_FILE
    fi
}

# Print error message and terminate with error
function err() {
    printf -- "\n!!! ERR  > " | tee /dev/tty >&2 >> $LOG_FILE
    printf -- "$@" | tee /dev/tty >&2 >> $LOG_FILE
    printf -- "\n" | tee /dev/tty >&2 >> $LOG_FILE
    exit 1
}

# Run and log command
function run_and_log() {
    local CMD="$@"
    log "Executing '$CMD'..."
    printf -- "====================== [%s] BEGIN ======================\n" "$1"
    set -o pipefail
    $CMD |& tee /dev/tty | sed "s/^/[$1] /" >> $LOG_FILE
    RET=$?
    set +o pipefail
    printf -- "======================= [%s] END =======================\n" "$1"
    return $RET
}

# Command to simulation script
function to_run_script() {
    local CMD="$@"
    [ ! "$RUN_SCRIPT" = "" ] && echo $CMD >> $RUN_SCRIPT
}

# Send commands to remote host
function remote_and_log() {
    local CMD="$@"
    log "Executing on remote host: $CMD..."
    printf -- "===================== REMOTE BEGIN =====================\n"
    set -o pipefail
    ssh -t $SSH_OPT $REMOTE_USER@$REMOTE_HOST "$CMD" |& tee /dev/tty | sed "s/^/[REMOTE] /" >> $LOG_FILE
    RET=$?
    set +o pipefail
    printf -- "====================== REMOTE END ======================\n"
    return $RET
}

# Clean up and exit
function clean_up() {
    log "Cleaning up..."
    [ ! "$RUN_SCRIPT" = "" ] && chmod +x $RUN_SCRIPT
    if [ $HOST_NAME = "ghostpro" ]; then
        source $INIT_SCRIPT -q
    fi
    log "ALL DONE!"
}

####################################
# ----- COMMAND LINE OPTIONS ----- #
####################################

# Parse command line options
# --------------------------
while getopts ':hB:g:rLR:dDb:atnf:l:isTm:W:N:xop:v:S' opt; do
    case $opt in
        h) # Print usage message
            print_usage
            exit 0
            ;;
        B) # Change simulation working directory
            BUILD_DIR="$OPTARG"
            ;;
        g) # auto-generate script
            RUN_SCRIPT="$OPTARG"
            rm -f $RUN_SCRIPT
            ;;
        r) # compile and run on remote server
            REMOTE_EXEC=1
            ;;
        L) # force local execution
            FORCE_LOCAL_EXEC=1
            ;;
        R) # Set rsync options
            SSH_OPT="$OPTARG"
            ;;
        d) # Clean build subdirectories
            BUILD_TARGET=clean
            ;;
        D) # Clean build directory
            BUILD_TARGET=clean-all
            ;;
        b) # Select build target
            BUILD_TARGET=$OPTARG
            ;;
        a) # shortcut for '-b all' (also compile testbench and sw files)
            BUILD_TARGET=all
            ;;
        t) # shortcut for '-b tb' (also compile testbench and sw files)
            BUILD_TARGET=tb
            ;;
        n) # compile dry run (pass '-n' to make)
            MAKE_OPT="$MAKE_OPT -n"
            ;;
        f) # add compilation options to 'vlog' command line
            VLOG_ARGS="$VLOG_ARGS $OPTARG"
            ;;
        l) # Use custom library
            VLIB_PATH=$OPTARG
            ;;
        s) # Launch simulation
            LAUNCH_SIM=1
            ;;
        T) # Print available tests
            BUILD_TARGET=print-tests
            ;;
        m) # Compile and simulate the requested test
            TEST_NAME=$OPTARG
            BUILD_TARGET="tb tests/$TEST_NAME"
            LAUNCH_SIM=1
            ;;
        W) # pass macro to simulator
            WAVE_FILE="$OPTARG"
            VSIM_GUI=1
            ;;
        N) # set the number of simulation cycles
            NUM_CYCLES=$OPTARG
            ;;
        x) # Launch simulation with GUI
            VSIM_GUI=1
            ;;
        o) # Remove -voptargs=+acc from simulation options
            VSIM_DISABLE_OPT=0
            ;;
        p) # pass '-do FILE' to the simulator AFTER the 'run' command
            POST_SIM_SCRIPT="$OPTARG"
            ;;
        v) # Set UVM verbosity level [0:5]
            UVM_VERBOSITY=$OPTARG
            ;;
        S) #Launch synthesis script
            LAUNCH_SYN=1
            REMOTE_EXEC=1
            ;;
        *) # Invalid option
            print_usage "invalid option"
            exit 1
            ;;
    esac
done
shift $((OPTIND-1))

# Setup paths
HW_BUILD_DIR="$BUILD_DIR/hw"
LOG_FILE="$BUILD_DIR/len5.log"
[ -z ${VLIB_PATH+x} ] && VLIB_PATH=$HW_BUILD_DIR/work
SIM_MACRO="$HW_BUILD_DIR/sim.do"

####################################
# ----- COMPILE AND SIMULATE ----- #
####################################

# Initialization
# --------------

# Initialize simulation directory
mkdir -p $BUILD_DIR
if [ -z ${RUN_SCRIPT+x} ]; then
    > ${RUN_SCRIPT}
fi

# Initialize compilation log
> $LOG_FILE

# Print welcome message
log "    [This is '%s' on '%s']" "$(basename $0)" "$(uname -n)"
log
if [ $PRINT_CMD_LINE -ne 0 ]; then
    log "arguments:"
    for arg in $CMD_LINE; do
        log "\t%s" "$arg"
    done
fi

# REMOTE EXECUTION
# ----------------
if [ $REMOTE_EXEC -ne 0 -a $FORCE_LOCAL_EXEC -eq 0 ]; then
    # Infer user name
    USR=$(whoami)
    case $USR in
        michi|michele.caon)
            REMOTE_USER=michele.caon
            ;;
        whasn|walid.walid)
            REMOTE_USER=walid.walid
            ;;
        *) # other
            log "WARNING: unknown user requested remote execution: expect errors."
            REMOTE_USER=$USR
            ;;
    esac

    # Prepare remote directories and SSH options
    remote_and_log "mkdir -p $REMOTE_ROOT_DIR"
    [ $VSIM_GUI -ne 0 ] && SSH_OPT="-Y $SSH_OPT"

    # Copy files to remote server
    log "Copying LEN5 files to '%s'..." "$REMOTE_HOST"
    rsync -e "ssh $SSH_OPT" $RSYNC_OPT --relative $LEN5_ROOT_DIR/./{include,src,tb,scripts,sw,sim,syn,makefile} $REMOTE_USER@$REMOTE_HOST:$REMOTE_ROOT_DIR/
    [ $? -ne 0 ] && err "!!! ERROR while copying LEN5 source files..."

    # Pass options to remote script
    log "Launching script on remote server..."
    CMD_LINE="-L $CMD_LINE"
    remote_and_log "$REMOTE_ROOT_DIR/scripts/$(basename $0) $CMD_LINE"
    [ $? -ne 0 ] && err "!!! ERROR while executing remote script..."

    # Retrieve files
    if [ $LAUNCH_SIM -ne 0 ]; then
        log "Retrieving files from '%s'...\n" "$REMOTE_HOST"
        mkdir -p $HW_BUILD_DIR
        rsync -e "ssh $SSH_OPT" $RSYNC_OPT --ignore-missing-args $REMOTE_USER@$REMOTE_HOST:$REMOTE_ROOT_DIR/sim/*.do $LEN5_ROOT_DIR/sim/
        rsync -e "ssh $SSH_OPT" $RSYNC_OPT --ignore-missing-args $REMOTE_USER@$REMOTE_HOST:$REMOTE_ROOT_DIR/build/hw/{*.txt,*.do} $HW_BUILD_DIR/
    fi

    if [ $LAUNCH_SYN -ne 0 ]; then
        log "Retrieving synthesis report from '%s'...\n" $REMOTE_HOST
        REPORT_DIR=$SYN_DIR/reports/$(date +%Y%m%d.%H%M%S)
        mkdir -p $REPORT_DIR
        rsync -e "ssh $SSH_OPT" $RSYNC_OPT --ignore-missing-args $REMOTE_USER@$REMOTE_HOST:$REMOTE_ROOT_DIR/syn/reports/*.{txt,log} $REPORT_DIR/
        rsync -e "ssh $SSH_OPT" $RSYNC_OPT --ignore-missing-args $REMOTE_USER@$REMOTE_HOST:$REMOTE_ROOT_DIR/syn/logs/*.{txt,log} $REPORT_DIR/
    fi

    # Exit
    log "REMOTE EXECUTION COMPLETED!"
    exit 0
fi

# LOCAL EXECUTION
# ---------------

# Default Questa Sim initialization script
HOST_NAME=$(uname -n)
if [[ $HOST_NAME =~ .*.vlsilab ]]; then   # VLSI Lab servers @ POLITO
    INIT_SCRIPT="/eda/scripts/init_questa"
elif [[ $HOST_NAME = saruman* ]]; then  # saruman.eda @ POLITO
    INIT_SCRIPT="/eda/scripts/init_questa"
elif [ $HOST_NAME = "ghostpro" ]; then
    INIT_SCRIPT="$HOME/Documents/scripts/init-questa.sh"
else
    err "!!! WARNING: running on unsupported host. Expect some issues."
    INIT_SCRIPT=""
fi

# Initialize generated script
to_run_script "#!/bin/bash"
to_run_script "$HEADER_MSG"
to_run_script "$CMD_LINE_MSG"

# Get other arguments
if [ $# -gt 0 ]; then 
    CUSTOM_SRC=1
    INPUT_DIR=$1
    if [ $# -gt 1 ]; then
        TOP_MODULE_FILE=$2
        shift
    fi
    shift
fi
SIM_ARGS="$@"

# Create simulation directory
cd $LEN5_ROOT_DIR
to_run_script "cd $LEN5_ROOT_DIR"
to_run_script "mkdir -p $(realpath --relative-to=$LEN5_ROOT_DIR $BUILD_DIR)"

# Launch initialization script
log "Initializing QuestaSim..."
source "$INIT_SCRIPT"
[ $? -ne 0 ] && err "!!! ERROR while sourcing '%s'" "$INIT_SCRIPT"
to_run_script "source $INIT_SCRIPT"

# Compile files
# -------------

# Get a list of additional source files
if [ $CUSTOM_SRC -ne 0 ]; then
    REL_PATH=$(realpath --relative-to=$LEN5_ROOT_DIR $INPUT_DIR)
    export CUSTOM_SRC_DIR=$REL_PATH
    to_run_script "export CUSTOM_SRC_DIR=$REL_PATH"
    BUILD_TARGET="$BUILD_TARGET custom-src"
fi

# Export variables for make
export VLOG_ARGS=$VLOG_ARGS
to_run_script "export VLOG_ARGS=\"$VLOG_ARGS\""
export VWORK=$VLIB_PATH
to_run_script "export VWORK=$VLIB_PATH"
export BUILD_DIR=$BUILD_DIR
to_run_script "export BUILD_DIR=$BUILD_DIR"

# Launch make
log "Compiling source files..."
run_and_log make $MAKE_OPT $BUILD_TARGET
[ $? -ne 0 ] && err "!!! ERROR while executing 'make'"
to_run_script "make $MAKE_OPT $BUILD_TARGET"

# Exit if only compilation was requested
log "COMPILATION SUCCESSFULLY COMPLETED!"
log
if [ $LAUNCH_SIM -eq 0 -a $LAUNCH_SYN -eq 0 ]; then
    clean_up
    exit 0
fi

# Launch synthesis script
if [ $LAUNCH_SYN -ne 0 ]; then
    log "Launching synthesis..."
    $SYN_SCRIPT
    if [ $? -ne 0 ]; then 
        err "!!! ERROR while synthesizing the design"
    fi
    clean_up
    exit 0
fi

# Launch simulation 
# -----------------

# Get the module name
TOP_MODULE="$(basename $TOP_MODULE_FILE)"
TOP_MODULE=${TOP_MODULE%.*}

# Run the simulation
log "Launching simulation of top module '%s'..." "$TOP_MODULE"

# Set UVM verbosity macro
case $UVM_VERBOSITY in
    0) UVM_VERBOSITY=UVM_NONE;;
    1) UVM_VERBOSITY=UVM_LOW;;
    2) UVM_VERBOSITY=UVM_MEDIUM;;
    3) UVM_VERBOSITY=UVM_HIGH;;
    4) UVM_VERBOSITY=UVM_FULL;;
    5) UVM_VERBOSITY=UVM_DEBUG;;
    *) UVM_VERBOSITY=UVM_MEDIUM;;
esac
SIM_OPT="$SIM_OPT +UVM_VERBOSITY=$UVM_VERBOSITY"

# Assemble the simulation script
log "- assembling simulation script '%s'..." "${SIM_MACRO}"
if [ $VSIM_GUI -ne 0 ]; then 
    SIM_OPT="-gui $SIM_OPT"
    VSIM_DISABLE_OPT=1
else 
    SIM_OPT="-c $SIM_OPT"
fi
[ $VSIM_DISABLE_OPT -ne 0 ] && SIM_OPT="-voptargs=+acc $SIM_OPT"
if [ ! -z ${TEST_NAME+x} ]; then
    MEM_FILE=$BUILD_DIR/sw/tests/mem/$TEST_NAME.img
    [ -f $MEM_FILE ] || err "Cannot find '%s'" $MEM_FILE
    SIM_OPT="$SIM_OPT +MEM_FILE=$MEM_FILE"
fi
SIM_OPT="$SIM_OPT +N=$NUM_CYCLES"
SIM_OPT="$SIM_OPT $SIM_ARGS"
if [ ! "$WAVE_FILE" = "" ]; then
    WAVE_FILE=$(realpath --relative-to=$HW_BUILD_DIR $WAVE_FILE)
    SIM_OPT="$SIM_OPT -do $WAVE_FILE"
fi
echo "$HEADER_MSG" > $SIM_MACRO
echo "\
puts \"\n########## SIMULATION STARTS ##########\n\"
run -all
puts \"\n##########  SIMULATION ENDS  ##########\n\"\
" >> $SIM_MACRO
[ ! $POST_SIM_SCRIPT = "" ] && echo "do $POST_SIM_SCRIPT" >> $SIM_MACRO
if [ $VSIM_GUI -eq 0 ]; then
    echo "exit" >> $SIM_MACRO
fi

# Prepare relative path
VLIB_PATH=$(realpath --relative-to $HW_BUILD_DIR $VLIB_PATH)
SIM_MACRO=$(realpath --relative-to $HW_BUILD_DIR $SIM_MACRO)

# Launch the simulation
log "- starting simulation..."
to_run_script "cd $BUILD_DIR"
cd $HW_BUILD_DIR
run_and_log vsim -work $VLIB_PATH $SIM_OPT -do $SIM_MACRO ${TOP_MODULE}
if [ $? -ne 0 ]; then 
    err "!!! ERROR while simulating the design"
fi
cd $LEN5_ROOT_DIR
to_run_script "vsim -work $VLIB_PATH $SIM_OPT -do $SIM_MACRO ${TOP_MODULE}"
to_run_script "cd $LEN5_ROOT_DIR"

# Exit
log "### ALL DONE!"
clean_up
exit 0