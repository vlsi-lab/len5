#!/bin/bash

####################
# ----- INFO ----- #
####################

# Compile LEN5 source code on VLSI servers (VLSI21 by default)

#####################################
# ----- DEFAULT CONFIGURATION ----- #
#####################################

# Script options
LOG_FILE="$(dirname $0)/compile-script.log"

# Get the LEN5 root directory
LEN5_ROOT_DIR="$(dirname $(realpath $0))"
LEN5_ROOT_DIR="$(realpath $LEN5_ROOT_DIR/..)"

# Remote LEN5 directory
REMOTE_SIM_DIR="~/sim/len5"

# File containing the list of LEN5 source files
SRC_LIST_FILE="$LEN5_ROOT_DIR/config/src-list.txt"
REMOTE_SRC_LIST_FILE="$REMOTE_SIM_DIR/$(basename $SRC_LIST_FILE)"

# Default remote host informatioin for SSH connection
USER_NAME=""
REMOTE_PORT=10033
SSH_KEY="~/.ssh/vlsi_rsa"
HOST_NAME="vlsiwall.polito.it"
REMOTE_HOST=""
SSH_OPT=""
RSYNC_OPT=""

# Compiler options
QUESTA_INIT_SCRIPT="/eda/scripts/init_questa"
COMPILER_OPT="-msglimit error -svinputport=compat +incdir+/eda/mentor/2020-21/RHELx86/QUESTA-CORE-PRIME_2020.4/questasim/verilog_src/uvm-1.1d/src/"

# Simulation options
TB_SRC=0
LAUNCH_SIM=0
WAVE_FILE="${LEN5_ROOT_DIR}/sim/waveall.do"
REMOTE_WAVE_FILE="${REMOTE_SIM_DIR}/remote-wave.do"
SIM_SCRIPT="${LEN5_ROOT_DIR}/private/sim/sim-script.do"
REMOTE_SIM_SCRIPT="${REMOTE_SIM_DIR}/sim.do"
VSIM_OPT_FILE="${LEN5_ROOT_DIR}/private/sim/sim-opt.txt"
REMOTE_VSIM_OPT_FILE="${REMOTE_SIM_DIR}/opt.txt"
SIM_TIME=100 # ns

####################################
# ----- FUNCTION DEFINITIONS ----- #
####################################

# Usage message
function print_usage() {
    [ ! "$1" = "" ] && { printf -- "\nERROR: %s\n\n" "$1" 1>&2; }
    printf -- "USAGE: $0 [OPTIONS]\n"
    printf -- "OPTIONS:\n"
    printf -- "-h:      print this message and exit.\n"
    printf -- "-t:      also compile top-level testbench files in 'tb/'.\n"
    printf -- "-r:      also run simulation (implies '-t')\n"
    printf -- "-p:      set remote port (default: %d).\n" $REMOTE_PORT
    printf -- "-u:      set remote username.\n"
    printf -- "-s HOST: run simulation on HOST instead of '%s'.\n" "$REMOTE_HOST"
    printf -- "-w FILE: add 'do FILE' (default: '%s') to simulation script.\n" "${WAVE_FILE}"
}

# Log message
function log() {
    if [ $# -eq 0 ]; then
        printf -- "\n"
    else
        printf -- "### INFO > " | tee /dev/tty >> ${LOG_FILE}
        printf -- "$@" | tee /dev/tty >> ${LOG_FILE}
        printf -- "\n" | tee /dev/tty >> ${LOG_FILE}
    fi
}

# Print error message and terminate with error
function err() {
    printf -- "\n!!! ERR  > " | tee /dev/tty >&2 >> ${LOG_FILE}
    printf -- "$@" | tee /dev/tty >&2 >> ${LOG_FILE}
    printf -- "\n" | tee /dev/tty >&2 >> ${LOG_FILE}
    exit 1
}

# Send commands to remote host
function remote_cmd() {
    ssh $SSH_OPT $REMOTE_HOST "
$@
    "
    if [ $? -ne 0 ]; then 
        err "ERROR while executing commands on remote host"
        return 1
    fi
    return 0
}

####################################
# ----- COMMAND-LINE OPTIONS ----- #
####################################

# Parse command line options
# --------------------------
while getopts ':htrpus:w:' opt; do
    case $opt in
        h) # Print usage message
            print_usage
            exit 0
            ;;
        t) # Also compile TB files
            TB_SRC=1
            ;;
        r) # Also run simulation
            TB_SRC=1
            LAUNCH_SIM=1
            ;;
        p) # Set the remote port
            REMOTE_PORT=$OPTARG
            ;;
        u) # Set remote username
            USER_NAME="$OPTARG"
            ;;
        s) # Override default remote host
            HOST_NAME="$OPTARG"
            ;;
        w) # Waveform macro
            WAVE_FILE="$OPTARG"
            ;;
        *) # Invalid option
            print_usage "invalid option"
            exit 1
            ;;
    esac
done
shift $((OPTIND-1))

# Add testbench source files if necessary
[ ${TB_SRC} -ne 0 ] && SRC_LIST_FILE="$LEN5_ROOT_DIR/config/tb-list.txt"

# If the log file exists, remove it
[ -f "$LOG_FILE" ] && rm "$LOG_FILE"

# Infer user name if not explicitely provided
if [ "$USER_NAME" = "" ]; then 
    USR=$(whoami)
    case $USR in
        michi)
            USER_NAME="michele.caon"
            ;;
        whasn)
            USER_NAME="walid.walid"
            ;;
        *) # other
            err "Cannot automatically infer user name. Please specify it with -u"
    esac
fi

# Assemble remote host string and add key option
REMOTE_HOST="$USER_NAME@$HOST_NAME"
SSH_OPT="$SSH_OPT -p $REMOTE_PORT"
SSH_OPT="$SSH_OPT -i $SSH_KEY"

###########################################
# ----- COMPILE LEN5 ON REMOTE HOST ----- #
###########################################

# Copy LEN5 source
log "Copying LEN5 source files to '%s'..." "$REMOTE_HOST"
remote_cmd "mkdir -p $REMOTE_SIM_DIR"
rsync -e "ssh $SSH_OPT" -a --del $LEN5_ROOT_DIR/include $LEN5_ROOT_DIR/src $LEN5_ROOT_DIR/tb $REMOTE_HOST:$REMOTE_SIM_DIR/
if [ $? -ne 0 ]; then
    err "ERROR while copying LEN5 files\n"
fi

# Copy the source file list
log "Copying file containing the list of LEN5 source files..."
rsync -e "ssh $SSH_OPT" $SRC_LIST_FILE $REMOTE_HOST:$REMOTE_SRC_LIST_FILE
if [ $? -ne 0 ]; then
    err "ERROR while copying list of source files"
fi

# Compile LEN5 source
log "Launching compilation..."
log
remote_cmd "
cd $REMOTE_SIM_DIR
source ${QUESTA_INIT_SCRIPT} > /dev/null
vlog $COMPILER_OPT -f $REMOTE_SRC_LIST_FILE
"
if [ $? -ne 0 ]; then
    err "ERROR: there were compilation errors\n"
else
    log
    log "SOURCE CODE COMPILED SUCCESSFULLY!!!"
fi

# Exit if no testbench is compiled
[ ${TB_SRC} -eq 0 ] && exit 0

#########################################
# ----- PREPARE SIMULATION SCRIPT ----- #
#########################################

if [ ${LAUNCH_SIM} -ne 0 ]; then 
    log
    log "Assembling simulation script '${SIM_SCRIPT##${LEN5_ROOT_DIR}/}'..."

    # Launch simulation
    echo "vsim work.tb_combined -t 10ps -voptargs=+acc" > ${SIM_SCRIPT}

    # Load waveforms
    echo "do ${REMOTE_WAVE_FILE}" >> ${SIM_SCRIPT}

    # Run the simulation for 100ns
    echo "run ${SIM_TIME}ns" >> ${SIM_SCRIPT}

    # Copy the simulation script on remote host
    log "Copying simualtion script on ${HOST_NAME}..."
    rsync -e "ssh $SSH_OPT" ${SIM_SCRIPT} $REMOTE_HOST:${REMOTE_SIM_SCRIPT}
    if [ $? -ne 0 ]; then
        err "ERROR while copying simulation script"
    fi

    # Copy waveforms macro file on remote host
    log "Copying waveforms macro on ${HOST_NAME}..."
    rsync -e "ssh $SSH_OPT" ${WAVE_FILE} $REMOTE_HOST:${REMOTE_WAVE_FILE}
    if [ $? -ne 0 ]; then
        err "ERROR while copying waveforms file"
    fi

    # log
    # log "DONE. You can launch the simulation on ${HOST_NAME} with:"
    # log "   vsim -f ${REMOTE_VSIM_OPT_FILE} -do ${REMOTE_SIM_SCRIPT}"

    # Launch the simulation
    log "Launching simulation on ${HOST_NAME}..."
    SSH_OPT="-X ${SSH_OPT}"
    remote_cmd "
    cd ${REMOTE_SIM_DIR}
    source ${QUESTA_INIT_SCRIPT} > /dev/null
    vsim -gui -f ${REMOTE_VSIM_OPT_FILE} -do ${REMOTE_SIM_SCRIPT}
    "
    if [ $? -ne 0 ]; then
        err "ERROR while launching simulation"
    fi
fi

# Terminate
exit 0