#!/bin/bash

####################
# ----- INFO ----- #
####################

# Compile LEN5 source code on VLSI servers (VLSI21 by default)

#####################################
# ----- DEFAULT CONFIGURATION ----- #
#####################################

# Get the LEN5 root directory
LEN5_ROOT_DIR="$(dirname $(realpath $0))"
LEN5_ROOT_DIR="$(realpath $LEN5_ROOT_DIR/..)"

# Log file
LOG_FILE="$LEN5_ROOT_DIR/private/compile-script.log"

# Remote LEN5 directory
REMOTE_SIM_DIR="~/sim/len5"

# File containing the list of LEN5 source files
SRC_LIST_FILE="$LEN5_ROOT_DIR/config/src-list.txt"

# Default remote host informatioin for SSH connection
USER_NAME=""
REMOTE_PORT=10033
SSH_KEY="~/.ssh/vlsi_rsa"
HOST_NAME="vlsiwall.polito.it"
REMOTE_HOST=""
SSH_OPT=""
RSYNC_OPT=""

# Compiler options
COMPILER_OPT="-msglimit error -svinputport=compat"

####################################
# ----- FUNCTION DEFINITIONS ----- #
####################################

# Usage message
function print_usage() {
    [ ! "$1" = "" ] && { printf -- "\nERROR: %s\n\n" "$1" 1>&2; }
    printf -- "USAGE: $0 [OPTIONS]\n"
    printf -- "OPTIONS:\n"
    printf -- "-h:      print this message and exit.\n"
    printf -- "-f FILE: read list of source files from FILE.\n"
    printf -- "         Default: %s.\n" "$SRC_LIST_FILE"
    printf -- "-l FILE: log messages to FILE.\n" 
    printf -- "         Default: %s.\n" "$LOG_FILE"
    printf -- "-p PORT: set remote port number.\n"
    printf -- "         Default: %d.\n" $REMOTE_PORT
    printf -- "-s HOST: run simulation on HOST.\n"
    printf -- "         Default: %s.\n" "$HOST_NAME"
    printf -- "-t:      also compile top-level testbench files in 'tb/'.\n"
    printf -- "-u USER: set remote username.\n"
}

# Log message
function log() {
    if [ $# -eq 0 ]; then
        printf -- "\n" | tee /dev/tty >> ${LOG_FILE}
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

####################################
# ----- COMMAND-LINE OPTIONS ----- #
####################################

# Parse command line options
# --------------------------
while getopts ':hf:l:p:s:tu:' opt; do
    case $opt in
        h) # Print usage message
            print_usage
            exit 0
            ;;
        f) # Read list of source files from file
            SRC_LIST_FILE="$OPTARG"
            ;;
        l) # Log output to file
            LOG_FILE="$OPTARG"
            ;;
        p) # Set the remote port
            REMOTE_PORT=$OPTARG
            ;;
        s) # Override default remote host
            HOST_NAME="$OPTARG"
            ;;
        t) # Also compile TB files
            SRC_LIST_FILE="$LEN5_ROOT_DIR/config/tb-list.txt"
            ;;
        u) # Set remote username
            USER_NAME="$OPTARG"
            ;;
        *) # Invalid option
            print_usage "invalid option"
            exit 1
            ;;
    esac
done
shift $((OPTIND-1))

# If the log file exists, remove it
[ -f "$LOG_FILE" ] && rm "$LOG_FILE"

# Infer user name if not explicitely provided
if [ "$USER_NAME" = "" ]; then 
    USR=$(whoami)
    case $USR in
        michi)
            USER_NAME="michele.caon"
            ;;
        walid)
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
ssh $SSH_OPT $REMOTE_HOST "mkdir -p $REMOTE_SIM_DIR"
rsync -e "ssh $SSH_OPT" -a --del $LEN5_ROOT_DIR/include $LEN5_ROOT_DIR/src $LEN5_ROOT_DIR/tb $REMOTE_HOST:$REMOTE_SIM_DIR/
if [ $? -ne 0 ]; then
    err "ERROR while copying LEN5 files\n"
fi

# Copy the source file list
log "Copying file containing the list of LEN5 source files..."
REMOTE_SRC_LIST_FILE="$REMOTE_SIM_DIR/$(basename $SRC_LIST_FILE)"
rsync -e "ssh $SSH_OPT" $SRC_LIST_FILE $REMOTE_HOST:$REMOTE_SRC_LIST_FILE
if [ $? -ne 0 ]; then
    err "ERROR while copying list of source files"
fi

# Compile LEN5 source
log "Launching compilation..."
log
ssh $SSH_OPT $REMOTE_HOST "
cd $REMOTE_SIM_DIR
source /software/europractice-release-2019/scripts/init_questa10.7c > /dev/null
vlog $COMPILER_OPT -f $REMOTE_SRC_LIST_FILE
" | tee /dev/tty >> ${LOG_FILE}
if [ $? -ne 0 ]; then
    err "ERROR: there were compilation errors\n"
else
    log
    log "SOURCE CODE COMPILED SUCCESSFULLY!!!"
fi

# Terminate
exit 0