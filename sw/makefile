####################
# ----- INFO ----- #
####################
# Set up LEN5 toolchain settings and build source files

# VARIABLES
# ---------
# LEN5 root directory
ROOT 			= ..

# LEN5 software libraries
SW_DIR			?= $(ROOT)/sw
BUILD_DIR		?= $(ROOT)/build
SW_BUILD_DIR 	:= $(BUILD_DIR)/sw
LEN5_LIB 		:= $(SW_BUILD_DIR)/lib/liblen5.a
LIB_SRCS		:= $(shell find $(SW_DIR)/src -type f -name *.c -or -name *.s -or -name *.S)
LIB_OBJS		:= $(filter %.o,\
				   $(patsubst $(SW_DIR)/src/%.c,$(SW_BUILD_DIR)/obj/%.o,$(LIB_SRCS))\
				   $(patsubst $(SW_DIR)/src/%.s,$(SW_BUILD_DIR)/obj/%.o,$(LIB_SRCS))\
				   $(patsubst $(SW_DIR)/src/%.S,$(SW_BUILD_DIR)/obj/%.o,$(LIB_SRCS)))
LINK_SCRIPT		:= $(SW_DIR)/len5-sim.ld

# RISC-V C compiler
CROSS_COMPILE 	?= riscv64-unknown-elf-
ISA_STRING		?= rv64i
ABI_STRING		?= lp64
CC 				:= $(CROSS_COMPILE)gcc
CFLAGS			:= 	-march=$(ISA_STRING) \
					-mabi=$(ABI_STRING)
CINC			:= -I$(SW_DIR)/include
AS 				:= $(CROSS_COMPILE)as
ASFLAGS			:= $(CFLAGS)
AR 				:= $(CROSS_COMPILE)ar
ARFLAGS			:= rcus # s replaces ranlib

###########################
# ----- BUILD RULES ----- #
###########################

# Aliases
.PHONY: all
all: liblen5 sw-support

# Library including LEN5 support source files (crt0, IRQ table, _write)
.PHONY: liblen5
liblen5: $(LEN5_LIB)
$(LEN5_LIB): $(LIB_OBJS) | $(SW_BUILD_DIR)/lib $(SW_BUILD_DIR)/include
	$(AR) $(ARFLAGS) $@ $+

# Software support files
.PHONY: sw-support
sw-support: | $(SW_BUILD_DIR)/include
	cp -r $(SW_DIR)/include/* $(SW_BUILD_DIR)/include/
	cp $(LINK_SCRIPT) $(SW_BUILD_DIR)/

# Implicit compilation rules
$(SW_BUILD_DIR)/obj/%.o: $(SW_DIR)/src/%.c | $(SW_BUILD_DIR)/obj
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(SW_BUILD_DIR)/obj/%.o: $(SW_DIR)/src/%.S | $(SW_BUILD_DIR)/obj
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(SW_BUILD_DIR)/obj/%.o: $(SW_DIR)/src/%.s | $(SW_BUILD_DIR)/obj
	$(AS) $(ASFLAGS) $(CINC) -c $< -o $@

# Directories
# -----------
$(SW_BUILD_DIR)/obj $(SW_BUILD_DIR)/lib $(SW_BUILD_DIR)/include:
	mkdir -p $@

# Clear rules
# -----------
.PHONY: clean
clean: 
	$(RM) -r $(SW_BUILD_DIR)

.test:
	@echo $(LIB_OBJS)