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
BUILD_DIR		?= $(ROOT)/build/sw/lib
LIB_PATH 		= $(shell realpath $(BUILD_DIR))
LEN5_LIB 		?= $(BUILD_DIR)/liblen5.a
LIB_SRCS		:= $(shell find $(SW_DIR)/src -type f -name *.c)
LIB_OBJS		:= $(patsubst $(SW_DIR)/src/%.c,$(BUILD_DIR)/obj/%.o,$(LIB_SRCS))
LIB_INC_DIR		:= $(ROOT)/sw/include
LIB_CFLAGS 		:= -I$(LIB_INC_DIR)

# RISC-V C compiler
CROSS_COMPILE 	?= riscv64-unknown-elf-
ISA_STRING		?= rv64i
ABI_STRING		?= lp64
CC 				= $(CROSS_COMPILE)gcc
CFLAGS			?= 	-march=$(ISA_STRING) \
					-mabi=$(ABI_STRING)
LDFLAGS			?=
CINC			?= -I$(SW_DIR)/include
AS 				= $(CROSS_COMPILE)as
ASFLAGS			= $(CFLAGS)
OBJDUMP			= $(CROSS_COMPILE)objdump
AR 				= $(CROSS_COMPILE)ar
ARFLAGS			= rcu

###########################
# ----- BUILD RULES ----- #
###########################

# All targets
.PHONY: all
all: crt0 $(LEN5_LIB) includes

# Compile custom C runtime crt0.s
.PHONY: crt0
crt0: $(BUILD_DIR)/obj/crt0.o
$(BUILD_DIR)/obj/crt0.o: $(SW_DIR)/src/crt0.S | $(BUILD_DIR)/obj
	$(AS) $(ASFLAGS) $(LIB_CFLAGS) -c $< -o $@

# Create dummy library that redefines _write from Newlib
.PHONY: liblen5
liblen5: $(LEN5_LIB)
$(LEN5_LIB): $(LIB_OBJS) | $(BUILD_DIR)
	$(AR) $(ARFLAGS) $@ $+ 

# Headers
.PHONY: includes
includes: $(SW_DIR)/include/*.h
	cp -r $(SW_DIR)/include $(BUILD_DIR)/

# Implicit compilation rules
$(BUILD_DIR)/obj/%.o: $(SW_DIR)/src/%.c | $(BUILD_DIR)/obj
	$(CC) $(CFLAGS) $(LIB_CFLAGS) -c $< -o $@
$(BUILD_DIR)/obj/%.o: $(SW_DIR)/src/%.s | $(BUILD_DIR)/obj
	$(AS) $(ASFLAGS) $(LIB_CFLAGS) -c $< -o $@

# Directories
# -----------
$(BUILD_DIR) $(BUILD_DIR)/obj $(BUILD_DIR)/obj:
	mkdir -p $@

# Clear rules
# -----------
.PHONY: clean
clean: 
	$(RM) -r $(BUILD_DIR)/obj $(BUILD_DIR)

.test:
	@echo $(ROOT)
	@echo $(BUILD_DIR)
	@echo $(BUILD_DIR)
	@echo $(LIB_PATH)
	@echo $(PWD)