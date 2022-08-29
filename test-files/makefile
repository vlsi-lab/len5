####################
# ----- INFO ----- #
####################
# Compile test files

# Variables
# ---------
# Paths
ROOT 			:= ..
BUILD_DIR		?= $(ROOT)/build/sw/tests
TEST_DIR 		:= .
TEST_SRCS		:= $(shell find $(TEST_DIR)/src/ -name '*.c' -or -name '*.s')
TEST_OBJS		:= $(patsubst $(TEST_DIR)/src/%.c,$(BUILD_DIR)/obj/%.o,$(TEST_SRCS))
TEST_BINS		:= $(patsubst $(TEST_DIR)/obj/%.o,$(BUILD_DIR)/bin/%,$(TEST_OBJS))
TESTS			:= $(addprefix tests/,$(basename $(notdir $(TEST_SRCS))))

# LEN5 software libraries
SW_DIR			?= $(ROOT)/sw
LIB_DIR 		?= $(ROOT)/build/sw/lib
LEN5_LIB 		?= $(LIB_DIR)/liblen5.a
LD_SCRIPT		?= $(SW_DIR)/len5-sim.ld

# RISC-V C compiler
CROSS_COMPILE 	?= riscv64-unknown-elf-
ISA_STRING		?= rv64i
ABI_STRING		?= lp64
CC 				:= $(CROSS_COMPILE)gcc
CFLAGS			?= 	-march=$(ISA_STRING) \
					-mabi=$(ABI_STRING) \
					-ffreestanding \
					-Wl,--gc-sections \
					-nostartfiles \
					-Wl,-T,$(LD_SCRIPT)
LDFLAGS			?= -llen5
CINC			?= -I$(SW_DIR)/include
CLIB			?= -L$(BUILD_DIR)/../lib
AS 				:= $(CROSS_COMPILE)as
ASFLAGS			:= $(CFLAGS)
AR 				:= $(CROSS_COMPILE)ar
ARFLAGS			:= rcu
OBJDUMP			:= $(CROSS_COMPILE)objdump
OBJCOPY			:= $(CROSS_COMPILE)objcopy

###########################
# ----- BUILD RULES ----- #
###########################

# Software tests
# --------------
.PHONY: all
all: $(TESTS)

.PHONY: $(TESTS)
$(TESTS): tests/%: $(BUILD_DIR)/mem/%.mem $(BUILD_DIR)/objdump/%.objdump

# Implicit rules
.PRECIOUS: $(BUILD_DIR)/objdump/%.objdump $(BUILD_DIR)/bin/%
$(BUILD_DIR)/mem/%.mem: $(BUILD_DIR)/bin/% | $(BUILD_DIR)/mem
	$(OBJCOPY) -O binary $< $@
$(BUILD_DIR)/objdump/%.objdump: $(BUILD_DIR)/bin/% | $(BUILD_DIR)/objdump
	$(OBJDUMP) -D $< > $@
$(BUILD_DIR)/bin/%: $(BUILD_DIR)/obj/%.o $(LEN5_LIB) | $(BUILD_DIR)/bin
	$(CC) $(CFLAGS) $(CINC) $(CLIB) $(SW_DIR)/src/crt0.S $< -o $@ $(LDFLAGS)
$(BUILD_DIR)/obj/%.o: $(TEST_DIR)/src/%.c | $(BUILD_DIR)/obj
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(BUILD_DIR)/obj/%.o: $(TEST_DIR)/src/%.s | $(BUILD_DIR)/obj
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@

# LEN5 library
$(LEN5_LIB): 
	$(MAKE) -C $(SW_DIR) liblen5

# Directories
# -----------
$(BUILD_DIR)/obj $(BUILD_DIR)/bin $(BUILD_DIR)/objdump $(BUILD_DIR)/mem:
	mkdir -p $@

# Clean rules
# -----------
.PHONY: clean
clean:
	$(RM) -r $(BUILD_DIR)/obj $(BUILD_DIR)/bin $(BUILD_DIR)/objdump $(BUILD_DIR)/mem

.test:
	@echo $(TEST_SRCS)
	@echo $(TEST_OBJS)
	@echo $(TESTS)