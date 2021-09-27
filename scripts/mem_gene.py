#################
## mem_gene.py ##
#################

# Author: Matteo Perotti
# Description: creation of a source file with some addresses, and a memory file in which they are mapped to words
# Details: The memory file will have (WORDS_IN_LINE*NLines) rows. Each row contains a hexadecimal address, a space delimiter, a random word.
# Notes: this script can be used to create files with reasonable length.
#        Constraint: NLines << MaxAddr (this should not be a problem)

import random as rand
import math

#############
##  PARAM  ##
#############

# Root path of the repository
ROOT_PATH = "../"

# Paths of the memory file and of the vaddr file
MemoryFilePath = ROOT_PATH + "src/memory/l2cache_emulator/memory.txt"
PaddrFilePath  = ROOT_PATH + "tb/memory/paddr.txt"
InfoFilePath   = ROOT_PATH + "tb/memory/info.txt"

# Others
delim = " "

# Parameters of the memory system
CacheSize = 2**15 # byte
NWay      = 2
BYTE_LEN  = 8     # bit
AddrLen   = 64    # bit
WordLen   = 64    # bit
LineSize  = 64    # byte

LINE_BYTE_OFF_LEN = int(math.log(LineSize, 2))
WORD_SIZE         = int(WordLen / BYTE_LEN)    # byte
LINE_LEN          = BYTE_LEN * LineSize        # bit

# How many lines to generate
NLines    = 64

##########################
##  LINE ADDR CREATION  ##
##########################

# List of the addresses
paddr_list = list()

# Find NLines different addresses
for k in range(NLines):
    # Find a line addr which hasn't already been used
    is_line_addr_ok = False
    while (not is_line_addr_ok):
      new_bin_addr = ""
      for bit in range(AddrLen - LINE_BYTE_OFF_LEN):
        new_bin_addr += str(rand.randint(0, 1))
      for bit in range(LINE_BYTE_OFF_LEN):
        new_bin_addr += '0'
      new_hex_addr = "{:0>16x}".format(int(new_bin_addr, 2))
      is_line_addr_ok = True
      for already_used_paddr in paddr_list:
        if (new_bin_addr == already_used_paddr):
          is_line_addr_ok = False
    # Valid address found
    paddr_list += [new_hex_addr]

# Order the list
paddr_list.sort()

#################
##  FILES GEN  ##
#################

# Write the memory file
with open(MemoryFilePath, "w") as mfid, open(PaddrFilePath, "w") as pfid, open(InfoFilePath, "w") as ifid:
  for addr in paddr_list:
    temp_word_addr = int(addr, 16)
    # For each word in a line -> create address and word
    for i in range(WORD_SIZE):
      word_addr = "{:0>16x}".format(temp_word_addr)
      # Random word generation
      random_word = ""
      for bit in range(WordLen):
        random_word += str(rand.randint(0, 1))
      # Use floor division to round down the address
      forcasted_set = int((temp_word_addr // LineSize) % (CacheSize // (NWay * LineSize)))
      mfid.write(word_addr + delim + random_word + "\n")
      pfid.write(word_addr + "\n")
      ifid.write(word_addr + delim + str(forcasted_set) + "\n")
      temp_word_addr += BYTE_LEN
