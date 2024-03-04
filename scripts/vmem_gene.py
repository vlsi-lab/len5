#!/usr/bin/python
import random

#############
##  PARAM  ##
#############

# Root path of the repository
ROOT_PATH = "../"

MEMORY_FILE_PATH   = ROOT_PATH + "src/memory/l2cache_emulator/memory.txt"
VADDR_FILE_PATH    = ROOT_PATH + "tb/memory/vaddr.txt"
ROOT_PPN_FILE_PATH = ROOT_PATH + "tb/memory/root_ppn.txt"

# CONSTANT
PAGE_OFF_A_LEN    = 12 # bit
PAGE_TABLE_LEVELS = 3
WORD_OFF_A_LEN    = 3

how_many_vaddr    = 170

# +1 because of the page table root address
HOW_MANY_44b_PPN  = (PAGE_TABLE_LEVELS * how_many_vaddr) + 1
# PPN page offset
HOW_MANY_9b_VPN   = (PAGE_TABLE_LEVELS * how_many_vaddr)
# VADDR/PADDR page offset
HOW_MANY_12b_POFF = how_many_vaddr

#############################################################
##  LISTS OF DIFFERENT PPN, VPN PARTS, PAGE OFFSET (RAWS)  ##
#############################################################

PPN_44b_list  = random.sample(range(0, (2**44)-1), HOW_MANY_44b_PPN)

VPN_9b_list   = random.sample(range(0, (2**9)-1), HOW_MANY_9b_VPN)

POFF_12b_list = random.sample(range(0, (2**12)-1), HOW_MANY_12b_POFF)

#############
##  LISTs  ##
#############

# List of all the VPN[2]
vpn2_list   = list()
# List of the physical memory addresses of the l3 page tabe entries
pt_l3_paddr = list()
# List of the PPN for l3 page table entries
pt_l3_ppn   = list()
# List of all the VPN[1]
vpn1_list   = list()
# List of the physical memory addresses of the l2 page tabe entries
pt_l2_paddr = list()
# List of the PPN for l2 page table entries
pt_l2_ppn   = list()
# List of all the VPN[0]
vpn0_list   = list()
# List of the physical memory addresses of the l1 page tabe entries
pt_l1_paddr = list()
# List of the PPN for l1 page table entries
pt_l1_ppn   = list()
# List of page offset
poff_list   = list()
# List of the physical memory addresses of the data
data_paddr  = list()

# ROOT PPN creation
root_ppn = PPN_44b_list.pop(0)
for idx in range(how_many_vaddr):
  # VPN creation
  vpn2_list   += [VPN_9b_list.pop(0)]
  vpn1_list   += [VPN_9b_list.pop(0)]
  vpn0_list   += [VPN_9b_list.pop(0)]
  poff_list   += [POFF_12b_list.pop(0)]
  # PPNs creation
  pt_l3_ppn   += [PPN_44b_list.pop(0)]
  pt_l2_ppn   += [PPN_44b_list.pop(0)]
  pt_l1_ppn   += [PPN_44b_list.pop(0)]
  # paddrs creation
  pt_l3_paddr += [((root_ppn      << PAGE_OFF_A_LEN)) + ((vpn2_list[-1] << WORD_OFF_A_LEN))]
  pt_l2_paddr += [((pt_l3_ppn[-1] << PAGE_OFF_A_LEN)) + ((vpn1_list[-1] << WORD_OFF_A_LEN))]
  pt_l1_paddr += [((pt_l2_ppn[-1] << PAGE_OFF_A_LEN)) + ((vpn0_list[-1] << WORD_OFF_A_LEN))]
  data_paddr  += [((pt_l1_ppn[-1] << PAGE_OFF_A_LEN)) + (poff_list[-1])]

##############################
##  PTE FILLER AND CONTROL  ##
##############################

pte_msb_filler = "0000000000"
non_leaf_ctrl  = "0000000001"
# Already accessed, dirty, all access permissions, Valid
leaf_ctrl      = "0011001111"

#######################
##  WRITE THE FILES  ##
#######################

with open(ROOT_PPN_FILE_PATH, "w") as rf:
  root_paddr = root_ppn << PAGE_OFF_A_LEN
  rf.write( "{:0>56b}".format(root_paddr) )

with open(VADDR_FILE_PATH, "w") as vf, open(MEMORY_FILE_PATH, "w") as mf:
  for i in range(how_many_vaddr):
    vpn   = "{:0>9b}".format(vpn2_list[i]) + "{:0>9b}".format(vpn1_list[i]) + "{:0>9b}".format(vpn0_list[i]) # + "{:0>12b}".format(poff_list[i])
    # vpn_msb_filler = (64-39) * vpn[0] # 25 * vpn_MSB
    vf.write( vpn + "\n" )
    paddr = "{:0>16x}".format(pt_l3_paddr[i])
    pte   = pte_msb_filler + "{:0>44b}".format(pt_l3_ppn[i]) + non_leaf_ctrl
    mf.write( paddr + " " + pte + "\n" )
  for i in range(how_many_vaddr):
    paddr = "{:0>16x}".format(pt_l2_paddr[i])
    pte   = pte_msb_filler + "{:0>44b}".format(pt_l2_ppn[i]) + non_leaf_ctrl
    mf.write( paddr + " " + pte + "\n" )
  for i in range(how_many_vaddr):
    paddr = "{:0>16x}".format(pt_l1_paddr[i])
    pte   = pte_msb_filler + "{:0>44b}".format(pt_l1_ppn[i]) + leaf_ctrl
    mf.write( paddr + " " + pte + "\n" )
  for i in range(how_many_vaddr):
    paddr = "{:0>16x}".format(data_paddr[i])
    data  = "{:0>64b}".format(random.randint(0, 2**64-1))
    mf.write( paddr + " " + data + "\n" )
