# Use worst-case libraries
set STD_CELLS_DIR "/software/dk/tsmc65/digital/Front_End/timing_power_noise/NLDM/tcbn65lp_200a"
set DB_STDCELLS [glob -directory $STD_CELLS_DIR -type {f l} -- "*.db"]

set target_library {}
set target_library "$DB_STDCELLS"

# link library
set link_library "* $target_library"

#debug output info
puts "------------------------------------------------------------------"
puts "USED LIBRARIES"
puts $link_library
puts "------------------------------------------------------------------"