# Use worst-case libraries
set STD_CELLS_DIR "../../../hw/asic/std-cells/db"
set DB_STDCELLS [glob -directory $STD_CELLS_DIR -type {f l} -- "*wc.db"]

set target_library {}
set target_library "$DB_STDCELLS"

# link library
set link_library "* $target_library"

#debug output info
puts "------------------------------------------------------------------"
puts "USED LIBRARIES"
puts $link_library
puts "------------------------------------------------------------------"