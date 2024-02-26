proc timing_loop_check { name } {
    # Open the file for reading
    set file_handle [open $name r]

    # Read the last line of the file
    set last_line ""
    while {[gets $file_handle line] != -1} {
        set last_line $line
    }

    # Close the file
    close $file_handle

    # Check if the last line contains '0'
    if {[string match "*0*" $last_line]} {
        puts "Combinational loop detected, exiting..."
        exit
    }
}