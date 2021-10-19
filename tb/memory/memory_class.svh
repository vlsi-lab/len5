// Copyright 2019 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: memory_class.svh
// Author: Matteo Perotti
// Date: 10/11/2019
// Description: memory emulator
// Details: it accesses to a file with sparse addresses and data. This way, it 
//          can emulate a large memory. The file should begin with the lowest 
//          address and end with the highest.

/* UVM report functions */
`include "uvm_macros.svh"
import uvm_pkg::*;

class memory_class;
    /* Calss properties */
    string          memory_file_path;
    logic [31:0]    read_word;
    logic [63:0]    read_doubleword;
    logic [511:0]   read_line;

    /* Constructor */
    function new (string memory_file_path = "./memory.txt");
        this.memory_file_path = memory_file_path;
    endfunction

    /* READ TASKS */

    /* Read a doubleword (64 bits) from the memory */
    function ReadDW (logic [63:0] addr);
        /* Variables */
        int             fd              = 0;    // file descriptor
        int             ret_code        = 0;    // $fopen() return code
        int             done            = 0;    // done flag
        logic [63:0]    read_addr       = 0;    // memory address
        logic [63:0]    read_doubleword = 0;    // memory data

        /* Check address alignment */
        if (addr[2:0] != 3'b000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 64 bits", addr))
            return 1; // exit
        end

        /* Open the memory file */
        fd = $fopen(this.memory_file_path, "r");
        if (fd == 0) begin
            `uvm_fatal("MEMFILE", $sformatf("Cannot open memory file '%s'", this.memory_file_path));
            return 1; // exit
        end

        /* Read address and data from the file */
        while (!done && !$feof(fd)) begin
            ret_code = $fscanf(fd, "%h %b", read_addr, read_doubleword);
            if (!$feof(fd) && ret_code != 2) begin    
                `uvm_error("MEMFILE", "Unexpected memory file format");
                return 1;
            end
            if (read_addr == addr) done = 1;
        end

        /* Close the file */
        $fclose(fd);

        /* Return an error if the line was not found */
        if (!done) begin
            `uvm_error("READMEM", $sformatf("Cannot find requested address 0x%h", addr))
            return 1;
        end

        /* Return the accessed doubleword */
        this.read_doubleword = read_doubleword;

        /* Return with success */
        return 0;
    endfunction

    
    /* Read a word (32 bits) from the memory */
    function ReadW (logic [63:0] addr);
        /* Check address aligment */
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1;
        end

        /* Read a doubleword */
        if (ReadDW({addr[63:4], 3'b000}) != 0) return 1;

        /* Extract the requested word */
        if (addr[2] == 1'b0)    this.read_word = this.read_doubleword[31:0];
        else                    this.read_word = this.read_doubleword[63:32];

        /* Return with success */
        return 0;
    endfunction

    /* Read a cache line (512 bits) from the memory */
    function ReadLine (logic [63:0] addr);
        /* Check address aligment */
        if (addr[5:0] != 9'b000000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1;
        end

        /* Read eight doublewords from the memory */
        for (int i = 0; i < 8; i++) begin
            if (ReadDW(addr + (i << 3)) != 0) return 1;
            this.read_line[64*i +: 64] = this.read_doubleword;
        end

        /* Return with success */
        return 0;
    endfunction

    /* WRITE TASKS */

    /* Write a word (32 bits) to the memory file */
    function WriteW(logic [63:0] addr, logic [31:0] data);
        /* Variables */
        int             fd              = 0;    // file descriptor
        int             ret_code        = 0;    // $fopen() return code
        int             done            = 0;    // done flag
        logic [63:0]    read_addr       = 0;    // memory address
        logic [63:0]    read_doubleword = 0;    // memory data
        logic [63:0]    write_doubleword = 0;   // data to store

        /* Check address alignment */
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1; // exit
        end

        /* Open the memory file */
        fd = $fopen(this.memory_file_path, "r+");
        if (fd == 0) begin
            `uvm_fatal("MEMFILE", $sformatf("Cannot open memory file '%s'", this.memory_file_path));
            return 1; // exit
        end

        /* Read address and data from the file */
        while (!done && !$feof(fd)) begin
            ret_code = $fscanf(fd, "%h %b", read_addr, read_doubleword);
            if (!$feof(fd) && ret_code != 2) begin    
                `uvm_error("MEMFILE", "Unexpected memory file format");
                return 1;
            end
            if (read_addr == {addr[63:3], 3'b000}) done = 1;
        end

        /* If the requested line exists, replace it */
        if (done) begin
            /* Replace the selected word */
            if (addr[2] == 1'b0)    write_doubleword = {read_doubleword[63:32], data};
            else                    write_doubleword = {data, read_doubleword[31:0]};

            /* Move back by 64 characters and write the new data */
            ret_code = $fseek(fd, -64, 1);
            if (ret_code != 0) begin
                `uvm_error("MEMFILE", "Unable to move back file pointer")
                return 1;
            end
            $fwrite(fd, $sformatf("%b\n", write_doubleword));
        end else begin
            /* Initialize the new doubleword */
            if (addr[2] == 1'b0)    write_doubleword = {{32{1'b0}}, data};
            else                    write_doubleword = {data, {32{1'b0}}};

            /* Append the line to the file */
            ret_code = $fseek(fd, 0, 2);
            if (ret_code != 0) begin
                `uvm_error("MEMFILE", "Unable to seek the end of file")
                return 1;
            end
            $fwrite(fd, $sformatf("%h %b\n", addr, write_doubleword));
        end

        /* Close the file */
        $fclose(fd);

        /* Return the accessed doubleword */
        this.read_doubleword = read_doubleword;

        /* Return with success */
        return 0;
    endfunction;

    /* Write a doubleword (64 bits) to the memory file */
    function WriteDW(logic [63:0] addr, logic [63:0] data);
        /* Check address alignment */
        if (addr[2:0] != 3'b000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 64 bits", addr))
            return 1; // exit
        end

        /* Write the two words */
        if (WriteW({addr[63:3], 3'b000}, data[31:0]) != 0) return 1;
        if (WriteW({addr[63:3], 3'b100}, data[63:32]) != 0) return 1;

        /* Return with success */
        return 0;
    endfunction;

    /* Write a cache line (512 bits) to the memory file */
    function WriteLine(logic [63:0] addr, logic [511:0] data);
        /* Check address aligment */
        if (addr[5:0] != 9'b000000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 512 bits", addr))
            return 1;
        end

        /* Write 8 doublewords to the selected address */
        for (int i = 0; i < 8; i++) begin
            if (WriteDW(addr + (i << 3), data[64*i +: 64]) != 0) return 1;
        end

        /* Return with success */
        return 0;
    endfunction;
endclass
