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
// Author: Matteo Perotti, Michele Caon
// Date: 10/11/2019
// Description: memory emulator
// Details: it accesses to a file with sparse addresses and data. This way, it 
//          can emulate a large memory. The file should begin with the lowest 
//          address and end with the highest.

/* UVM report functions */
`include "uvm_macros.svh"
import uvm_pkg::*;

class memory_class #(
    parameter WWIDTH = 32,
    parameter AWIDTH = 64    
);
    // PROPERTIES
    // ----------

    // Parameters
    localparam  DWWIDTH = WWIDTH << 1;
    localparam  LWIDTH  = WWIDTH << 4;

    // File info
    local string    memory_file_path;
    local int       fd;
    local string    file_line;

    // File data
    local logic [WWIDTH-1:0]    word_buf;
    logic [WWIDTH-1:0]          read_word;
    logic [DWWIDTH-1:0]         read_doubleword;
    logic [LWIDTH-1:0]          read_line;

    // Memory data
    logic [WWIDTH-1:0]  mem [logic [AWIDTH-1:0]];
    string              insn_str [logic [AWIDTH-1:0]];

    // METHODS
    // -------

    // Constructor
    function new (string memory_file_path = "./memory.txt");
        this.memory_file_path = memory_file_path;
    endfunction

    // Open the memory file
    local function void OpenMemFile(string mode = "r", string file = this.memory_file_path);
        this.fd = $fopen(file, mode);
        if (this.fd == 0) begin
            `uvm_fatal("MEMFILE", $sformatf("Cannot open memory file '%s'", this.memory_file_path));
        end
    endfunction: OpenMemFile

    // Close the memory file
    local function void CloseMemFile();
        $fclose(this.fd);
    endfunction: CloseMemFile

    // Load the memory file
    function int LoadMem(string file);
        return 0;
    endfunction: LoadMem

    /* READ TASKS */

    // Find a word (32 bits) in memory file
    local function bit FindW (logic [AWIDTH-1:0] addr);
        logic [WWIDTH-1:0]  w;
        logic [AWIDTH-1:0]  read_addr;
        int                 ret_code = 0;

        /* Check address aligment */
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1;
        end

        // Search the requested address
        if ($rewind(this.fd)) `uvm_fatal("MEMFILE", "$rewind() failed");
        while (!$feof(this.fd)) begin
            if ($fgets(this.file_line, this.fd) < 0) begin
                `uvm_error("MEMFILE", "Unexpected memory file format ($fgets)");
                return 1;
            end
            ret_code = $sscanf(this.file_line, "%h %h", read_addr, w);
            if (!$feof(this.fd) && ret_code != 2) begin    
                `uvm_error("MEMFILE", "Unexpected memory file format ($fscanf)");
                return 1;
            end
            if (read_addr == addr) begin 
                this.word_buf = w;  // save the word content
                return 0;
            end
        end

        // Return with error (word not found)
        return 1;
    endfunction

    // Read a word (32 bits) from the memory
    function bit ReadW(logic [AWIDTH-1:0] addr);
        // Check the address alignment
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1;
        end

        OpenMemFile();

        // Find the requested word in memory
        if (FindW(addr)) begin
            `uvm_error("MEMREAD", $sformatf("Cannot find word at address 0x%h", addr));
            return 1;
        end
        
        CloseMemFile();

        // Save the read word
        this.read_word = this.word_buf;

        // Return success
        return 0;
    endfunction: ReadW

    /* Read a doubleword (64 bits) from the memory */
    function bit ReadDW (logic [AWIDTH-1:0] addr);
        logic [DWWIDTH-1:0] dw = 0;    // memory data

        // Check address alignment
        if (addr[2:0] != 3'b000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 64 bits", addr))
            return 1; // exit
        end

        OpenMemFile();

        // Read lower word
        if (FindW(addr)) begin
            `uvm_error("MEMREAD", $sformatf("Cannot find word at address 0x%h", addr));
            return 1;
        end
        dw[WWIDTH-1:0]  = this.word_buf;
        
        // Read upper word
        if (FindW(addr | 64'h04)) begin
            `uvm_error("MEMREAD", $sformatf("Cannot find word at address 0x%h", addr | 64'h4));
            return 1;
        end
        dw[DWWIDTH-1:WWIDTH]    = this.word_buf;

        CloseMemFile();

        // Save accessed double word
        this.read_doubleword    = dw;

        // Return 
        return 0;
    endfunction

    /* Read a cache line (512 bits) from the memory */
    function bit ReadLine (logic [AWIDTH-1:0] addr);
        /* Check address aligment */
        if (addr[5:0] != 9'b000000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1;
        end

        OpenMemFile();

        /* Read sixteen words from the memory */
        for (int i = 0; i < 16; i++) begin
            if (FindW(addr + (i << 2))) begin
                `uvm_error("MEMREAD", $sformatf("Cannot find word at address 0x%h", addr | 64'h4));
                return 1;
            end
            this.read_line[32*i +: 32] = this.word_buf;
        end

        CloseMemFile();

        /* Return with success */
        return 0;
    endfunction

    /* WRITE TASKS */

    /* Write a word (32 bits) to the memory file */
    function bit WriteW(logic [AWIDTH-1:0] addr, logic [WWIDTH-1:0] data);
        /* Variables */
        int                 ret_code        = 0;    // $fopen() return code
        int                 done            = 0;    // done flag
        logic [AWIDTH-1:0]  read_addr       = 0;    // memory address
        logic [DWWIDTH-1:0] dw = 0;    // memory data
        logic [DWWIDTH-1:0] write_doubleword = 0;   // data to store
        string              line_buf;

        // Check address alignment
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1; // exit
        end

        // Update the line buffer
        $sformat(line_buf, "%016h %08h", addr, data);

        OpenMemFile("r+");

        // Find the requested word in memory
        if (!FindW(addr)) begin
            // Go back one line
            if ($fseek(this.fd, -this.file_line.len(), 1)) begin
                `uvm_fatal("MEMFILE", "fseek() failed");
            end
            // Update the line content
            $fwrite(this.fd, line_buf);
        end else $fdisplay(this.fd, line_buf);

        CloseMemFile();

        /* Return with success */
        return 0;
    endfunction;

    /* Write a doubleword (64 bits) to the memory file */
    function bit WriteDW(logic [AWIDTH-1:0] addr, logic [DWWIDTH-1:0] data);
        /* Check address alignment */
        if (addr[2:0] != 3'b000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 64 bits", addr))
            return 1; // exit
        end

        /* Write the two words */
        if (WriteW({addr[63:3], 3'b000}, data[WWIDTH-1:0]) != 0) return 1;
        if (WriteW({addr[63:3], 3'b100}, data[DWWIDTH-1:WWIDTH]) != 0) return 1;

        /* Return with success */
        return 0;
    endfunction;

    /* Write a cache line (512 bits) to the memory file */
    function bit WriteLine(logic [AWIDTH-1:0] addr, logic [LWIDTH-1:0] data);
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

    // Print functions
    // ---------------

    // Print the last w/dw/line fetched
    function string PrintW();
        string str;
        $sformat(str, "%08x", this.read_word);
        return str;
    endfunction: PrintW
    
    function string PrintDW();
        string str;
        $sformat(str, "%016x", this.read_doubleword);
        return str;
    endfunction: PrintDW

    function string PrintLine();
        string str;
        $sformat(str, "%0128x", this.read_line);
        return str;
    endfunction: PrintLine
endclass
