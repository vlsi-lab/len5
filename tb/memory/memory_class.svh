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
// Author: Michele Caon
// Date: 25/06/2022
// Description: memory emulator
// Details: memory modeled as SystemVerilog associative array to support
//          sparse data.

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
    // NOTE: delared as static so it's shared by all instances
    static logic [WWIDTH-1:0]   mem [logic [AWIDTH-1:0]];

    // METHODS
    // -------

    // Constructor
    function new (string memory_file_path = "./memory.txt");
        this.memory_file_path = memory_file_path;
        this.mem = {};
    endfunction: new

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

    // Scan one line and return address and data
    local function bit ScanMemLine(ref logic [AWIDTH-1:0] addr, ref logic [WWIDTH-1:0] data);
        int ret_code = 0;

        // Scan the next line in the memory
        if ($fgets(this.file_line, this.fd) < 0) begin
            `uvm_error("MEMFILE", "Unexpected memory file format ($fgets)");
            return 1;
        end
        ret_code = $sscanf(this.file_line, "%h %h", addr, data);
        if (!$feof(this.fd) && ret_code != 2) begin    
            `uvm_error("MEMFILE", "Unexpected memory file format ($fscanf)");
            return 1;
        end
        return 0;
    endfunction: ScanMemLine

    // Load the memory file
    function int LoadMem(string file = this.memory_file_path);
        logic [AWIDTH-1:0]  addr;
        logic [WWIDTH-1:0]  data;
        int                 data_cnt = 0;

        // Open the memory file
        OpenMemFile("r", file);

        // Scan each line and load the data into the memory array
        while (!$feof(this.fd)) begin
            if (ScanMemLine(addr, data) != 0) return -1;
            mem[addr] = data;
            data_cnt++;
        end

        // Close the file
        CloseMemFile();

        return data_cnt;
    endfunction: LoadMem

    // READ FUNCTIONS
    // --------------

    // Read a word
    function bit ReadW(logic [AWIDTH-1:0] addr);
        // Check address alignment
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1;
        end

        // Search word
        if (!this.mem.exists(addr)) begin
            `uvm_error("MEMREAD", $sformatf("Cannot find word at address 0x%h", addr));
            return 1;
        end

        // Save the accessed word
        this.read_word = mem[addr];

        // Return
        return 0;
    endfunction: ReadW

    // Read a doubleword
    function bit ReadDW(logic [AWIDTH-1:0] addr);
        logic [DWWIDTH-1:0] dw = 0;    // memory doubleword
        logic [AWIDTH-1:0]  low_addr    = addr;
        logic [AWIDTH-1:0]  high_addr   = addr | 'h04;

        // Check address alignment
        if (addr[2:0] != 3'b000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 64 bits", addr))
            return 1; // exit
        end

        // Read the lower word
        if (!this.mem.exists(low_addr)) begin
            `uvm_error("MEMREAD", $sformatf("Cannot find word at address 0x%h", low_addr));
            return 1;
        end
        dw[WWIDTH-1:0]  = mem[low_addr];

        // Read the upper word
        if (!this.mem.exists(high_addr)) begin
            `uvm_error("MEMREAD", $sformatf("Cannot find word at address 0x%h", high_addr));
            return 1;
        end
        dw[DWWIDTH-1:WWIDTH] = mem[high_addr];

        // Save the accessed doubleword
        this.read_doubleword    = dw;

        // Return
        return 0;
    endfunction: ReadDW

    // Read a line
    function bit ReadLine(logic [AWIDTH-1:0] addr);
        logic [LWIDTH-1:0]  line;
        logic [AWIDTH-1:0]  waddr;

        // Check address alignment
        if (addr[5:0] != 9'b000000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1;
        end

        // Access the requested line
        for (int i = 0; i < LWIDTH/WWIDTH; i++) begin
            waddr = addr + (i << 2);
            if (!this.mem.exists(waddr)) begin
                `uvm_error("MEMREAD", $sformatf("Cannot find word at address 0x%h", waddr));
                return 1;
            end
            line[WWIDTH*i +: WWIDTH]    = mem[waddr];
        end

        // Save the accessed line
        this.read_line  = line;

        // Return
        return 0;
    endfunction: ReadLine

    // WRITE FUNCTIONS
    // ---------------

    // Write word
    function bit WriteW(logic [AWIDTH-1:0] addr, logic [WWIDTH-1:0] data);
        // Check address alignment
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 32 bits", addr))
            return 1; // exit
        end

        // Store the word
        mem[addr] = data;

        // Return
        return 0;
    endfunction: WriteW

    // Write doubleword
    function bit WriteDW(logic [AWIDTH-1:0] addr, logic [DWWIDTH-1:0] data);
        // Check address alignment
        if (addr[2:0] != 3'b000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 64 bits", addr))
            return 1; // exit
        end

        // Store the doubleword
        mem[addr]           = data[WWIDTH-1:0];
        mem[addr | 'h04]    = data[DWWIDTH-1:WWIDTH];

        // Return
        return 0;
    endfunction: WriteDW

    // Store entire line
    function bit WriteLine(logic [AWIDTH-1:0] addr, logic [LWIDTH-1:0] data);
        logic [AWIDTH-1:0]  waddr;
        
        // Ceck address alignment
        if (addr[5:0] != 9'b000000) begin
            `uvm_error("MISALIGNED", $sformatf("Address 0x%h is NOT aligned on 512 bits", addr))
            return 1;
        end

        // Store the line
        for (int i = 0; i < LWIDTH/WWIDTH; i++) begin
            waddr   = addr + (i << 2);
            mem[waddr]  = data[WWIDTH*(i+1)-1 -: WWIDTH];
        end

        // Return
        return 0;
    endfunction: WriteLine

    // Print functions
    // ---------------

    // Dump memory content to file
    function bit PrintMem(string out_path = this.memory_file_path);
        logic [AWIDTH-1:0]  waddr;

        // Open the output file
        OpenMemFile("w", out_path);

        // Print the memory content
        if (!mem.first(waddr)) begin
            `uvm_error("MEMWRITE", "Memory is empty");
            return 1;
        end
        do begin
            $fdisplay(this.fd, "%016h %08h", waddr, mem[waddr]);
        end while (mem.next(waddr));

        // Close the file
        CloseMemFile();

        // Return
        return 0;
    endfunction: PrintMem
endclass
