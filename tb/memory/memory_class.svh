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
    localparam  BWIDTH  = 8;
    localparam  HWWIDTH = WWIDTH >> 1;
    localparam  DWWIDTH = WWIDTH << 1;
    localparam  LWIDTH  = WWIDTH << 4;

    // File info
    local string    memory_file_path;
    local int       fd;
    local string    file_line;

    // File data
    local logic [WWIDTH-1:0]    word_buf;
    logic [BWIDTH-1:0]          read_byte;
    logic [HWWIDTH-1:0]         read_halfword;
    logic [WWIDTH-1:0]          read_word;
    logic [DWWIDTH-1:0]         read_doubleword;
    logic [LWIDTH-1:0]          read_line;

    // Memory data
    // NOTE: delared as static so it's shared by all instances
    static logic [BWIDTH-1:0]   mem [logic [AWIDTH-1:0]];

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
        logic [AWIDTH-1:0]  waddr, baddr;
        logic [WWIDTH-1:0]  data;

        // Open the memory file
        OpenMemFile("r", file);

        // Scan each line and load the data into the memory array
        while (!$feof(this.fd)) begin
            if (ScanMemLine(waddr, data) != 0) return -1;
            // Store the read bytes
            for (int i = 0; i<(WWIDTH>>3); i++) begin
                baddr = waddr + i;
                this.mem[baddr] = data[BWIDTH*(i+1)-1-:BWIDTH];
            end
        end

        // Close the file
        CloseMemFile();

        // Return the number of loaded bytes
        `uvm_info("MEMLOAD", $sformatf("Loaded %0d bytes (%0d words)", this.mem.num(), this.mem.num() >> 2), UVM_HIGH);
        return this.mem.num();
    endfunction: LoadMem

    // READ FUNCTIONS
    // --------------
    // Return value:
    // 0 - success
    // 1 - address misaligned
    // 2 - access fault

    // Read a byte
    function int ReadB(logic [AWIDTH-1:0] addr);
        // Search the byte in memory
        if (!this.mem.exists(addr)) begin
            `uvm_error("MEMREAD", $sformatf("Cannot find byte at address 0x%h", addr));
            return 2;
        end

        // Save the accessed byte
        this.read_byte  = this.mem[addr];
        return 0;
    endfunction: ReadB

    // Read a halfword
    function int ReadHW(logic [AWIDTH-1:0] addr);
        logic [AWIDTH-1:0]  baddr; // word address
        logic [HWWIDTH-1:0] hw;
        int                 ret;

        // Check address alignment
        if (addr[0] != 1'b0) begin
            `uvm_error("MISALIGNED", $sformatf("Halfword address 0x%h is NOT aligned on 16 bits", addr))
            return 1; // exit
        end

        // Read bytes from memory
        for (int i = 0; i < (HWWIDTH>>3); i++) begin
            baddr   = addr + i;

            // Read current byte
            ret     = this.ReadB(baddr);
            if (ret != 0) begin
                `uvm_error("MEM ACCESS", $sformatf("Unable to find halfword at %h", addr));
                return ret;
            end

            // Save current byte
            hw [BWIDTH*(i+1)-1-:BWIDTH] = this.read_byte;
        end

        // Save the requested halfword
        this.read_halfword  = hw;
        return 0;
    endfunction: ReadHW

    // Read a word
    function int ReadW(logic [AWIDTH-1:0] addr);
        logic [AWIDTH-1:0]  baddr; // word address
        logic [WWIDTH-1:0] w;
        int                 ret;

        // Check address alignment
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Word address 0x%h is NOT aligned on 32 bits", addr))
            return 1; // exit
        end

        // Read bytes from memory
        for (int i = 0; i < (WWIDTH>>3); i++) begin
            baddr   = addr + i;

            // Read current byte
            ret     = this.ReadB(baddr);
            if (ret != 0) begin
                `uvm_error("MEM ACCESS", $sformatf("Unable to find word at %h", addr));
                return ret;
            end

            // Save current byte
            w [BWIDTH*(i+1)-1-:BWIDTH] = this.read_byte;
        end

        // Save the requested word
        this.read_word  = w;
        return 0;
    endfunction: ReadW

    // Read a doubleword
    function int ReadDW(logic [AWIDTH-1:0] addr);
        logic [AWIDTH-1:0]  baddr; // word address
        logic [DWWIDTH-1:0] dw;
        int                 ret;

        // Check address alignment
        if (addr[2:0] != 3'b000) begin
            `uvm_error("MISALIGNED", $sformatf("Doubleword address 0x%h is NOT aligned on 64 bits", addr))
            return 1; // exit
        end

        // Read bytes from memory
        for (int i = 0; i < (DWWIDTH>>3); i++) begin
            baddr   = addr + i;

            // Read current byte
            ret     = this.ReadB(baddr);
            if (ret != 0) begin
                `uvm_error("MEM ACCESS", $sformatf("Unable to find doubleword at %h", addr));
                return ret;
            end

            // Save current byte
            dw [BWIDTH*(i+1)-1-:BWIDTH] = this.read_byte;
        end

        // Save the requested word
        this.read_doubleword  = dw;
        return 0;
    endfunction: ReadDW

    // Read a line
    function int ReadLine(logic [AWIDTH-1:0] addr);
        logic [AWIDTH-1:0]  baddr; // word address
        logic [LWIDTH-1:0]  l;
        int                 ret;

        // Check address alignment
        if (addr[5:0] != 9'b000000) begin
            `uvm_error("MISALIGNED", $sformatf("Line address 0x%h is NOT aligned on 512 bits", addr))
            return 1; // exit
        end

        // Read bytes from memory
        for (int i = 0; i < (LWIDTH>>3); i++) begin
            baddr   = addr + i;

            // Read current byte
            ret     = this.ReadB(baddr);
            if (ret != 0) begin
                `uvm_error("MEM ACCESS", $sformatf("Unable to find line at %h", addr));
                return ret;
            end

            // Save current byte
            l [BWIDTH*(i+1)-1-:BWIDTH] = this.read_byte;
        end

        // Save the requested word
        this.read_line  = l;
        return 0;
    endfunction: ReadLine

    // WRITE FUNCTIONS
    // ---------------
    // Return value:
    // 0 - success
    // 1 - address misaligned
    // 2 - access fault

    // Write a byte
    function void WriteB(logic [AWIDTH-1:0] addr, logic [BWIDTH-1:0] data);
        // Replace the requested byte in memory
        this.mem[addr]   = data;
    endfunction: WriteB
    
    // Write a halfword
    function int WriteHW(logic [AWIDTH-1:0] addr, logic [HWWIDTH-1:0] data);
        logic [AWIDTH-1:0]  baddr; // word address
        int                 ret;

        // Check address alignment
        if (addr[0] != 1'b0) begin
            `uvm_error("MISALIGNED", $sformatf("Halfword address 0x%h is NOT aligned on 16 bits", addr))
            return 1; // exit
        end

        // Store the bytes
        for (int i = 0; i < (HWWIDTH>>3); i++) begin
            baddr   = addr + i;
            WriteB(baddr, data[BWIDTH*(i+1)-1-:BWIDTH]);
        end
        return 0;
    endfunction: WriteHW

    // Write word
    function int WriteW(logic [AWIDTH-1:0] addr, logic [WWIDTH-1:0] data);
        logic [AWIDTH-1:0]  baddr; // word address
        int                 ret;

        // Check address alignment
        if (addr[1:0] != 2'b00) begin
            `uvm_error("MISALIGNED", $sformatf("Word address 0x%h is NOT aligned on 32 bits", addr))
            return 1; // exit
        end

        // Store the bytes
        for (int i = 0; i < (WWIDTH>>3); i++) begin
            baddr   = addr + i;
            WriteB(baddr, data[BWIDTH*(i+1)-1-:BWIDTH]);
        end
        return 0;
    endfunction: WriteW

    // Write doubleword
    function int WriteDW(logic [AWIDTH-1:0] addr, logic [DWWIDTH-1:0] data);
        logic [AWIDTH-1:0]  baddr; // word address
        int                 ret;

        // Check address alignment
        if (addr[2:0] != 3'b000) begin
            `uvm_error("MISALIGNED", $sformatf("Doubleword address 0x%h is NOT aligned on 64 bits", addr))
            return 1; // exit
        end

        // Store the bytes
        for (int i = 0; i < (DWWIDTH>>3); i++) begin
            baddr   = addr + i;
            WriteB(baddr, data[BWIDTH*(i+1)-1-:BWIDTH]);
        end
        return 0;
    endfunction: WriteDW

    // Store entire line
    function int WriteLine(logic [AWIDTH-1:0] addr, logic [LWIDTH-1:0] data);
        logic [AWIDTH-1:0]  baddr; // word address
        int                 ret;

        // Check address alignment
        if (addr[5:0] != 9'b000000) begin
            `uvm_error("MISALIGNED", $sformatf("Line address 0x%h is NOT aligned on 512 bits", addr))
            return 1; // exit
        end

        // Store the bytes
        for (int i = 0; i < (LWIDTH>>3); i++) begin
            baddr   = addr + i;
            WriteB(baddr, data[BWIDTH*(i+1)-1-:BWIDTH]);
        end
        return 0;
    endfunction: WriteLine

    // Print functions
    // ---------------

    // Dump memory content to file
    function bit PrintMem(string out_path = this.memory_file_path);
        logic [AWIDTH-1:0]  baddr, waddr;
        logic [WWIDTH-1:0]  w;

        // Open the output file
        OpenMemFile("w", out_path);

        // Check if the memory is empty
        if (!this.mem.first(baddr)) begin
            `uvm_error("MEMWRITE", "Memory is empty");
            return 1;
        end

        // Iterate over the memory
        w       = 'x;
        do begin
            w[BWIDTH*(baddr[1:0]+1)-1-:BWIDTH] = this.mem[baddr];
            // $display("cnt: %0d | buff: %h | baddr: %h | data: %h", baddr[1:0], w, baddr, this.mem[baddr]);
            // Print the word and reset the word buffer
            if (baddr[1:0] == 2'b11) begin
                waddr = {baddr[AWIDTH:2], 2'b00};
                $fdisplay(this.fd, "%016h %08h", waddr, w);
                w = 'x;
            end
        end while (this.mem.next(baddr));

        // Close the file
        CloseMemFile();
        return 0;
    endfunction: PrintMem
endclass
