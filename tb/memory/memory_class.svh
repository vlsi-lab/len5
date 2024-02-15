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

import len5_pkg::WWIDTH;
import len5_pkg::AWIDTH;
import len5_pkg::BWIDTH;
import len5_pkg::HWWIDTH;
import len5_pkg::DWWIDTH;
import len5_pkg::LWIDTH;

typedef enum int unsigned {
  FILE_MODE_READ,
  FILE_MODE_READ_BINARY,
  FILE_MODE_WRITE
} file_mode_t;

class memory_class;
  // File info
  const local string                     memory_file_path;
  const local int                        fd;
  const local string                     file_line;

  // File data
  logic              [ BWIDTH-1:0] read_byte;
  logic              [HWWIDTH-1:0] read_halfword;
  logic              [ WWIDTH-1:0] read_word;
  logic              [DWWIDTH-1:0] read_doubleword;
  logic              [ LWIDTH-1:0] read_line;

  // Memory data
  // NOTE: delared as static so it's shared by all instances
  // TODO: Update verilator to support static class members
  // static logic       [ BWIDTH-1:0] mem[logic         [AWIDTH-1:0]];
  logic       [BWIDTH-1:0] mem[logic         [AWIDTH-1:0]];

  // METHODS
  // -------

  // Constructor
  function new(string file_path = "./memory.txt");
    this.memory_file_path = file_path;
    this.mem              = '{default: 0};
  endfunction : new

  // Open the memory file
  local function void OpenMemFile(string path, file_mode_t mode);
    // NOTE: prevent Verilator error about mode width in $fopen()
    case (mode)
      FILE_MODE_READ: this.fd = $fopen(path, "r");
      FILE_MODE_READ_BINARY: this.fd = $fopen(path, "rb");
      FILE_MODE_WRITE: this.fd = $fopen(path, "w");
      default: begin
        $display("ERROR: $fopen() mode '%d' not supported", mode);
      end
    endcase
    if (this.fd == 0) begin
      $display("Cannot open memory file '%s'", this.memory_file_path);
    end
  endfunction : OpenMemFile

  // Close the memory file
  local function void CloseMemFile();
    $fclose(this.fd);
  endfunction : CloseMemFile

  // Load memory wrapper
  function int LoadMem(logic [AWIDTH-1:0] offs = 0);
    string path = this.memory_file_path;
    string ext = path.substr(path.len() - 3, path.len() - 1);
    // Choose the memory load method based on the file extension
    if (ext.compare("txt") == 0) begin
      return this.LoadMemTxt();
    end else if (ext.compare("hex") == 0) begin
      return this.LoadMemHex();
    end else begin
      return this.LoadMemBin(offs);
    end
  endfunction : LoadMem

  // Load the memory content from a memory dump file (e.g., the output of 'objcopy -O binary')
  local function int LoadMemBin(logic [AWIDTH-1:0] offs = 0);
    string             path = this.memory_file_path;
    int                ret_code = 0;
    logic [AWIDTH-1:0] addr = offs;
    logic [       7:0] frame_buff   [512];  // read 512 bytes at a time

    // Open the memory file as binary
    this.OpenMemFile(path, FILE_MODE_READ_BINARY);

    // Store the memory bytes
    do begin
      // Read multiple bytes at a time to reduce overhead
      ret_code = $fread(frame_buff, this.fd);
      for (int i = 0; i < ret_code; i++) begin
        this.mem[addr+{32'b0, i}] = frame_buff[i];
      end
      addr += {32'b0, ret_code};
    end while (ret_code != 0);

    // Close the memory file
    this.CloseMemFile();

    // Return the number of loaded bytes
    return this.mem.num();
  endfunction : LoadMemBin

  // Scan one line and return address and data
  local function bit ScanMemLine(ref logic [AWIDTH-1:0] addr, ref logic [WWIDTH-1:0] data);
    int ret_code = 0;

    // Scan the next line in the memory
    if ($fgets(this.file_line, this.fd) < 0) begin
      $display("ERROR: Unexpected memory file format ($fgets)");
      return 1;
    end
    ret_code = $sscanf(this.file_line, "%h %h", addr, data);
    if (!$feof(this.fd) && ret_code != 2) begin
      $display("ERROR: Unexpected memory file format ($fscanf)");
      return 1;
    end
    return 0;
  endfunction : ScanMemLine

  // Load the memory content from a text file ('address data' pairs)
  local function int LoadMemTxt();
    string path = this.memory_file_path;
    logic [AWIDTH-1:0] waddr, baddr;
    logic [WWIDTH-1:0] data;

    // Open the memory file
    OpenMemFile(path, FILE_MODE_READ);

    // Scan each line and load the data into the memory array
    while (!$feof(
        this.fd
    )) begin
      if (ScanMemLine(waddr, data) != 0) return -1;
      // Store the read bytes
      for (int i = 0; i < (WWIDTH >> 3); i++) begin
        baddr           = waddr + {32'b0, i};
        this.mem[baddr] = data[BWIDTH*(i+1)-1-:BWIDTH];
      end
    end

    // Close the file
    CloseMemFile();

    // Return the number of loaded bytes
    $display("Loaded %0d bytes (%0d words)", this.mem.num(), this.mem.num() >> 2);
    return this.mem.num();
  endfunction : LoadMemTxt
  
  // Load the memory content from a text file ('address data' pairs)
  local function int LoadMemHex();
    string path = this.memory_file_path;

    // Load memory file content
    $readmemh(path, this.mem);

    // Return the number of loaded bytes
    $display("Loaded %0d bytes (%0d words)", this.mem.num(), this.mem.num() >> 2);
    return this.mem.num();
  endfunction : LoadMemHex

  // READ FUNCTIONS
  // --------------
  // Return value:
  // 0 - success
  // 1 - address misaligned
  // 2 - access fault

  // Read a byte
  function int ReadB(logic [AWIDTH-1:0] addr);
    // Search the byte in memory
    if (this.mem.exists(addr) == 0) begin
      $display($sformatf("Reading uninitialized byte at address 0x%h", addr),);
      this.read_byte = '0;
      return 2;
    end

    // Save the accessed byte
    this.read_byte = this.mem[addr];
    return 0;
  endfunction : ReadB

  // Read a halfword
  function int ReadHW(logic [AWIDTH-1:0] addr);
    logic [ AWIDTH-1:0] baddr;  // word address
    logic [HWWIDTH-1:0] hw;
    int                 ret;

    // Check address alignment
    if (addr[0] != 1'b0) begin
      $display("ERROR: Halfword address 0x%h is NOT aligned on 16 bits", addr);
      return 1;  // exit
    end

    // Read bytes from memory
    for (int i = 0; i < (HWWIDTH >> 3); i++) begin
      baddr                      = addr + {32'b0, i};

      // Read current byte
      ret                        = this.ReadB(baddr);
      hw[BWIDTH*(i+1)-1-:BWIDTH] = this.read_byte;
    end

    // Save the requested halfword
    this.read_halfword = hw;
    return ret;
  endfunction : ReadHW

  // Read a word
  function int ReadW(logic [AWIDTH-1:0] addr);
    logic [AWIDTH-1:0] baddr;  // word address
    logic [WWIDTH-1:0] w;
    int                ret;

    // Check address alignment
    if (addr[1:0] != 2'b00) begin
      $display("ERROR: Word address 0x%h is NOT aligned on 32 bits", addr);
      return 1;  // exit
    end

    // Read bytes from memory
    for (int i = 0; i < (WWIDTH >> 3); i++) begin
      baddr                     = addr + {32'b0,i};

      // Read current byte
      ret                       = this.ReadB(baddr);
      w[BWIDTH*(i+1)-1-:BWIDTH] = this.read_byte;
    end

    // Save the requested word
    this.read_word = w;
    return ret;
  endfunction : ReadW

  // Read a doubleword
  function int ReadDW(logic [AWIDTH-1:0] addr);
    logic [ AWIDTH-1:0] baddr;  // word address
    logic [DWWIDTH-1:0] dw;
    int                 ret;

    // Check address alignment
    if (addr[2:0] != 3'b000) begin
      $display("ERROR: Doubleword address 0x%h is NOT aligned on 64 bits", addr);
      return 1;  // exit
    end

    // Read bytes from memory
    for (int i = 0; i < (DWWIDTH >> 3); i++) begin
      baddr                      = addr + {32'b0,i};

      // Read current byte
      ret                        = this.ReadB(baddr);
      dw[BWIDTH*(i+1)-1-:BWIDTH] = this.read_byte;
    end

    // Save the requested word
    this.read_doubleword = dw;
    return ret;
  endfunction : ReadDW

  // Read a line
  function int ReadLine(logic [AWIDTH-1:0] addr);
    logic [AWIDTH-1:0] baddr;  // word address
    logic [LWIDTH-1:0] l;
    int                ret;

    // Check address alignment
    if (addr[5:0] != 6'b000000) begin
      $display("ERROR: Line address 0x%h is NOT aligned on 512 bits", addr);
      return 1;  // exit
    end

    // Read bytes from memory
    for (int i = 0; i < (LWIDTH >> 3); i++) begin
      baddr                     = addr + {32'b0, i};

      // Read current byte
      ret                       = this.ReadB(baddr);
      l[BWIDTH*(i+1)-1-:BWIDTH] = this.read_byte;
    end

    // Save the requested word
    this.read_line = l;
    return ret;
  endfunction : ReadLine

  // WRITE FUNCTIONS
  // ---------------
  // Return value:
  // 0 - success
  // 1 - address misaligned
  // 2 - access fault

  // Write a byte
  function int WriteB(logic [AWIDTH-1:0] addr, logic [BWIDTH-1:0] data);
    // Replace the requested byte in memory
    this.mem[addr] = data;
    return 0;
  endfunction : WriteB

  // Write a halfword
  function int WriteHW(logic [AWIDTH-1:0] addr, logic [HWWIDTH-1:0] data);
    logic [AWIDTH-1:0] baddr;  // word address

    // Check address alignment
    if (addr[0] != 1'b0) begin
      $display("ERROR: Halfword address 0x%h is NOT aligned on 16 bits", addr);
      return 1;  // exit
    end

    // Store the bytes
    for (int i = 0; i < (HWWIDTH >> 3); i++) begin
      baddr = addr + {32'b0, i};
      if (0 != WriteB(baddr, data[BWIDTH*(i+1)-1-:BWIDTH])) return 2;
    end
    return 0;
  endfunction : WriteHW

  // Write word
  function int WriteW(logic [AWIDTH-1:0] addr, logic [WWIDTH-1:0] data);
    logic [AWIDTH-1:0] baddr;  // word address

    // Check address alignment
    if (addr[1:0] != 2'b00) begin
      $display("ERROR: Word address 0x%h is NOT aligned on 32 bits", addr);
      return 1;  // exit
    end

    // Store the bytes
    for (int i = 0; i < (WWIDTH >> 3); i++) begin
      baddr = addr + {32'b0, i};
      if (0 != WriteB(baddr, data[BWIDTH*(i+1)-1-:BWIDTH])) return 2;
    end
    return 0;
  endfunction : WriteW

  // Write doubleword
  function int WriteDW(logic [AWIDTH-1:0] addr, logic [DWWIDTH-1:0] data);
    logic [AWIDTH-1:0] baddr;  // word address

    // Check address alignment
    if (addr[2:0] != 3'b000) begin
      $display("ERROR: Doubleword address 0x%h is NOT aligned on 64 bits", addr);
      return 1;  // exit
    end

    // Store the bytes
    for (int i = 0; i < (DWWIDTH >> 3); i++) begin
      baddr = addr + {32'b0, i};
      if (0 != WriteB(baddr, data[BWIDTH*(i+1)-1-:BWIDTH])) return 2;
    end
    return 0;
  endfunction : WriteDW

  // Store entire line
  function int WriteLine(logic [AWIDTH-1:0] addr, logic [LWIDTH-1:0] data);
    logic [AWIDTH-1:0] baddr;  // word address

    // Check address alignment
    if (addr[5:0] != 6'b000000) begin
      $display("ERROR: Line address 0x%h is NOT aligned on 512 bits", addr);
      return 1;  // exit
    end

    // Store the bytes
    for (int i = 0; i < (LWIDTH >> 3); i++) begin
      baddr = addr + {32'b0, i};
      if (0 != WriteB(baddr, data[BWIDTH*(i+1)-1-:BWIDTH])) return 2;
    end
    return 0;
  endfunction : WriteLine

  // Print functions
  // ---------------

  // Dump memory content to file
  function bit PrintMem(string out_path = "./memory_dump.txt");
    logic [AWIDTH-1:0] baddr, waddr;
    logic [WWIDTH-1:0] w;
    baddr = '0;
    // Open the output file
    OpenMemFile(out_path, FILE_MODE_WRITE);

    // Check if the memory is empty
    if (this.mem.first(baddr) == 0) begin
      $display("ERROR: Memory is empty");
      return 1;
    end

    // Iterate over the memory
    w = 'x;
    do begin
      w[BWIDTH*({30'b0, baddr[1:0]} + 1)-1-:BWIDTH] = this.mem[baddr];
      // $display("cnt: %0d | buff: %h | baddr: %h | data: %h", baddr[1:0], w, baddr, this.mem[baddr]);
      // Print the word and reset the word buffer
      if (baddr[1:0] == 2'b11) begin
        waddr = {baddr[AWIDTH-1:2], 2'b00};
        $fdisplay(this.fd, "%016h %08h", waddr, w);
        w = 'x;
      end
    end while (this.mem.next(
        baddr
    ) == 1);

    // Close the file
    CloseMemFile();
    return 0;
  endfunction : PrintMem
endclass
