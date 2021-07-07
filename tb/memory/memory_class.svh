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

class memory_class;
  // Class properties
  string        memory_file_path;
  logic [63:0]  read_doubleword;
  logic [511:0] read_line;

  // Class constructor
  function new (string memory_file_path = "./memory.txt");
    this.memory_file_path = memory_file_path;
  endfunction

  // Read a DW from the memory
  task ReadDW (logic [63:0] addr);
    // Variables
    int           fd;
    int           ret_code;
    int           done;
    logic [63:0]  read_addr;
    logic [63:0]  read_doubleword;
    // Opening the memory file
    fd = $fopen(this.memory_file_path, "r");
    if (fd) begin
      // Accessing the memory...
      done     = 0;
      ret_code = 0;
      while (!done && (ret_code != -1)) begin
        ret_code = $fscanf(fd, "%h %b", read_addr, read_doubleword);
        if (ret_code == -1) $error("Can't find the requested line in the memory file.\n");
        if (read_addr == addr) done = 1;
      end
      // Memory access done
      $fclose(fd);
      // Return the line
      this.read_doubleword = read_doubleword;
    end else $error("Memory file can't be opened.");
  endtask

  // Read a line from the memory
  task ReadLine (logic [63:0] addr);
    // Variables
    int           fd;
    int           ret_code;
    int           done;
    logic [63:0]  read_addr;
    logic [63:0]  read_doubleword [8];
    logic [511:0] read_line;
    // Opening the memory file
    fd = $fopen(this.memory_file_path, "r");
    if (fd) begin
      // Accessing the memory...
      done     = 0;
      ret_code = 0;
      while (!done && (ret_code != -1)) begin
        ret_code = $fscanf(fd, "%h %b", read_addr, read_doubleword[0]);
        if (ret_code == -1) $error("Can't find the requested line in the memory file.\n");
        if (read_addr == addr) begin
          // Read the other doublewords of the line
          for (int k = 1; k < 8; k++) begin
            if ($fscanf(fd, "%h %b", read_addr, read_doubleword[k]) == -1) $error("Broken line into memory at doubleword %d of the requested line.\n", k);
          end
          done = 1;
        end
      end
      // Memory access done
      $fclose(fd);
      // Return the line
      this.read_line = {read_doubleword[7], read_doubleword[6], read_doubleword[5], read_doubleword[4], read_doubleword[3], read_doubleword[2], read_doubleword[1], read_doubleword[0]};
    end else $error("Memory file can't be opened.");
  endtask

endclass
