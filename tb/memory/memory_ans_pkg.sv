package memory_ans_pkg;

  // Answer from the memory
  typedef struct packed {
    logic [len5_pkg::ILEN-1:0] read;           // instruction read
    logic                      except_raised;
    len5_pkg::except_code_t    except_code;
  } instr_mem_ans_t;

  typedef struct packed {
    logic [len5_pkg::BUFF_IDX_LEN-1:0] tag;            // instruction tag
    logic [len5_pkg::XLEN-1:0]         read;           // data read
    logic                              except_raised;
    len5_pkg::except_code_t            except_code;
  } dload_mem_ans_t;

  typedef struct packed {
    logic [len5_pkg::BUFF_IDX_LEN-1:0] tag;            // instruction tag
    logic                              except_raised;
    len5_pkg::except_code_t            except_code;
  } dstore_mem_ans_t;

endpackage
