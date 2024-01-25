import len5_pkg::*;
import memory_pkg::*;
import fetch_pkg::*;
import csr_pkg::csr_priv_t;
import expipe_pkg::ldst_width_t;

module datapath #(
    parameter FETCH_MEMIF_FIFO_DEPTH = 2,
    parameter BOOT_PC = '0
) (
    // Clock and reset
    input logic clk_i,
    input logic rst_n_i,

    output logic mem_flush_o,

    // Instruction memory interface
    output logic                            instr_req_o,            // old: ins_mem_valid_o
    input  logic                            instr_gnt_i,            // old: ins_mem_ready_i
    input  logic                            instr_rvalid_i,         // old: ins_mem_valid_i
    output logic                            instr_rready_o,         // old: ins_mem_ready_o
    output logic                            instr_we_o,
    input  logic         [BUFF_IDX_LEN-1:0] instr_tag_i,            // old: ins_mem_req_o.tag
    input  logic         [        XLEN-1:0] instr_rdata_i,          // old: ins_mem_ans_i.value
    output logic         [        XLEN-1:0] instr_addr_o,           // old: ins_mem_req_o.addr
    output logic         [BUFF_IDX_LEN-1:0] instr_tag_o,            // old: ins_mem_req_o.tag
    // manca instr_be_o perchè è sempre LWORD
    input  logic                            instr_except_raised_i,
    input  except_code_t                    instr_except_code_i,

    // ----------------------
    // Data memory interface
    // ----------------------
    // Load interface
    output logic                            data_load_req_o,             // old: data_mem_valid_o
    input  logic                            data_load_gnt_i,             // old: data_mem_ready_i
    input  logic                            data_load_rvalid_i,          // old: data_mem_valid_i
    output logic                            data_load_rready_o,          // old: data_mem_ready_o
    output logic                            data_load_we_o,
    output logic         [        XLEN-1:0] data_load_addr_o,            // old: data_mem_req_o.addr
    output logic         [             3:0] data_load_be_o,              // old: data_mem_req_o.ls_type
    output logic         [BUFF_IDX_LEN-1:0] data_load_tag_o,             // old: data_mem_req_o.tag  
    input  logic         [        XLEN-1:0] data_load_rdata_i,           // old: data_mem_ans_i.value
    input  logic         [BUFF_IDX_LEN-1:0] data_load_tag_i,             // old: data_mem_ans_i.tag
    input  logic                            data_load_except_raised_i,
    input  except_code_t                    data_load_except_code_i,
    // Store interface
    output logic                            data_store_req_o,            // old: data_mem_valid_o
    input  logic                            data_store_gnt_i,            // old: data_mem_ready_i
    input  logic                            data_store_rvalid_i,         // old: data_mem_valid_i
    output logic                            data_store_rready_o,         // old: data_mem_ready_o
    output logic                            data_store_we_o,
    output logic         [        XLEN-1:0] data_store_addr_o,           // old: data_mem_req_o.addr
    output logic         [             3:0] data_store_be_o,             // old: data_mem_req_o.ls_type
    output logic         [        XLEN-1:0] data_store_wdata_o,          // old: data_mem_req_o.value
    output logic         [BUFF_IDX_LEN-1:0] data_store_tag_o,            // old: data_mem_req_o.tagù
    input  logic         [BUFF_IDX_LEN-1:0] data_store_tag_i,            // old: data_mem_ans_i.tag
    input  logic                            data_store_except_raised_i,
    input  except_code_t                    data_store_except_code_i,

    // Interrupt inputs ---> Not implemented
    input  logic [31:0] irq_i,      // CLINT interrupts + CLINT extension interrupts
    output logic        irq_ack_o,  // 
    output logic [ 4:0] irq_id_o,

    // CPU Control Signals ---> Not implemented
    input  logic fetch_enable_i,
    output logic core_sleep_o
);

  // ----------------
  // INTERNAL SIGNALS
  // ----------------

  // Frontend <--> backend
  // ---------------------
  logic                    fe_be_valid;
  logic                    be_fe_ready;
  logic         [ILEN-1:0] fe_be_instr;
  prediction_t             fe_be_pred;
  logic                    fe_be_except_raised;
  except_code_t            fe_be_except_code;
  logic                    be_fe_mis_flush;
  logic                    be_fe_except_flush;
  logic                    be_fe_res_valid;
  resolution_t             be_fe_res;
  logic                    be_fe_except_raised;
  logic         [XLEN-1:0] be_fe_except_pc;
  logic                    fe_be_bu_ready;

  // ---------
  // FRONT-END
  // ---------
  fetch_stage #(
      .HLEN            (HLEN),
      .BTB_BITS        (BTB_BITS),
      .BOOT_PC         (BOOT_PC),
      .INIT_C2B        (INIT_C2B),
      .MEMIF_FIFO_DEPTH(FETCH_MEMIF_FIFO_DEPTH)
  ) u_fetch_stage (
      .clk_i                (clk_i),
      .rst_n_i              (rst_n_i),
      .flush_i              (be_fe_mis_flush),
      .flush_bpu_i          (be_fe_except_flush),
      .instr_mem_valid_i    (instr_mem_rvalid_i),
      .instr_mem_ready_i    (instr_mem_gnt_i),
      .instr_mem_ready_o    (instr_mem_rready_o),
      .instr_mem_valid_o    (instr_mem_req_o),
      .instr_mem_we_o       (instr_mem_we_o),
      .instr_rdata_i        (instr_rdata_i),
      .instr_addr_o         (instr_addr_o),
      .instr_tag_o          (instr_tag_o),
      .instr_except_raised_i(instr_except_raised_i),
      .instr_except_code    (instr_except_code_i),
      .issue_ready_i        (be_fe_ready),
      .issue_valid_o        (fe_be_valid),
      .issue_instr_o        (fe_be_instr),
      .issue_pred_o         (fe_be_pred),
      .issue_except_raised_o(fe_be_except_raised),
      .issue_except_code_o  (fe_be_except_code),
      .bu_res_valid_i       (be_fe_res_valid),
      .bu_res_i             (be_fe_res),
      .bu_ready_o           (fe_be_bu_ready),
      .comm_except_raised_i (be_fe_except_raised),
      .comm_except_pc_i     (be_fe_except_pc)
  );

  // --------
  // BACK-END
  // --------
  backend u_backend (
      .clk_i                (clk_i),
      .rst_n_i              (rst_n_i),
      .fetch_valid_i        (fe_be_valid),
      .fetch_ready_i        (fe_be_bu_ready),
      .fetch_ready_o        (be_fe_ready),
      .fetch_instr_i        (fe_be_instr),
      .fetch_pred_i         (fe_be_pred),
      .fetch_except_raised_i(fe_be_except_raised),
      .fetch_except_code_i  (fe_be_except_code),
      .fetch_mis_flush_o    (be_fe_mis_flush),
      .fetch_except_flush_o (be_fe_except_flush),
      .fetch_res_valid_o    (be_fe_res_valid),
      .fetch_res_o          (be_fe_res),
      .fetch_except_raised_o(be_fe_except_raised),
      .fetch_except_pc_o    (be_fe_except_pc),

      .mem_load_valid_o        (data_load_req_o),
      .mem_load_ready_i        (data_load_gnt_i),
      .mem_load_valid_i        (data_load_rvalid_i),
      .mem_load_ready_o        (data_load_rready_o),
      .mem_load_we_o            (data_load_we_o),
      .mem_load_addr_o         (data_load_addr_o),
      .mem_load_be_o           (data_load_be_o),
      .mem_load_tag_o          (data_load_tag_o),
      .mem_load_rdata_i        (data_load_rdata_i),
      .mem_load_tag_i          (data_load_tag_i),
      .mem_load_except_raised_i(data_load_except_raised_i),
      .mem_load_except_code_i  (data_load_except_code_i),

      .mem_store_valid_o        (data_store_req_o),
      .mem_store_ready_i        (data_store_gnt_i),
      .mem_store_valid_i        (data_store_rvalid_i),
      .mem_looad_ready_o        (data_store_rready_o),
      .mem_store_we_o           (data_store_we_o),
      .mem_store_addr_o         (data_store_addr_o),
      .mem_store_be_o           (data_store_be_o),
      .mem_store_wdata_o        (data_store_wdata_o),
      .mem_store_tag_o          (data_store_tag_o),
      .mem_store_tag_i          (data_store_tag_i),
      .mem_store_except_raised_i(data_store_except_raised_i),
      .mem_store_except_code_i  (data_store_except_code_i)
  );

  // -------------
  // MEMORY-SYSTEM
  // -------------
  // NOTE: in the bare-metal version, the load-store unit and the fetch stage are
  // directly connected to the memory.
  // -----------------
  // OUTPUT EVALUATION
  // -----------------
  // Memory misprediction flush
  assign mem_flush_o = be_fe_mis_flush;

endmodule
