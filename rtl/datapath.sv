module datapath #(
  parameter int unsigned FETCH_MEMIF_FIFO_DEPTH = 2,
  parameter longint unsigned BOOT_PC = '0
) (
  // Clock and reset
  input logic clk_i,
  input logic rst_ni,

  output logic mem_flush_o,

  // Instruction memory interface
  output logic                                        instr_req_o,
  input  logic                                        instr_gnt_i,
  input  logic                                        instr_rvalid_i,
  output logic                                        instr_rready_o,
  output logic                                        instr_we_o,
  output logic                   [len5_pkg::XLEN-1:0] instr_addr_o,
  input  logic                   [len5_pkg::ILEN-1:0] instr_rdata_i,
  // manca instr_be_o perchè è sempre LWORD
  input  logic                                        instr_except_raised_i,
  input  len5_pkg::except_code_t                      instr_except_code_i,

  // ----------------------
  // Data memory interface
  // ----------------------
  // Load interface
  output logic                                                data_load_req_o,
  input  logic                                                data_load_gnt_i,
  input  logic                                                data_load_rvalid_i,
  output logic                                                data_load_rready_o,
  output logic                                                data_load_we_o,
  output logic                   [        len5_pkg::XLEN-1:0] data_load_addr_o,
  output logic                   [len5_pkg::BUFF_IDX_LEN-1:0] data_load_tag_o,
  output logic                   [                       7:0] data_load_be_o,
  input  logic                   [        len5_pkg::XLEN-1:0] data_load_rdata_i,
  input  logic                   [len5_pkg::BUFF_IDX_LEN-1:0] data_load_tag_i,
  input  logic                                                data_load_except_raised_i,
  input  len5_pkg::except_code_t                              data_load_except_code_i,
  // Store interface
  output logic                                                data_store_req_o,
  input  logic                                                data_store_gnt_i,
  input  logic                                                data_store_rvalid_i,
  output logic                                                data_store_rready_o,
  output logic                                                data_store_we_o,
  output logic                   [        len5_pkg::XLEN-1:0] data_store_addr_o,
  output logic                   [len5_pkg::BUFF_IDX_LEN-1:0] data_store_tag_o,
  output logic                   [                       7:0] data_store_be_o,
  output logic                   [        len5_pkg::XLEN-1:0] data_store_wdata_o,
  input  logic                   [len5_pkg::BUFF_IDX_LEN-1:0] data_store_tag_i,
  input  logic                                                data_store_except_raised_i,
  input  len5_pkg::except_code_t                              data_store_except_code_i,

  // Interrupt inputs ---> TODO: implement
  input  logic [31:0] irq_i,      // CLINT interrupts + CLINT extension interrupts
  output logic        irq_ack_o,  //
  output logic [ 4:0] irq_id_o,

  // CPU Control Signals ---> TODO: implement
  input  logic fetch_enable_i,
  output logic core_sleep_o
);

  import len5_pkg::*;
  import memory_pkg::*;
  import fetch_pkg::*;
  import csr_pkg::csr_priv_t;

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
  logic                    be_fe_bpu_valid;
  logic                    be_fe_pcgen_valid;
  resolution_t             be_fe_res;
  logic                    be_fe_except_raised;
  logic         [XLEN-1:0] be_fe_except_pc;
  logic                    fe_be_bu_pcgen_ready;
  logic                    early_jump_mem_flush;

  // ---------
  // FRONT-END
  // ---------
  fetch_stage #(
    .HLEN            (HLEN),
    .BTB_BITS        (BTB_BITS),
    .BOOT_PC         (BOOT_PC),
    .MEMIF_FIFO_DEPTH(FETCH_MEMIF_FIFO_DEPTH)
  ) u_fetch_stage (
    .clk_i                (clk_i),
    .rst_ni               (rst_ni),
    .flush_i              (be_fe_mis_flush),
    .flush_bpu_i          (be_fe_except_flush),
    .instr_valid_i        (instr_rvalid_i),
    .instr_ready_i        (instr_gnt_i),
    .instr_ready_o        (instr_rready_o),
    .instr_valid_o        (instr_req_o),
    .instr_we_o           (instr_we_o),
    .instr_rdata_i        (instr_rdata_i),
    .instr_addr_o         (instr_addr_o),
    .early_jump_mem_flush_o(early_jump_mem_flush),
    .instr_except_raised_i(instr_except_raised_i),
    .instr_except_code_i  (instr_except_code_i),
    .issue_ready_i        (be_fe_ready),
    .issue_valid_o        (fe_be_valid),
    .issue_instr_o        (fe_be_instr),
    .issue_pred_o         (fe_be_pred),
    .issue_except_raised_o(fe_be_except_raised),
    .issue_except_code_o  (fe_be_except_code),
    .bu_pcgen_ready_o     (fe_be_bu_pcgen_ready),
    .bu_bpu_valid_i       (be_fe_bpu_valid),
    .bu_pcgen_valid_i     (be_fe_pcgen_valid),
    .bu_res_i             (be_fe_res),
    .comm_except_raised_i (be_fe_except_raised),
    .comm_except_pc_i     (be_fe_except_pc)
  );

  // --------
  // BACK-END
  // --------
  backend u_backend (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .fetch_valid_i        (fe_be_valid),
    .fetch_ready_o        (be_fe_ready),
    .fetch_instr_i        (fe_be_instr),
    .fetch_pred_i         (fe_be_pred),
    .fetch_except_raised_i(fe_be_except_raised),
    .fetch_except_code_i  (fe_be_except_code),
    .fetch_pcgen_ready_i  (fe_be_bu_pcgen_ready),
    .fetch_bpu_valid_o    (be_fe_bpu_valid),
    .fetch_pcgen_valid_o  (be_fe_pcgen_valid),
    .fetch_mis_flush_o    (be_fe_mis_flush),
    .fetch_except_flush_o (be_fe_except_flush),
    .fetch_res_o          (be_fe_res),
    .fetch_except_raised_o(be_fe_except_raised),
    .fetch_except_pc_o    (be_fe_except_pc),

    .mem_load_valid_o        (data_load_req_o),
    .mem_load_ready_i        (data_load_gnt_i),
    .mem_load_valid_i        (data_load_rvalid_i),
    .mem_load_ready_o        (data_load_rready_o),
    .mem_load_we_o           (data_load_we_o),
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
    .mem_store_ready_o        (data_store_rready_o),
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
  assign mem_flush_o = be_fe_mis_flush | early_jump_mem_flush;

endmodule
