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
// File: memory_pkg.sv
// Author: Matteo Perotti
// Date: 23/08/2019

`include "util.svh"

package memory_pkg;
    import len5_pkg::*;
    import csr_pkg::csr_priv_t;
    import expipe_pkg::ldst_width_t;

    // Byte widths
    localparam int unsigned BYTE = 1;
    localparam int unsigned KiB = 1024;
    localparam int unsigned MiB = 1024*KiB;
    localparam int unsigned GiB = 1024*MiB;
    localparam int unsigned TiB = 1024*GiB;

    // TO BE DEFINED IN ANOTHER PLACE
    localparam int unsigned ASID_LEN = 8;
    typedef logic [ASID_LEN-1:0] asid_t;

    // ------------\\
    // RISC-V spec \\
    // ------------\\

    localparam int unsigned VADDR_LEN       = 39; // 512 GiB of virtual address space
    localparam int unsigned PADDR_LEN       = 56; // 2^16 TiB of physical address space
    localparam int unsigned PAGE_OFFSET_LEN = 12; // 4 KiB of page size
    localparam int unsigned VPN_PART_LEN    =  9; // 512 entries for each page table level
    localparam int unsigned PT_LEVELS       =  3; // page table indirection levels

    localparam int unsigned VPN_LEN         = VADDR_LEN - PAGE_OFFSET_LEN; // 27 bits  virtual page address
    localparam int unsigned PPN_LEN         = PADDR_LEN - PAGE_OFFSET_LEN; // 44 bits physical page address

    typedef logic [PT_LEVELS-1:0][VPN_PART_LEN-1:0] vpn_t; // 27 bit virtual page number
    typedef struct packed {
        logic [25:0] p2;    // To address the Gibipage
        logic [8:0]  p1;    // With ppn2, to address a Mebipage
        logic [8:0]  p0;    // With ppn2 and ppn1, to address a Kibipage
    } ppn_t; // 44 bit physical page number

    typedef struct packed {
        logic [XLEN-1:VADDR_LEN]    not_used;
        vpn_t                       vpn;
        logic [PAGE_OFFSET_LEN-1:0] page_offset;
    } virtual_addr_t;

    typedef enum logic [1:0] {
        KibiPage,
        MebiPage,
        GibiPage
    } page_type_e;

    typedef enum logic [1:0] {
        NoException,
        PageFault,
        AccessException
    } exception_e;

    // Memory access type
    typedef enum logic [1:0] {
        MEM_ACC_INSTR,  // instruction fetch
        MEM_ACC_LD,     // load
        MEM_ACC_ST      // store
    } mem_acc_t;

    // ------------------------
    // BARE-METAL MEMORY SYSTEM
    // ------------------------

    // Request to the memory
    typedef struct packed {
        logic [BUFF_IDX_LEN-1:0]    tag;    // instruction tag
        mem_acc_t                   acc_type;
        ldst_width_t                ls_type;
        logic [XLEN-1:0]            addr;   // physical address
        logic [XLEN-1:0]            value;
    } mem_req_t;

    // Answer from the memory
    typedef struct packed {
        logic [BUFF_IDX_LEN-1:0]    tag;    // instruction tag
        mem_acc_t                   acc_type;
        logic [XLEN-1:0]            addr;
        logic [XLEN-1:0]            value;  // fetched value
        logic                       except_raised;
        except_code_t               except_code;
    } mem_ans_t;

    //--------\\
    // CACHEs \\
    //--------\\

    //------------\\
    // L1 I-CACHE \\
    //------------\\

    localparam int unsigned ICACHE_L1_SIZE           = 16*KiB;
    localparam int unsigned ICACHE_L1_ASSOCIATIVITY  = 4;
    localparam int unsigned ICACHE_L1_LINE_SIZE      = 64*BYTE;
    localparam int unsigned ICACHE_L1_WORD_SIZE      = 4*BYTE;

    localparam int unsigned ICACHE_L1_LINE_LEN       = 8*ICACHE_L1_LINE_SIZE; // 512 bit/line
    localparam int unsigned ICACHE_L1_WORD_LEN       = 8*ICACHE_L1_WORD_SIZE; //  32 bit/word

    localparam int unsigned ICACHE_L1_WORD_A_LEN     = $clog2(ICACHE_L1_WORD_SIZE); // 2 bit to address a byte in the word 2;//
    localparam int unsigned ICACHE_L1_LINE_OFF_A_LEN = $clog2(ICACHE_L1_LINE_SIZE / ICACHE_L1_WORD_SIZE); // 4 bit to address a word in the line4;//
    localparam int unsigned ICACHE_L1_IDX_A_LEN      = $clog2(ICACHE_L1_SIZE / (ICACHE_L1_ASSOCIATIVITY * ICACHE_L1_LINE_SIZE)); // 6 bit to address a single set6;//
    localparam int unsigned ICACHE_L1_TAG_A_LEN      = XLEN - (ICACHE_L1_IDX_A_LEN + ICACHE_L1_LINE_OFF_A_LEN + ICACHE_L1_WORD_A_LEN);

    localparam int unsigned ICACHE_L1_BE_LEN     = ((ICACHE_L1_TAG_A_LEN+1)+7)/8;

    typedef logic [ICACHE_L1_IDX_A_LEN-1:0]  icache_idx_addr_t;
    typedef logic [ICACHE_L1_TAG_A_LEN-1:0]  icache_L1_tag_t;
    typedef logic [ICACHE_L1_LINE_LEN-1:0]   icache_line_t;

    typedef struct packed {
        logic [ICACHE_L1_TAG_A_LEN-1:0]      tag;
        logic [ICACHE_L1_IDX_A_LEN-1:0]      idx;
        logic [ICACHE_L1_LINE_OFF_A_LEN-1:0] line_off;
        logic [ICACHE_L1_WORD_A_LEN-1:0]     word_off;
    } icache_L1_addr_t;

    typedef struct packed {
        logic [ICACHE_L1_TAG_A_LEN-1:0]      tag;
        logic [ICACHE_L1_IDX_A_LEN-1:0]      idx;
    } icache_line_addr_t;

    typedef struct packed {
        logic [XLEN-1:0] vaddr;
        logic            valid;
    } frontend_icache_req_t;

    typedef struct packed {
        icache_line_t    line;
        logic [XLEN-1:0] vaddr;
        exception_e      exception;
        logic            valid;
    } icache_frontend_ans_t;

    typedef struct packed {
        virtual_addr_t vaddr;
        logic          valid;
    } icache_tlb_req_t;

    typedef struct packed {
        icache_L1_addr_t paddr;
        logic            hit;
        exception_e      exception;
        logic            valid;
    } tlb_icache_ans_t;

    typedef struct packed {
        icache_line_addr_t line_addr;
        logic              valid;
    } icache_l2_req_t;

    typedef struct packed {
        icache_line_t line;
        logic         valid;
    } l2_icache_ans_t;

    typedef struct packed {
        icache_L1_tag_t tag;
        logic           valid;
    } icache_L1_vtag_t;

    typedef struct packed {
        icache_line_t   [ICACHE_L1_ASSOCIATIVITY-1:0] data_vec;
        icache_L1_tag_t [ICACHE_L1_ASSOCIATIVITY-1:0] tag_vec;
        logic           [ICACHE_L1_ASSOCIATIVITY-1:0] valid_vec;
    } icache_mem_out_t;

    typedef enum logic [1:0] {
        FlushCnt,
        VaddrD,
        VaddrQ
    } icache_addr_src_e;

    typedef enum logic [1:0] {
        Idle,            // Do nothing
        ReadSet,         // Read an whole set
        WriteLineAndTag, // Write line and tag
        InvalidSet       // Invalid the entire set (used during a flush operation)
    } icache_ctrl_e;

    typedef struct packed {
        logic                           cs;
        logic                           we;
        logic [ICACHE_L1_LINE_SIZE-1:0] be;
    } icache_dmem_ctrl_t;

    typedef struct packed {
        logic                        cs;
        logic                        we;
        logic [ICACHE_L1_BE_LEN-1:0] be;
    } icache_tvmem_ctrl_t;

    typedef struct packed {
        icache_dmem_ctrl_t  [ICACHE_L1_ASSOCIATIVITY-1:0] dmem_vec;
        icache_tvmem_ctrl_t [ICACHE_L1_ASSOCIATIVITY-1:0] tvmem_vec;
    } icache_mem_ctrl_t;

    typedef logic [ICACHE_L1_ASSOCIATIVITY-1:0] icache_replace_vec_t;
    typedef logic [ICACHE_L1_ASSOCIATIVITY-1:0] icache_valid_vec_t;
    typedef logic [ICACHE_L1_ASSOCIATIVITY-1:0] icache_hit_vec_t;

    //--------------\\
    // L1 WB BUFFER \\
    //--------------\\

    localparam int unsigned DCACHE_L1_STAGES = 2;
    localparam int unsigned CACHE_L2_STAGES = 6; // random number, for now

    // 2^WBB_TAG_LEN must be greater than the number of stages in the route WBB -> L2 -> WBB
    localparam int unsigned DL1_DL2_STAGES = DCACHE_L1_STAGES + CACHE_L2_STAGES;
    localparam int unsigned WBB_TAG_LEN    = $clog2(DL1_DL2_STAGES); // Conservative number of stages, can be optimized3;//

    // Input tag for the WBB
    typedef logic [WBB_TAG_LEN-1:0] wbb_tag_t;

    //------------\\
    // L1 D-CACHE \\
    //------------\\

    localparam int unsigned DCACHE_L1_SIZE              = 32*KiB;
    localparam int unsigned DCACHE_L1_ASSOCIATIVITY     = 2;
    localparam int unsigned DCACHE_L1_LINE_SIZE         = 64*BYTE;
    localparam int unsigned DCACHE_L1_WORD_SIZE         = 8*BYTE;

    localparam int unsigned DCACHE_L1_LINE_LEN          = 8*DCACHE_L1_LINE_SIZE;
    localparam int unsigned DCACHE_L1_WORD_LEN          = 8*DCACHE_L1_WORD_SIZE;

    localparam int unsigned DCACHE_L1_WORD_A_LEN        = $clog2(DCACHE_L1_WORD_SIZE);//8;//
    localparam int unsigned DCACHE_L1_LINE_OFF_A_LEN    = $clog2(DCACHE_L1_LINE_SIZE / DCACHE_L1_WORD_SIZE);//3;//
    localparam int unsigned DCACHE_L1_IDX_A_LEN         = $clog2(DCACHE_L1_SIZE / (DCACHE_L1_ASSOCIATIVITY * DCACHE_L1_LINE_SIZE));//3;//
    localparam int unsigned DCACHE_L1_TAG_A_LEN         = XLEN - (DCACHE_L1_IDX_A_LEN + DCACHE_L1_LINE_OFF_A_LEN + DCACHE_L1_WORD_A_LEN);

    localparam int unsigned DCACHE_L1_LINE_A_LEN        = DCACHE_L1_TAG_A_LEN + DCACHE_L1_IDX_A_LEN;
    localparam int unsigned DCACHE_L1_TVD_LEN           = DCACHE_L1_TAG_A_LEN + 2; // Tag + Valid + Dirty (TVD)

    localparam int unsigned DCACHE_L1_WBB_ENTRIES       = 4;
    localparam int unsigned DCACHE_L1_MSHR_ENTRIES      = 4;
    localparam int unsigned LOG2_DCACHE_L1_WBB_ENTRIES  = $clog2(DCACHE_L1_WBB_ENTRIES);//2;//
    localparam int unsigned LOG2_DCACHE_L1_MSHR_ENTRIES = $clog2(DCACHE_L1_MSHR_ENTRIES);//2;//

    typedef logic [DCACHE_L1_LINE_LEN-1:0]          dcache_line_t;
    typedef logic [DCACHE_L1_LINE_LEN-1:0]          dcache_data_t;
    typedef logic [DCACHE_L1_IDX_A_LEN-1:0]         dcache_addr_t;
    typedef logic [DCACHE_L1_TAG_A_LEN-1:0]         dcache_tag_t;
    typedef logic [DCACHE_L1_ASSOCIATIVITY-1:0]     hit_vec_t;
    typedef logic [DCACHE_L1_ASSOCIATIVITY-1:0]     valid_vec_t;
    typedef logic [DCACHE_L1_ASSOCIATIVITY-1:0]     dirty_vec_t;
    typedef logic [DCACHE_L1_ASSOCIATIVITY-1:0]     repl_vec_t;
    typedef logic [LOG2_DCACHE_L1_MSHR_ENTRIES-1:0] l1dc_mshr_addr_t;
    typedef logic [LOG2_DCACHE_L1_WBB_ENTRIES-1:0]  l1dc_wbb_addr_t;

    typedef struct packed {
        logic [DCACHE_L1_TAG_A_LEN-1:0]      tag;
        logic [DCACHE_L1_IDX_A_LEN-1:0]      idx;
        logic [DCACHE_L1_LINE_OFF_A_LEN-1:0] line_off;
        logic [DCACHE_L1_WORD_A_LEN-1:0]     word_off;
    } dcache_L1_addr_t;

    typedef struct packed {
        logic [DCACHE_L1_TAG_A_LEN-1:0] tag;
        logic [DCACHE_L1_IDX_A_LEN-1:0] idx;
    } line_addr_t;

    // LSQ -> L1 D-Cache
        localparam int unsigned LSBUFF_LEN = ($clog2(LDBUFF_DEPTH) > $clog2(STBUFF_DEPTH)) ? $clog2(LDBUFF_DEPTH) : $clog2(STBUFF_DEPTH);
    typedef logic [LSBUFF_LEN-1:0] lsq_addr_t;
    typedef enum logic {
        Load,
        Store
    } lsq_d0_req_type_e;

    typedef enum logic [1:0] {
        B,
        HW,
        W,
        DW
    } store_width_e;

    typedef struct packed {
        dcache_L1_addr_t  paddr;       // the physical cache address
        logic [XLEN-1:0]  data;        // data to be stored
        lsq_d0_req_type_e req_type;    // Load or Store
        store_width_e     store_width; // B, HW, W, DW (for Store!)
        lsq_addr_t        lsq_addr;    // to address the answer to LSQ
        logic             valid;       // request valid
    } lsq_l1dc_req_t;

    // L1 D-Cache -> LSQ
    typedef struct packed {
        logic [XLEN-1:0] data;      // loaded data
        logic            was_store; // '1' if the answer is relative to a store
        lsq_addr_t       lsq_addr;  // to address the answer
        logic            valid;     // valid answer
    } l1dc_lsq_ans_t;

    // L1 D-Cache -> LSQ (wake-up)
    typedef struct packed {
        line_addr_t      line_addr; // the address of the line which has just returned into the cache
        logic            valid;     // valid wake up signal
    } l1dc_lsq_wup_t;

    // L1 D-Cache -> L2 Cache
    typedef struct packed {
        line_addr_t      line_addr; // line address for the request and to address the ans
        dcache_line_t    line;      // line to be stored
        wbb_tag_t        wbb_tag;   // WBB tag mark
        logic            is_store;  // if '0': load, if '1': store
        logic            valid;
    } l1dc_l2c_req_t;

    // L2 Cache -> L1 D-Cache
    typedef enum logic [1:0] {
        ReplaceLine,
        WWBWakeUp,
        StoreHit
    } l2c_d0_ans_type_e;

    typedef struct packed {
        line_addr_t       line_addr; // to address the answer
        dcache_line_t     line;      // line to be replaced
        wbb_tag_t         wbb_tag;   // tag for wbb comparison
        l2c_d0_ans_type_e ans_type;  // if '0': relative to load, if '1': relative to storeì
        logic             valid;
    } l2c_l1dc_ans_t;

    typedef struct packed {
        logic [DCACHE_L1_IDX_A_LEN-1:0] idx;
        logic                           valid;
    } upd_l1dc_req_t;

    typedef struct packed {
        logic [DCACHE_L1_IDX_A_LEN-1:0] dcache_addr;
        logic                           valid;
    } rst_l1dc_req_t;

    // d0 -> d1
    typedef enum logic [2:0] {
        d0_d1_Idle,        // nothing to be done
        d0_d1_Load,        // check hit, wb buf, mshr
        d0_d1_Store,       // check hit, wb buf, mshr, write d0
        d0_d1_L2WBBWakeUp, // wb buf wake-up
        d0_d1_L2StHit,     // wb buf acknowledge
        d0_d1_ReplaceReq,  // check dirty, wb buf full, write d0
        d0_d1_UpdateL2     // give dirty vector to d0, check wb buf, write d0
    } d0_d1_req_type_e;

    // d0 data sel block -> output registers

    typedef struct packed {
        d0_d1_req_type_e req_type;    // request type
        dcache_L1_addr_t paddr;       // the physical cache address
        logic [XLEN-1:0] data;        // doubleword to be stored
        dcache_line_t    line;
        store_width_e    store_width; // B, HW, W, DW (for Store!)
        wbb_tag_t        wbb_tag;     // tag for L2 -> WBB answers
        lsq_addr_t       lsq_addr;    // to address the answer to LSQ
        logic            valid;       // request valid
    } d1_req_info_t;

    typedef struct packed {
        dcache_tag_t  [DCACHE_L1_ASSOCIATIVITY-1:0] tag_vec;
        logic         [DCACHE_L1_ASSOCIATIVITY-1:0] valid_vec;
        logic         [DCACHE_L1_ASSOCIATIVITY-1:0] dirty_vec;
        dcache_data_t [DCACHE_L1_ASSOCIATIVITY-1:0] data_vec;
    } d1_mem_out_t;

    typedef struct packed {
        d1_req_info_t info;
        d1_mem_out_t  mem_out;
    } d0_d1_req_t;

    // d1 -> d0
    typedef enum logic [2:0] {
        LoadReplay,       // load replay
        StoreReplay,      // store replay
        WriteCleanLine,   // instant line write (dirty = 1'b0)
        WriteDirtyLine,   // instant line write (dirty = 1'b1)
        WriteStore,       // instant store write (DW, W, HW, B)
        CleanDirty,       // clean the dirty bit
        WaitL2UpdatingCnt // wait for the L2 upd counter to be updated
    } d1_d0_req_type_e;

    typedef struct packed {
        d1_d0_req_type_e req_type;    // d1 -> d0 request type
        dcache_L1_addr_t paddr;       // the physical cache address
        logic [XLEN-1:0] data;        // data to be stored
        dcache_line_t    line;        // forwarded line
        store_width_e    store_width; // B, HW, W, DW (for Store!)
        lsq_addr_t       lsq_addr;    // to address the answer to LSQ
        hit_vec_t        hit_vec;     // hit lines from the comparison block in d1
        dirty_vec_t      dirty_vec;   // one hotted dirty vector from d1
        repl_vec_t       replace_vec; // updateL2 replace idx
        logic            valid;       // request valid
    } d1_d0_req_t;

    typedef struct packed {
        logic                                 cs;
        logic                                 we;
        logic [((DCACHE_L1_TVD_LEN)+7)/8-1:0] be; // TAG + VALID + DIRTY
    } tmem_ctrl_t;

    typedef struct packed {
        logic                                  cs;
        logic                                  we;
        logic [((DCACHE_L1_LINE_LEN)+7)/8-1:0] be; // Data line byte enable
    } dmem_ctrl_t;

    typedef struct packed {
        tmem_ctrl_t [DCACHE_L1_ASSOCIATIVITY-1:0] tvd_ctrl_vec;
        dmem_ctrl_t [DCACHE_L1_ASSOCIATIVITY-1:0] data_ctrl_vec;
    } dcache_ctrl_t;

    // Blocks which interact with the L1 D-Cache. Only one of them can be selected by the scheduler.
    typedef enum logic [2:0] {
        Nobody,
        LSQ,
        UpdateL2,
        L2Cache,
        D1,
        RstBlock
    } d0_winner_e;

    // Possible action performed by d0 on the cache
    typedef enum logic [3:0] {
        d0_Idle,              // nothing to be done: no fulfillable requests
        d0_ReadLsq,           // cache read (source: LSQ)
        d0_ReadD1,            // cache read (source: d1)
        d0_WriteCleanLineD1,  // cache clean line write (source: d1)
        d0_WriteDirtyLineD1,  // cache dirty line write (source: d1)
        d0_WriteStoreD1,      // cache store write (source: d1)
        d0_ReadL2,            // cache read (source: L2)
        d0_FwdL2StAddr,       // fwd store addr (source: L2)
        d0_ReadUpdate,        // cache read (source: update-L2 block)
        d0_CleanDirty,        // clean the dirty bit (source: d1)
        d0_ResetLines         // invalid the set (source: rst_block)
    } d0_req_type_e;

    typedef struct packed {
        dcache_tag_t tag;
        logic        valid;
        logic        dirty;
    } tvd_mem_line_t;

    typedef struct packed {
        logic                                 cs;
        logic                                 we;
        logic [(DCACHE_L1_LINE_SIZE+7)/8-1:0] be;
    } data_mem_ctrl_t;

    typedef struct packed {
        dcache_addr_t dcache_addr;
        logic         valid;
    } l1dc_rst_req_t;

    // MSHR - WB BUFFER scheduler
    typedef enum logic {
        MSHR,
        WBB
    } mshr_wbb_winner_e;

    typedef struct packed {
        d1_d0_req_type_e req_type;
        dcache_L1_addr_t paddr;
        logic [XLEN-1:0] doubleword;
        lsq_addr_t       lsq_addr;
        store_width_e    store_width;
    } l1dc_replay_t;

    //---------\\
    // L1 MSHR \\
    //---------\\

    localparam int unsigned L1C_MSHR_ENTRIES = 4;

    localparam int unsigned LOG2_L1C_MSHR_ENTRIES     = $clog2(L1C_MSHR_ENTRIES);//2;//
    localparam int unsigned LOG2_L1C_MSHR_PENDING_REQ = $clog2(L1C_MSHR_ENTRIES + 1); // For a 4 entries mshr: 0, 1, 2, 3, 4//2;//


    typedef logic [LOG2_L1C_MSHR_ENTRIES-1:0]     mshr_addr_t;
    typedef logic [LOG2_L1C_MSHR_PENDING_REQ-1:0] mshr_pending_req_t;

    //---------------------\\
    // L1 WB VICTIM BUFFER \\
    //---------------------\\

    localparam int unsigned L1C_WBB_ENTRIES = 4;

    localparam int unsigned LOG2_L1C_WBB_ENTRIES      = $clog2(L1C_WBB_ENTRIES);//2;//
    localparam int unsigned LOG2_L1C_WBB_FREE_ENTRIES = $clog2(L1C_WBB_ENTRIES + 1); // For a 4 entries buf: 0, 1, 2, 3, 42;//

    typedef logic [LOG2_L1C_WBB_ENTRIES-1:0]      wbb_addr_t;
    typedef logic [LOG2_L1C_WBB_FREE_ENTRIES-1:0] wbb_free_entries_t;

    //---------\\
    // L2  MSHR \\
    //---------\\

    localparam int unsigned L2C_MSHR_ENTRIES = 4;

    localparam int unsigned LOG2_L2C_MSHR_ENTRIES = $clog2(L2C_MSHR_ENTRIES);//2;//

    typedef logic [LOG2_L2C_MSHR_ENTRIES-1:0] l2c_mshr_addr_t;

    //---------------------\\
    // L2 WB VICTIM BUFFER \\
    //---------------------\\

    localparam int unsigned L2C_WBB_ENTRIES = 4;

    localparam int unsigned LOG2_L2C_WBB_ENTRIES = $clog2(L2C_WBB_ENTRIES);//2;//

    typedef logic [LOG2_L2C_WBB_ENTRIES-1:0] l2c_wbb_addr_t;

    //------------------\\
    // L2 CACHE (draft) \\
    //------------------\\

    localparam int unsigned CACHE_L2_SIZE           = 1*MiB;
    localparam int unsigned CACHE_L2_ASSOCIATIVITY  = 16;
    localparam int unsigned CACHE_L2_LINE_SIZE      = 64*BYTE;
    localparam int unsigned CACHE_L2_WORD_SIZE      = 8*BYTE;

    localparam int unsigned CACHE_L2_LINE_LEN       = 8*CACHE_L2_LINE_SIZE;
    localparam int unsigned CACHE_L2_WORD_LEN       = 8*CACHE_L2_WORD_SIZE;

    localparam int unsigned CACHE_L2_WORD_A_LEN     = $clog2(CACHE_L2_WORD_SIZE); // 3
    localparam int unsigned CACHE_L2_LINE_OFF_A_LEN = $clog2(CACHE_L2_LINE_SIZE / CACHE_L2_WORD_SIZE); // 3
    localparam int unsigned CACHE_L2_IDX_A_LEN      = $clog2(CACHE_L2_SIZE / (CACHE_L2_ASSOCIATIVITY * CACHE_L2_LINE_SIZE)); // 10
    localparam int unsigned CACHE_L2_TAG_A_LEN      = XLEN - (CACHE_L2_IDX_A_LEN + CACHE_L2_LINE_OFF_A_LEN + CACHE_L2_WORD_A_LEN);

    typedef logic [CACHE_L2_LINE_LEN-1:0]      l2c_line_t;
    typedef logic [CACHE_L2_IDX_A_LEN-1:0]     l2c_addr_t;
    typedef logic [CACHE_L2_IDX_A_LEN-1:0]     l2c_line_addr_t;
    typedef logic [CACHE_L2_ASSOCIATIVITY-1:0] l2c_hit_vec_t;
    typedef logic [CACHE_L2_ASSOCIATIVITY-1:0] l2c_dirty_vec_t;
    typedef logic [CACHE_L2_ASSOCIATIVITY-1:0] l2c_repl_vec_t;
    typedef logic [CACHE_L2_TAG_A_LEN-1:0]     l2c_tag_t;
    typedef logic [CACHE_L2_LINE_LEN-1:0]      l2c_data_t;

    // The line size should be equal for i-Cache, d-Cache, L2-Cache
    typedef struct packed {
        logic [CACHE_L2_TAG_A_LEN-1:0]      tag;
        logic [CACHE_L2_IDX_A_LEN-1:0]      idx;
        logic [CACHE_L2_LINE_OFF_A_LEN-1:0] line_off;
        logic [CACHE_L2_WORD_A_LEN-1:0]     word_off;
    } cache_L2_addr_t;

    // L2-Arbiter -> L2 Cache
    typedef enum logic [1:0] {
        IReadLine,
        DReadLine,
        DWriteLine,
        PTWLoad
    } l2arb_s0_req_type_e;

    typedef struct packed {
        cache_L2_addr_t     paddr;    // the physical cache address
        l2c_line_t          line;     // line to be stored
        l2arb_s0_req_type_e req_type; // specify the request type
        wbb_tag_t           wbb_tag;  // to address the answer to LSQ
        logic               valid;    // request valid
    } l2arb_l2c_req_t;

    // L2 Cache -> L2-Arbiter
    typedef enum logic [2:0] {
        l2arb_s0_ILineRead,
        l2arb_s0_DLineRead,
        l2arb_s0_DWbbWakeUp,
        l2arb_s0_DLineWritten,
        l2arb_s0_PTWLoad
    } l2c_l2arb_ans_type_e;

    typedef struct packed {
        logic [XLEN-1:0]     data;      // loaded data
        l2c_line_t           line;      // l2c line ans
        cache_L2_addr_t      paddr;     // data to be stored
        l2c_l2arb_ans_type_e ans_type;  // specify the request type
        wbb_tag_t            wbb_tag;   // to address the answer
        logic                valid;     // valid answer
    } l2c_l2arb_ans_t;

    // L2 Cache -> DRAM
    typedef struct packed {
        cache_L2_addr_t  line_addr; // line address for the request and to address the ans
        l2c_line_t       line;      // line to be stored
        logic            is_write;  // if '0': read, if '1': write
        logic            valid;
    } l2c_dram_req_t;

    // DRAM -> L2 Cache
    typedef enum logic {
        Read,
        Write
    } dram_l2c_ans_type_e;

    typedef struct packed {
        l2c_line_t          line;     // read line
        dram_l2c_ans_type_e ans_type; // Answer to a read or to a write?
        logic               valid;
    } dram_l2c_ans_t;

    typedef struct packed {
        logic [CACHE_L2_IDX_A_LEN-1:0] idx;
        logic                          valid;
    } upd_l2c_req_t;

    typedef struct packed {
        logic [CACHE_L2_IDX_A_LEN-1:0] L2c_addr;
        logic                          valid;
    } rst_l2c_req_t;

    //---------\\
    //  TLBs   \\
    //---------\\

    localparam int unsigned PTE_SIZE = 8*BYTE;

    typedef enum logic [1:0] {
        NoFlush,
        FlushASID,
        FlushPage,
        FlushAll
    } tlb_flush_e;

    typedef struct packed {
        logic [9:0]  reserved;
        logic [43:0] ppn;
        logic [1:0]  rsw;
        logic        d;
        logic        a;
        logic        g;
        logic        u;
        logic        x;
        logic        w;
        logic        r;
        logic        v;
    } pte_t;

    //----------\\
    // L1 I-TLB \\
    //----------\\

    localparam int unsigned ITLB_TAG_LEN  = VPN_LEN;
    localparam int unsigned ITLB_DATA_LEN = PPN_LEN;

    localparam int unsigned I_TLB_ENTRIES = 10;

    typedef struct packed {
        logic [VPN_LEN-1:0] vpn;
        logic               valid;
    } itlb_l2tlb_req_t;

    typedef struct packed {
        ppn_t       ppn;
        page_type_e page_type;
        exception_e exception;
        logic       g_bit;
        logic       u_bit;
        logic       valid;
    } l2tlb_itlb_ans_t;

    typedef struct packed {
        ppn_t  ppn;    // i-TLB data
        vpn_t  vpn;    // i-TLB tag
        asid_t asid;   // ASID linked to the page entry
        logic  glob;   // Global page, if '1' the ASID field is neglected (it is valid for all the Address Spaces)
        logic  user;
        logic  gibi;   // GibiPage
        logic  mebi;   // MebiPage
        logic  valid;  // The entry is valid
    } itlb_entry_t;

    //----------\\
    // L1 D-TLB \\
    //----------\\

    localparam int unsigned D_TLB_ENTRIES = 8;

    typedef struct packed {
        logic [VPN_LEN-1:0] vpn;
        logic               is_store;
        lsq_addr_t          lsq_addr;
        logic               valid;
    } lsq_dtlb_req_t;

    typedef struct packed {
        logic [PPN_LEN-1:0] ppn;
        exception_e         exception;
        logic               was_store;
        lsq_addr_t          lsq_addr;
        logic               valid;
    } dtlb_lsq_ans_t;

    typedef struct packed {
        logic [VPN_LEN-1:0] vpn;
        logic               valid;
    } dtlb_lsq_wup_t;

    typedef struct packed {
        logic [VPN_LEN-1:0] vpn;
        logic               valid;
    } dtlb_l2tlb_req_t;

    typedef struct packed {
        logic [VPN_LEN-1:0] vpn;
        logic [PPN_LEN-1:0] ppn;
        page_type_e         page_type;
        logic               g_bit;
        logic               r_bit;
        logic               w_bit;
        logic               x_bit;
        logic               u_bit;
        logic               d_bit;
        exception_e         exception;
        logic               valid;
    } l2tlb_dtlb_ans_t;

    typedef struct packed {
        vpn_t  vpn;     // i-TLB tag
        ppn_t  ppn;     // i-TLB data
        asid_t asid;    // ASID linked to the
        logic  glob;    // Global page, if '1' the ASID field is neglected (it is valid for all the Address Spaces)
        logic  user;    // User page. To be checked with the actual privilege mode and the SUM bit
        logic  read;    // The page is readable
        logic  execute; // If this page is ONLY executable, it can be read iff the MXR bit is 1
        logic  write;   // Write permission bit
        logic  dirty;   // Page dirty: if a clean page is accessed by a store -> raise a page fault
        logic  gibi;    // GibiPage
        logic  mebi;    // MebiPage
        logic  valid;   // The entry is valid
    } dtlb_entry_t;

    typedef enum logic [1:0] {
        dtlb_NoReq,
        dtlb_LSQReq,
        dtlb_Flush,
        dtlb_L2Ans
    } dtlb_ctrl_e;

    // d-TLB MSHR

    localparam int unsigned DTLB_MSHR_ENTRIES = 2;

    typedef struct packed {
        vpn_t       vpn;
        logic       waiting;
        logic       valid;
    } dtlb_mshr_entry_t;

    //--------\\
    // L2 TLB \\
    //--------\\

    localparam int unsigned L2_TLB_ENTRIES        = 512;
    localparam int unsigned L2_TLB_ASSOCIATIVITY  = 4;
    localparam int unsigned L2_TLB_N_SETS         = L2_TLB_ENTRIES / L2_TLB_ASSOCIATIVITY;
    localparam int unsigned L2_TLB_IDX_LEN        = $clog2(L2_TLB_N_SETS);//9;//
    localparam int unsigned L2_TLB_TAG_LEN        = VPN_LEN - L2_TLB_IDX_LEN;
    localparam int unsigned L2_TLB_TAG_ENTRY_LEN  = L2_TLB_TAG_LEN + ASID_LEN + 9;
    localparam int unsigned L2_TLB_TMEM_ENTRY_LEN = ((L2_TLB_TAG_ENTRY_LEN)+7)/8;

    localparam int unsigned L2_TLB_MSHR_ENTRIES   = 4;

    typedef logic [L2_TLB_TAG_LEN-1:0] l2tlb_tag_t;

    typedef struct packed {
        ppn_t       ppn;
        l2tlb_tag_t tag;
        asid_t      asid;
        logic       glob;
        logic       read;
        logic       write;
        logic       execute;
        logic       dirty;
        logic       user;
        logic       mebi;
        logic       gibi;
        logic       valid;
    } l2tlb_entry_t;

    typedef struct packed {
        l2tlb_tag_t tag;
        asid_t      asid;
        logic       glob;
        logic       user;
        logic       read;
        logic       write;
        logic       execute;
        logic       dirty;
        logic       mebi;
        logic       gibi;
        logic       valid;
    } l2tlb_t_entry_t;

    typedef enum logic {
        ITLB,
        DTLB
    } tlb_arb_tag_e;

    typedef struct packed {
        vpn_t         vpn;
        tlb_arb_tag_e origin;
        logic         valid;
    } l1tlb_l2tlb_req_t;

    typedef struct packed {
        vpn_t         vpn;
        ppn_t         ppn;
        page_type_e   page_type;
        logic         w_bit;
        logic         r_bit;
        logic         x_bit;
        logic         d_bit;
        logic         g_bit;
        logic         u_bit;
        exception_e   exception;
        tlb_arb_tag_e destination;
        logic         valid;
    } l2tlb_l1tlb_ans_t;

    typedef struct packed {
        logic                       cs;
        logic                       we;
        logic [((PPN_LEN)+7)/8-1:0] be;
    } l2tlb_dmem_ctrl_t;

    typedef struct packed {
        logic                             cs;
        logic                             we;
        logic [L2_TLB_TMEM_ENTRY_LEN-1:0] be;
    } l2tlb_tmem_ctrl_t;

    typedef enum logic [2:0] {
        t0_t1_Idle,
        t0_t1_KibiRead,
        t0_t1_MebiRead,
        t0_t1_GibiRead,
        t0_t1_FlushASID,
        t0_t1_FlushPage,
        t0_t1_PTWAns
    } t0_t1_req_type_e;

    typedef struct packed {
        logic w;
        logic r;
        logic x;
    } wrx_t;

    typedef struct packed {
        vpn_t               vpn;
        logic [PPN_LEN-1:0] ppn;
        page_type_e         page_type;
        exception_e         exception;
        wrx_t               wrx_bits;
        logic               d_bit;
        logic               g_bit;
        logic               u_bit;
        tlb_arb_tag_e       destination;
        t0_t1_req_type_e    req_type;
    } t0_t1_req_t;

    typedef enum logic [1:0] {
        t1_t0_MebiRead,
        t1_t0_GibiRead,
        t1_t0_ReplaceLine,
        t1_t0_FlushMasked
    } t1_t0_req_type_e;

    typedef struct packed {
        vpn_t                            vpn;
        logic [PPN_LEN-1:0]              ppn;
        page_type_e                      page_type;
        wrx_t                            wrx_bits;
        logic                            d_bit;
        logic                            u_bit;
        logic                            g_bit;
        logic [L2_TLB_ASSOCIATIVITY-1:0] flush_vec;
        t1_t0_req_type_e                 req_type;
        tlb_arb_tag_e                    destination;
        logic                            valid;
    } t1_t0_req_t;

    //-----\\
    // PTW \\
    //-----\\

    localparam int unsigned MMUC_TAG_LEN = (PT_LEVELS-1)*VPN_PART_LEN; // 2*9 = 18 bits
    localparam int unsigned MMUC_ENTRIES = 10;

    typedef struct packed {
        vpn_t vpn;   // 9 bit vpn + 9 bit vpn + 9 bit vpn = 27 bit vpn
        logic valid;
    } l2tlb_ptw_req_t;

    typedef struct packed {
        logic [PPN_LEN-1:0] ppn;       // 44 bit physical page address
        page_type_e         page_type; // is the page a superpage?
        exception_e         exception; // encoded exception
        wrx_t               wrx_bits;  // Writable, Readable, eXecutable page bits
        logic               d_bit;     // dirty page bit
        logic               g_bit;     // global page bit
        logic               u_bit;     // user page bit
        logic               valid;
    } ptw_l2tlb_ans_t;

    typedef struct packed {
        logic [PT_LEVELS-2:0][VPN_PART_LEN-1:0] mmuc_tags; // the first two VPN parts (used as TAG for mmuc)
        logic                                   valid;
    } ptw_mmuc_req_t;

    typedef struct packed {
        logic [VPN_PART_LEN-1:0] mmuc_tag;   // 9 bit single VPN part
        logic [PPN_LEN-1:0]      mmuc_data;  // 44 bit single ppn
        logic                    wr_en;      // write enable
        logic                    which_side; // write the first or the second part of the trace
        logic                    wr_partial; // write the partial field
        logic                    partial;    // trace only partially valid
        logic                    try_update; // try to update the shift register for replacement
    } ptw_mmuc_write_t;

    typedef struct packed {
        logic [PPN_LEN-1:0] ppn;         // 44 bit single ppn
        logic               hit;
        logic               is_full_hit; // hit of both the two VPNs or only the first one?
    } mmuc_ptw_ans_t;

    typedef struct packed {
        logic [PADDR_LEN-1:0] pte_paddr;  // physical address of the page table entry
        logic                 valid;
    } ptw_l2c_req_t;

    typedef struct packed {
        logic [XLEN-1:0] pte;            // 64 bits page table entry
        logic            valid;
    } l2c_ptw_ans_t;

    typedef struct packed {
        csr_priv_t          priv;
        csr_priv_t          priv_ls; // privilege for load/store. It's priv filtered by MPRV bit
        logic               sum;
        logic               mxr;
    } csr_ptw_ctrl_t;

    typedef struct packed {
    //  logic [1:0] rsw; // used by software, the hardware can ignore it
    //  logic       d;   // dirty bit. In this implementation, it is not checked in the PTW
        logic       a;   //
    //  logic       g;   // global bit. In this implementation, it is not checked in the PTW
    //  logic       u;   // user bit. In this implementation, it is not checked in the PTW
        logic       x;   //
        logic       w;   //
        logic       r;   //
        logic       v;   //
    } pte_ctrl_t;

    typedef enum logic [1:0] {
        Root = 'b11,
        L3   = 'b10,
        L2   = 'b01,
        L1   = 'b00
    } pte_level_e;

    //-------------\\
    // L2C ARBITER \\
    //-------------\\

    typedef enum logic [1:0] {
        l2arb_ans_NoWhere,
        l2arb_ans_DCache,
        l2arb_ans_ICache,
        l2arb_ans_PTW
    } l2arb_ans_destination_e;

    typedef enum logic [1:0] {
        l2arb_req_NoWhere,
        l2arb_req_DCache,
        l2arb_req_ICache,
        l2arb_req_PTW
    } l2arb_req_sender_e;

    typedef enum logic {
        l2arb_id_prio_ICache,
        l2arb_id_prio_DCache
    } l2arb_i_d_priority_e;

    typedef enum logic {
        l2arb_cptw_prio_Cache,
        l2arb_cptw_prio_PTW
    } l2arb_cache_ptw_priority_e;

    typedef enum logic {
        l2arb_id_win_ICache,
        l2arb_id_win_DCache
    } l2arb_i_d_winner_e;

    typedef enum logic {
        l2arb_cptw_win_Cache,
        l2arb_cptw_win_PTW
    } l2arb_cache_ptw_winner_e;

endpackage
