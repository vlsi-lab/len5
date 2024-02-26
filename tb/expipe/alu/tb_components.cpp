#include "tb_components.hh"
#include "Valu_expipe_pkg.h"
#include "tb_macros.hh"
#include <inttypes.h>

const char * op_str[] = {
    "ALU_ADD",
    "ALU_ADDW",
    "ALU_SUB",
    "ALU_SUBW",
    "ALU_AND",
    "ALU_OR",
    "ALU_XOR",
    "ALU_SLL",
    "ALU_SLLW",
    "ALU_SRL",
    "ALU_SRLW",
    "ALU_SRA",
    "ALU_SRAW",
    "ALU_SLT",
    "ALU_SLTU",
};

ReqTx::ReqTx()
{
}

ReqTx::~ReqTx()
{
}

RspTx::RspTx()
{
}

RspTx::~RspTx()
{
}

Drv::Drv(Valu *dut)
{
    this->dut = dut;
}

Drv::~Drv()
{
}

void Drv::drive(ReqTx *req)
{
    dut->valid_i = 0;
    dut->flush_i = 0;
    uint8_t p;

    // Otherwise, drive RS1 and RS2 with the current request
    if (req != NULL)
    {
        dut->rs1_i = req->rs1;
        dut->rs2_i = req->rs2;
        dut-> ctl_i = req->alu_ctl;
        dut->valid_i = req->valid;
        dut->flush_i = req->flush;
        dut->rob_idx_i = req->rob_idx;  
    }
}

Scb::Scb()
{
    this->tx_num = 0;
    this->err_num = 0;
}

Scb::~Scb()
{
}

void Scb::writeReq(ReqTx *req)
{
    this->req_q.push_back(req);
}

void Scb::writeRsp(RspTx *rsp)
{
    this->rsp_q.push_back(rsp);
    this->checkRes();
}

void Scb::flush() 
{
    // Tell me that C++ sucks without telling me that C++ sucks...
    while (!this->req_q.empty()) {
        ReqTx *req = this->req_q.front();
        this->req_q.pop_front();
        delete req;
    }
    while (!this->rsp_q.empty()) {
        RspTx *rsp = this->rsp_q.front();
        this->rsp_q.pop_front();
        delete rsp;
    }
}

void Scb::checkRes()
{
    // Expected result
    vluint64_t exp_res = 0;
    vluint32_t exp_res_32 = 0;
    if (this->req_q.empty())
    {
        TB_ERR("SCB > Received response without request!");
    }

    ReqTx *req = this->req_q.front();
    this->req_q.pop_front();
    RspTx * rsp = this->rsp_q.front();
    this->rsp_q.pop_front();
    tx_num++;

    int64_t rs1_int = (int64_t) req->rs1;
    int64_t rs2_int = (int64_t) req->rs2;
    
    uint64_t rs1_w_int = (int32_t) req->rs1;
    uint64_t rs2_w_int = (int32_t) req->rs2;

    // shift amount
    const vluint8_t shamt = req->rs2 & 0x3F;
    const vluint8_t shamt_w = req->rs2 & 0x1F;

    // arithmetic shift
    unsigned char rs1_neg = (rs1_int >> 63);
    unsigned char rs1_w_neg = (rs1_w_int >> 31);

    // Check if the result is correct
    switch (req->alu_ctl)
    {
    case Valu_expipe_pkg::ALU_ADD:
        exp_res = (vluint64_t) rs1_int + rs2_int;
        break;
    case Valu_expipe_pkg::ALU_ADDW:
        exp_res_32 = (vluint32_t) rs1_w_int + rs2_w_int;
        // sign extend the result on 64 bits
        exp_res = (exp_res_32 & 0x80000000) ? 0xffffffff00000000 | exp_res_32 : exp_res_32;
        break;
    case Valu_expipe_pkg::ALU_SUB:
        exp_res = (vluint64_t) rs1_int - rs2_int;
        break;
    case Valu_expipe_pkg::ALU_SUBW:
        exp_res_32 = (int32_t) rs1_w_int - rs2_w_int;
        // sign extend the result on 64 bits
        exp_res = (exp_res_32 & 0x80000000) ? 0xffffffff00000000 | exp_res_32 : exp_res_32;
        break;
    case Valu_expipe_pkg::ALU_AND:
        exp_res = (vluint64_t) (req->rs1 & req->rs2);
        break;
    case Valu_expipe_pkg::ALU_OR:
        exp_res = (vluint64_t) (req->rs1 | req->rs2);
        break;
    case Valu_expipe_pkg::ALU_XOR:
        exp_res = (vluint64_t) (req->rs1 ^ req->rs2);
        break;
    case Valu_expipe_pkg::ALU_SLL:
        exp_res = (vluint64_t) (req->rs1 << shamt);
        break;
    case Valu_expipe_pkg::ALU_SLLW:
        exp_res_32 = (vluint32_t) (rs1_w_int << shamt_w);
        // sign extend the result on 64 bits
        exp_res = ((exp_res_32 & 0x80000000) != 0) ? 0xffffffff00000000 | exp_res_32 : exp_res_32;
        break;
    case Valu_expipe_pkg::ALU_SRL:
        exp_res = (vluint64_t) (req->rs1 >> shamt);
        break;
    case Valu_expipe_pkg::ALU_SRLW:
        exp_res_32 = (vluint32_t) (((vluint32_t) req->rs1) >> shamt_w);
        // sign extend the result on 64 bits
        exp_res = ((exp_res_32 & 0x80000000) != 0) ? 0xffffffff00000000 | exp_res_32 : exp_res_32;
        break;
    case Valu_expipe_pkg::ALU_SRA:
        exp_res = (vluint64_t) (rs1_int >> shamt);
        break;
    case Valu_expipe_pkg::ALU_SRAW:
        exp_res_32 = (vluint32_t) (rs1_w_int >> shamt_w);
        // sign extend the result on 64 bits
        exp_res = ((exp_res_32 & 0x80000000) != 0) ? 0xffffffff00000000 | exp_res_32 : exp_res_32;
        break;
    case Valu_expipe_pkg::ALU_SLT:
        exp_res = (vluint64_t) (rs1_int < rs2_int) ? 1 : 0;
        break;
    case Valu_expipe_pkg::ALU_SLTU:
        exp_res = (vluint64_t) (req->rs1 < req->rs2) ? 1 : 0;
        break;
    default: // ADD
        exp_res = (vluint64_t) req->rs1 + req->rs2;
        break;
    }
    if ( rsp->res != exp_res)
    {
        TB_ERR("Received wrong result!");
        TB_ERR("RSP > op: %-5s rs1: 0x%016lx | rs2: 0x%016lx --> res: 0x%016lx (expected: 0x%016lx)", 
                op_str[req->alu_ctl], req->rs1, req->rs2, rsp->res, exp_res);
        err_num++;
    }
    else
    {
        TB_SUCCESS(LOG_MEDIUM, "RSP > op: %-5s rs1: 0x%016lx | rs2: 0x%016lx --> res: 0x%016lx (expected: 0x%016lx)", 
                op_str[req->alu_ctl], req->rs1, req->rs2, rsp->res, exp_res);
    }
    // Clean up
    delete req;
    delete rsp;
}

unsigned int Scb::getTxNum()
{
    return this->tx_num;
}

unsigned int Scb::getErrNum()
{
    return this->err_num;
}

int Scb::isDone()
{
    return this->req_q.empty() && this->rsp_q.empty();
}

ReqMonitor::ReqMonitor(Valu *dut, Scb *scb)
{
    this->dut = dut;
    this->scb = scb;
    this->req = NULL;
    this->req_busy = false; // reset request status
}

ReqMonitor::~ReqMonitor()
{
}

void ReqMonitor::monitor()
{
    // If flush is requested, clear the scoreboard
    if (dut->flush_i)
    {
        scb->flush();
        this->req_busy = false;
        TB_LOG(LOG_MEDIUM, "REQ > Flush requested");
        return;
    }
    // Else, check if there's a new request
    else if (dut->valid_i)
    {
        // Fetch the data from the DUT interface
        this->req = new ReqTx();
        this->req->rs1 = dut->rs1_i;
        this->req->rs2 = dut->rs2_i;
        this->req->alu_ctl = dut->ctl_i;
        this->req->rob_idx = dut->rob_idx_i;
        // Send the request to the scoreboard
        scb->writeReq(this->req);

        // Print the request content
        TB_LOG(LOG_HIGH, "REQ > op: %-5s | rs1:  0x%" PRIx64 " | rs2:  0x%" PRIx64 " ", op_str[this->req->alu_ctl], this->req->rs1, this->req->rs2);
    }
}

RspMonitor::RspMonitor(Valu *dut, Scb *scb)
{
    this->dut = dut;
    this->scb = scb;
}

RspMonitor::~RspMonitor()
{
}

void RspMonitor::monitor()
{
    // Check if the DUT produced any response
    if (dut->valid_o && !dut->flush_i)
    {
        // Fetch the data from the DUT interface
        RspTx *rsp = new RspTx();
        rsp->res = dut->result_o;
        scb->writeRsp(rsp);
    }
}