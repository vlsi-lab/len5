#include "tb_macros.hh"

TbLogger::TbLogger() 
{
    // By default, set the log level to medium
    this->log_lvl = LOG_MEDIUM;
    this->vcntx = NULL;
}

TbLogger::~TbLogger()
{
}

log_lvl_t TbLogger::log_lvl;

vluint64_t TbLogger::getSimTime()
{
    if (this->vcntx != NULL)
        return this->vcntx->time();
    else
        return 0;
}

void TbLogger::setSimContext(VerilatedContext *cntx)
{
    this->vcntx = cntx;
}

void TbLogger::setLogLvl(log_lvl_t lvl)
{
    this->log_lvl = lvl;
}

void TbLogger::setLogLvl(char *lvl)
{
    if (!strcmp(lvl, "LOG_NONE")) this->log_lvl = LOG_NONE;
    else if (!strcmp(lvl, "LOG_LOW")) this->log_lvl = LOG_LOW;
    else if (!strcmp(lvl, "LOG_HIGH")) this->log_lvl = LOG_HIGH;
    else if (!strcmp(lvl, "LOG_FULL")) this->log_lvl = LOG_FULL;
    else if (!strcmp(lvl, "LOG_DEBUG")) this->log_lvl = LOG_DEBUG;
    else this->log_lvl = LOG_MEDIUM;
}

void TbLogger::setLogLvl(int lvl)
{
    switch (lvl)
    {
    case 0:
        this->log_lvl = LOG_NONE;
        break;
    case 1:
        this->log_lvl = LOG_LOW;
        break;
    case 2:
        this->log_lvl = LOG_MEDIUM;
        break;
    case 3:
        this->log_lvl = LOG_HIGH;
        break;
    case 4:
        this->log_lvl = LOG_FULL;
        break;
    case 5:
        this->log_lvl = LOG_DEBUG;
        break;
    default:
        this->log_lvl = LOG_MEDIUM;
        break;
    }
}

log_lvl_t TbLogger::getLogLvl()
{
    return this->log_lvl;
}

void TbLogger::log(log_lvl_t lvl, const char *file, const unsigned int line, const char *fmt, ...)
{
    if (lvl <= this->log_lvl)
    {
        char n[256];
        strcpy(n, file);
        sprintf(this->str_buf, "[LOG   ] %s:%u >", basename(n), line);
        printf("%-35s [%5lu] ", this->str_buf, this->getSimTime());
        va_list arg_ptr;
        va_start(arg_ptr, fmt);
        vprintf(fmt, arg_ptr);
        va_end(arg_ptr);
        printf("\n");
    }
}

void TbLogger::success(log_lvl_t lvl, const char *file, const unsigned int line, const char *fmt, ...)
{
    if (lvl <= this->log_lvl)
    {
        char n[256];
        strcpy(n, file);
        sprintf(this->str_buf, "\033[1;32m[OK!   ] %s:%u >\033[0m", basename(n), line);
        printf("%-46s [%5lu] ", this->str_buf, this->getSimTime());
        va_list arg_ptr;
        va_start(arg_ptr, fmt);
        vprintf(fmt, arg_ptr);
        va_end(arg_ptr);
        printf("\n");
    }
}

void TbLogger::config(const char *file, const unsigned int line, const char *fmt, ...)
{
    char n[256];
    strcpy(n, file);
    sprintf(this->str_buf, "\033[1m[CONFIG] %s:%u >\033[0m", basename(n), line);
    printf("%-44s", this->str_buf);
    va_list arg_ptr;
    va_start(arg_ptr, fmt);
    vprintf(fmt, arg_ptr);
    va_end(arg_ptr);
    printf("\n");
}

void TbLogger::warning(const char *file, const unsigned int line, const char *fmt, ...)
{
    char n[256];
    strcpy(n, file);
    sprintf(this->str_buf, "\033[1;33m[WARN  ] %s:%u >\033[0m", basename(n), line);
    fprintf(stderr, "%-46s [%5lu] ", this->str_buf, this->getSimTime());
    va_list arg_ptr;
    va_start(arg_ptr, fmt);
    vfprintf(stderr, fmt, arg_ptr);
    va_end(arg_ptr);
    fprintf(stderr, "\n");
}

void TbLogger::error(const char *file, const unsigned int line, const char *fmt, ...)
{
    char n[256];
    strcpy(n, file);
    sprintf(this->str_buf, "\033[1;31m[ERR!  ] %s:%u >\033[0m", basename(n), line);
    fprintf(stderr, "%-46s [%5lu] ", this->str_buf, this->getSimTime());
    va_list arg_ptr;
    va_start(arg_ptr, fmt);
    vfprintf(stderr, fmt, arg_ptr);
    va_end(arg_ptr);
    fprintf(stderr, "\n");
}
