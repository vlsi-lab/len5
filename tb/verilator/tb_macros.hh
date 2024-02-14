#if !defined(TB_MACROS_HH_)
#define TB_MACROS_HH_

#include <cstdio>
#include <libgen.h>
#include <verilated.h>

#define TB_LOG(lvl, ...)\
    logger.log(lvl, __FILE__, __LINE__, __VA_ARGS__)

#define TB_SUCCESS(lvl, ...)\
    logger.success(lvl, __FILE__, __LINE__, __VA_ARGS__)

#define TB_CONFIG(...)\
    logger.config(__FILE__, __LINE__, __VA_ARGS__)

#define TB_WARN(...)\
    logger.warning(__FILE__, __LINE__, __VA_ARGS__)

#define TB_ERR(...)\
    logger.error(__FILE__, __LINE__, __VA_ARGS__)

#define TB_DEBUG(...) TB_LOG(LOG_DEBUG, __VA_ARGS__)
#define TB_INFO(...) TB_LOG(LOG_HIGH, __VA_ARGS__)

typedef enum {
    LOG_NONE,
    LOG_LOW,
    LOG_MEDIUM,
    LOG_HIGH,
    LOG_FULL,
    LOG_DEBUG
} log_lvl_t;

// Class definition
class TbLogger
{
private:
    char str_buf[256];
    static log_lvl_t log_lvl;
    VerilatedContext *vcntx; // handle to the simulation context

    // Get current simulation time if available
    vluint64_t getSimTime();
public:
    TbLogger();
    ~TbLogger();

    // Set the verilated context (used for timestamping)
    void setSimContext(VerilatedContext *cntx);

    // Alternative ways to set the log level
    void setLogLvl(log_lvl_t lvl);
    void setLogLvl(int lvl); // particularly convenient when using optarg
    void setLogLvl(char *log_lvl);
    
    // Get the current log level
    log_lvl_t getLogLvl();

    // Log messages
    void log(log_lvl_t lvl, const char *file, const unsigned int line, const char *fmt...);
    void success(log_lvl_t lvl, const char *file, const unsigned int line, const char *fmt...);
    void config(const char *file, const unsigned int line, const char *fmt...);
    void warning(const char *file, const unsigned int line, const char *fmt...);
    void error(const char *file, const unsigned int line, const char *fmt...);
};

// Shared logger (for macros)
extern TbLogger logger;

#endif // TB_MACROS_HH_
