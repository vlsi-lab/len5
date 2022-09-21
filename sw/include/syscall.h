#ifndef WRITE_H_
#define WRITE_H_

// HEADERS
// -------
#include <sys/stat.h>
#include <newlib.h>
#include <unistd.h>
#include <errno.h>
#include "syscall.h"

// MACROS
// ------

/* Serial interface registers */
#ifndef UART_BASE
#define UART_BASE (unsigned char *)0x100
#endif
#define UART_WRITE_REG (*(UART_BASE + 0x00))
#define UART_WRITE_FLAG (*(UART_BASE + 0x01))
#define UART_READ_REG (*(UART_BASE + 0x02))
#define UART_READ_FLAG (*(UART_BASE + 0x03))

/* Exit code register */
#ifndef EXIT_REG
#define EXIT_REG (*(unsigned char *)0x200)
#endif

/* STDIN, STDOUT, and STDERR "file descriptors" */
#define STDIN 0
#define STDOUT 1
#define STDERR 2

// FUNCTION PROTOTYPES
// -------------------

int _access(const char *file, int mode);
int _chdir(const char *path);
int _chmod(const char *path, mode_t mode);
int _chown(const char *path, uid_t owner, gid_t group);
int _close(int file);
int _execve(const char *name, char *const argv[], char *const env[]);

/**
 * @brief	Minimal exit function
 *
 * @details	Store the exit value in a predefined memory location and waste
 * power forever because we don't have interrupts (yet...).
 *
 * @param	exit_status: the exit status
 */
void _exit(int exit_status);

int _faccessat(int dirfd, const char *file, int mode, int flags);
int _fork(void);
int _fstat(int file, struct stat *st);
int _fstatat(int dirfd, const char *file, struct stat *st, int flags);
int _ftime(void *tp);
char *_getcwd(char *buf, size_t size);
int _getpid();
int _gettimeofday(struct timeval *tp, void *tzp);
int _isatty(int file);
int _kill(int pid, int sig);
int _link(const char *old_name, const char *new_name);
off_t _lseek(int file, off_t ptr, int dir);
int _lstat(const char *file, struct stat *st);
int _open(const char *name, int flags, int mode);
int _openat(int dirfd, const char *name, int flags, int mode);
ssize_t _read(int file, void *ptr, size_t len);
int _stat(const char *file, struct stat *st);
long _sysconf(int name);
clock_t _times(void *buf);
int _unlink(const char *name);
int _utime(const char *path, void *times);
int _wait(int *status);

/**
 * @brief	Minimal serial interface
 *
 * @details	Write the input character to a designated memory location defined
 * in 'serial_write.h'.
 *
 * @param	c: the character to write
 */
void serial_write(char c);

/**
 * @brief	Stub _write implementation
 *
 * @details	Redirect STDOUT to a low-level serial interface implemented by
 * 'serial_write()'.
 *
 * @param	handle: buffer file descriptor (only STDOUT is supported)
 * @param   data: input buffer
 * @param   size: buffer length
 *
 * @return	Returns 0 is successful, -1 otherwise
 *
 * @retval	{0 :success value}
 */
ssize_t _write(int handle, const char *data, size_t size);

int _brk(void *addr);
void *_sbrk(ptrdiff_t incr);

#endif // WRITE_H_
