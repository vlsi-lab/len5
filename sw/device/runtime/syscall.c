// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: syscall.c
// Author: Michele Caon
// Date: 16/09/2022

/******************/
/* ---- INFO ---- */
/******************/
/*
 * This file implements a ridiculously small set of system calls in a
 * ridiculously simple way. It is inspired by the same file from ETH
 * Zurich and, likewise, it's meant to substitute Newlib's default
 * implementation.
 */

// HEADERS
// -------
#include <sys/stat.h>
#include <sys/times.h>
#include <sys/timeb.h>
#include <sys/utime.h>
#include <newlib.h>
#include <unistd.h>
#include <errno.h>

// LEN5 headers
#include "len5.h"
#include "syscall.h"

// GLOBAL VARIABLES
// ----------------

// Heap top and bottom, provided by the linker script
extern char __heap_bottom[];
extern char __heap_top[];
static char *brk = __heap_bottom;

#ifdef SPIKE_CHECK
// Spike exit function
extern void tohost_exit(int code);
#endif // SPIKE_CHECK

// FUNCTION DEFINITIONS
// --------------------
void unimplemented_syscall(void)
{
    const char *msg = "Unimplemented system call!\n";
    _write(STDOUT_FILENO, msg, sizeof(msg));
}

int _access(const char *file, int mode)
{
    errno = ENOSYS;
    return -1;
}

int _chdir(const char *path)
{
    errno = ENOSYS;
    return -1;
}

int _chmod(const char *path, mode_t mode)
{
    errno = ENOSYS;
    return -1;
}

int _chown(const char *path, uid_t owner, gid_t group)
{
    errno = ENOSYS;
    return -1;
}

int _close(int file)
{
    return -1;
}

int _execve(const char *name, char *const argv[], char *const env[])
{
    errno = ENOMEM;
    return -1;
}

/**
 * @brief	Minimal exit function
 *
 * @details	Store the exit value in a predefined memory location and waste
 * power forever because we don't have interrupts (yet...).
 *
 * @param	exit_status: the exit status
 */
void _exit(int exit_status)
{
    EXIT_REG = exit_status;
#ifdef SPIKE_CHECK
    tohost_exit(exit_status);
#endif
    asm volatile("wfi");
    __builtin_unreachable(); // prevent returning instruction warning
}

int _faccessat(int dirfd, const char *file, int mode, int flags)
{
    errno = ENOSYS;
    return -1;
}

int _fork(void)
{
    errno = EAGAIN;
    return -1;
}

int _fstat(int file, struct stat *st)
{
    st->st_mode = S_IFCHR;
    return 0;
    // errno = -ENOSYS;
    // return -1;
}

int _fstatat(int dirfd, const char *file, struct stat *st, int flags)
{
    errno = ENOSYS;
    return -1;
}

int _ftime(struct timeb *tp)
{
    errno = ENOSYS;
    return -1;
}

char *_getcwd(char *buf, size_t size)
{
    errno = -ENOSYS;
    return NULL;
}

int _getpid()
{
    return 1;
}

int _gettimeofday(struct timeval *tp, void *tzp)
{
    errno = -ENOSYS;
    return -1;
}

int _isatty(int file)
{
    return (file == STDOUT_FILENO);
}

int _kill(int pid, int sig)
{
    errno = EINVAL;
    return -1;
}

int _link(const char *old_name, const char *new_name)
{
    errno = EMLINK;
    return -1;
}

off_t _lseek(int file, off_t ptr, int dir)
{
    return 0;
}

int _lstat(const char *file, struct stat *st)
{
    errno = ENOSYS;
    return -1;
}

int _open(const char *name, int flags, int mode)
{
    return -1;
}

int _openat(int dirfd, const char *name, int flags, int mode)
{
    errno = ENOSYS;
    return -1;
}

ssize_t _read(int file, void *ptr, size_t len)
{
    if (file != STDIN)
        return -1;

    for (size_t i = 0; i < len; i++)
    {
        /* Busy-wait for a new character */
        while (!UART_READ_FLAG)
            ;
        /* Read the character and clear the flag */
        *((volatile char *)ptr) = UART_READ_REG;
        ptr++;
    }
    return 0;
}

int _stat(const char *file, struct stat *st)
{
    st->st_mode = S_IFCHR;
    return 0;
    // errno = ENOSYS;
    // return -1;
}

long _sysconf(int name)
{
    return -1;
}

/**
 * @brief	Get the number of elapsed clock cycles
 *
 * @details	This function returns the current value of the 'mcycle' CSR, that
 *          records the number of elapsed clock cycle since the startup. If the
 *          operating frequency is known, this value can be used to determine
 *          a program's execution time.
 *
 * @return	The number of elapsed clock cycles
 */
clock_t _times(struct tms *buf)
{
    clock_t t;
    asm volatile("csrr %[val], mcycle"
                 : [val] "=r"(t));
    buf->tms_stime = t;
    buf->tms_utime = 0;
    buf->tms_cstime = 0;
    buf->tms_cutime = 0;
    return t;
}

int _unlink(const char *name)
{
    errno = ENOENT;
    return -1;
}

int _utime(const char *path, const struct utimbuf *times)
{
    errno = ENOSYS;
    return -1;
}

int _wait(int *status)
{
    errno = ECHILD;
    return -1;
}

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
ssize_t _write(int handle, const char *data, size_t size)
{
    const char *end_data = data + size;

    // Skip files other than STDOUT
    if (handle != STDOUT) {
        errno = ENOSYS;
        return -1;
    }

    while (data != end_data) {
        serial_write(*data);
        data++;
    }

    return size;
}

int _brk(void *addr)
{
    brk = addr;
    return 0;
}

void *_sbrk(ptrdiff_t incr)
{
    char *old_brk = brk;

    if (&__heap_bottom[0] == &__heap_top[0])
    {
        return NULL;
    }

    if ((brk += incr) < __heap_top)
    {
        brk += incr;
    }
    else
    {
        brk = __heap_top;
    }
    return old_brk;
}
