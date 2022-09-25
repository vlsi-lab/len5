#include "syscall.h"

void main(void)
{
    char str[] = "Hello World!";
    _write(STDOUT, str, sizeof(str));
}