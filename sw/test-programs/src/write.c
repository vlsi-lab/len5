#include "syscall.h"

void main(void)
{
    char str[] = "Hello World!\n";
    _write(STDOUT, str, sizeof(str));
}