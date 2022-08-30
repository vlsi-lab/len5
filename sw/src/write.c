#include "write.h"

void serial_write(char c)
{
    *((volatile char *)UART_WRITE_BUFFER) = c;
}

/* Redefine stub _write() from newlib */
int _write(int handle, char *data, int size)
{
    int count;
    handle = handle; // unused
    for (count = 0; count < size; count++)
    {
        serial_write(data[count]);
    }
    return count;
}