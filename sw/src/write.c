#include "write.h"

void serial_write(char c)
{
    char *p = SERIAL_DATA_ADDR;
    *p = c;
}

/* Redefine stup _write() from newlib */
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