#define SERIAL_DATA_ADDR (char *)0x0000000000000010

void serial_write(char c)
{
    char *p = SERIAL_DATA_ADDR;
    *p = c;
}

void main(void)
{
    char c = 'a';
    serial_write(c);
}