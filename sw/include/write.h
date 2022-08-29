#ifndef WRITE_H_
#define WRITE_H_

#define SERIAL_DATA_ADDR (char *)0x0000000000000010

void serial_write(char c);
int _write(int handle, char *data, int size);

#endif // WRITE_H_
