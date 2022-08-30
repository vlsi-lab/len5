#ifndef WRITE_H_
#define WRITE_H_

/* UART base address provided by linker script */
extern volatile char *__uart_base;
#define UART_BASE __uart_base
#define UART_WRITE_BUFFER (UART_BASE + 0x00)
#define UART_READ_BUFFER (UART_BASE + 0x01)

void serial_write(char c);
int _write(int handle, char *data, int size);

#endif // WRITE_H_
