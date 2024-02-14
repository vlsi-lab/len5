#ifndef LEN5_H_
#define LEN5_H_

/********************/
/* ---- MACROS ---- */
/********************/

#include <sys/types.h>

/********************/
/* ---- MACROS ---- */
/********************/

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

/*********************************/
/* ---- FUNCTION PROTOTYPES ---- */
/*********************************/

/**
 * @brief	Minimal serial interface
 *
 * @details	Write the input character to a designated memory location defined
 * in 'serial_write.h'.
 *
 * @param	c: the character to write
 */
void serial_write(char c);

#endif // LEN5_H_
