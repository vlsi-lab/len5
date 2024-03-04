#ifndef LEN5_H_
#define LEN5_H_

/********************/
/* ---- MACROS ---- */
/********************/

#include <sys/types.h>

/********************/
/* ---- MACROS ---- */
/********************/
/* Peripherals base address */
// NOTE: only powers of 2 are supported. This value must be consistent with
// MMAP_MASK in `len5_config_pkg.sv`.
#define PERI_BASE ((unsigned char *) 0x20000000) // 512MB

/* Serial interface registers */
#define UART_BASE ((unsigned char *) (PERI_BASE + 0x00))
#define UART_WRITE_REG (*(UART_BASE + 0x00))
#define UART_WRITE_FLAG (*(UART_BASE + 0x01))
#define UART_READ_REG (*(UART_BASE + 0x02))
#define UART_READ_FLAG (*(UART_BASE + 0x03))

/* Exit code register */
#define EXIT_REG_BASE ((unsigned char *) (PERI_BASE + 0x100))
#define EXIT_REG (*(EXIT_REG_BASE + 0x00))

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
