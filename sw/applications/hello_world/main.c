#include <stdio.h>

// Random string
char str[] = "EDIOLOGNOM";

// Function prototype
void print_char(char *c);

// Program body
int main(void)
{
    int a = 0;

    // Waste power
    for (size_t i = 0; i < 160; i++) {
        a++;
    }

    // Welcome message
    printf("Hello LEN%d!\n", a >> 5);

    // Recursively question Faith
    print_char(str);
    printf("\n");

    // Return with success (since we successfully questioned Faith)
    return 0;
}

// Print a character
void print_char(char *c)
{
    char *next = c + 1;
    printf("%c", *c);
    if (*next != 0) print_char(next);
    else printf("O");
    printf("%c", *c);
    return;
}
