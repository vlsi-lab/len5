#include <stdio.h>

int main(void)
{
    int a = 0, b = 1;
    int c = 0;

    for (size_t i = 0; i < 100 && c != 5; i++)
    {
        a = a + 1;
        b = 2 * a;
        c = b - a;
        printf("%d\n", c);
    }

    printf("Hello LEN%d!\n", c);
    // puts("Hello, LEN5!");
    return 0;
}