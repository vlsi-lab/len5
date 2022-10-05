#include <stdio.h>

int main(void)
{
    int a = 0;

    for (size_t i = 0; i < 10; i++)
    {
        a++;
    }

    printf("Hello LEN%d!\n", a >> 1);
    // puts("Hello, LEN5!");
    return 0;
}