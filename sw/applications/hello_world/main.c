#include <stdio.h>

int main(void)
{
    int a = 0;

    for (size_t i = 0; i < 160; i++) {
        a++;
    }

    printf("Hello LEN%d!\n\r", a >> 5);
    return 0;
}