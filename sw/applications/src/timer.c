#include <stdio.h>
#include <time.h>

int main(void)
{
    clock_t cycle_start = clock();
    printf("Hello, LEN5!\n");
    clock_t cycle_stop = clock();
    clock_t cycle_delay = cycle_stop - cycle_start;
    printf("Latency: %lu cycles\n", cycle_delay);
    return 0;
}
