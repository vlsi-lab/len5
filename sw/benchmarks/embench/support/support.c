void __attribute__ ((noinline)) __attribute__ ((externally_visible))
start_trigger ()
{
  __asm__ volatile ("nop" : : : "memory");
}

void __attribute__ ((noinline)) __attribute__ ((externally_visible))
stop_trigger ()
{
  __asm__ volatile ("nop" : : : "memory");
}