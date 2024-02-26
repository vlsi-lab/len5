/* Common main.c for the benchmarks

   Copyright (C) 2014 Embecosm Limited and University of Bristol
   Copyright (C) 2018-2019 Embecosm Limited

   Contributor: James Pallister <james.pallister@bristol.ac.uk>
   Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>

   This file is part of Embench and was formerly part of the Bristol/Embecosm
   Embedded Benchmark Suite.

   SPDX-License-Identifier: GPL-3.0-or-later */

#include "support.h"
#include <stdio.h>


int __attribute__ ((used))
main (int argc __attribute__ ((unused)),
      char *argv[] __attribute__ ((unused)))
{
  int i;
  volatile int result;
  int correct;
  int mcycle_start, mcycle_stop;
  int minstret_start, minstret_stop;

  initialise_benchmark ();
  warm_caches (WARMUP_HEAT);

  asm volatile ("csrr %0, mcycle" : "=r" (mcycle_start));
  asm volatile ("csrr %0, minstret" : "=r" (minstret_start));
  result = benchmark ();
  asm volatile ("csrr %0, mcycle" : "=r" (mcycle_stop));
  asm volatile ("csrr %0, minstret" : "=r" (minstret_stop));


  /* bmarks that use arrays will check a global array rather than int result */
  correct = verify_benchmark (result);

  printf("Cycles: %d\n", mcycle_stop - mcycle_start);
  printf("Instructions: %d\n", minstret_stop - minstret_start);
  return (!correct);

}				/* main () */


/*
   Local Variables:
   mode: C
   c-file-style: "gnu"
   End:
*/
