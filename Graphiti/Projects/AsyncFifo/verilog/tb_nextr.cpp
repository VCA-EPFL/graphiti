// Exhaustive check of the exported read-domain next-state netlist against `rNext` of the Lean
// model (n = 2): all 2^11 input combinations.  The counterpart of tb_next.cpp for the write
// domain.  It cannot prove anything about the Verilog, but it does catch a wrong bus layout or
// a wrong template body, which is what the export can get wrong.
//
// Bus layout: the read state register stores `!empty` (StRegR.stBit), so
//   st = {q2[2:0], !empty, ptr[2:0]}      d = {gnext[2:0], st'[6:0]}
#include "Vnext_state_r.h"
#include "verilated.h"
#include <cstdio>

static unsigned ungray3(unsigned q) { return (q ^ (q >> 1) ^ (q >> 2)) & 7u; }

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Vnext_state_r *dut = new Vnext_state_r;
  unsigned long checked = 0, bad = 0;

  for (unsigned st = 0; st < 128; ++st)
    for (unsigned q1 = 0; q1 < 8; ++q1)
      for (unsigned inc = 0; inc < 2; ++inc) {
        dut->st = st; dut->q1 = q1; dut->inc = inc;
        dut->eval();

        const unsigned ptr = st & 7u, nempty = (st >> 3) & 1u, q2 = (st >> 4) & 7u;
        const unsigned empty = !nempty;
        const unsigned ok = (inc && !empty) ? 1u : 0u;          // rNext: inc && !st.empty
        const unsigned ptrn = ok ? ((ptr + 1u) & 7u) : ptr;
        const unsigned emptyn = (ptrn == ungray3(q2)) ? 1u : 0u;
        const unsigned q2n = q1;
        const unsigned gnext = (ptrn ^ (ptrn >> 1)) & 7u;
        const unsigned expected = ptrn | ((!emptyn ? 1u : 0u) << 3) | (q2n << 4) | (gnext << 7);

        if ((unsigned)dut->d != expected) {
          if (bad < 5)
            printf("MISMATCH st=%02x q1=%u inc=%u: netlist %03x, rNext %03x\n",
                   st, q1, inc, (unsigned)dut->d, expected);
          bad++;
        }
        checked++;
      }
  if (bad) { printf("next_state_r: %lu of %lu combinations disagree with rNext\n", bad, checked); return 1; }
  printf("next_state_r: all %lu input combinations agree with rNext\n", checked);
  return 0;
}
