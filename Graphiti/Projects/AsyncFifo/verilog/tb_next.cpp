// Exhaustive check of the exported gate netlist `next_state.v` against the next-state function
// `wNext` of the Lean model (n = 2, 1-bit data): all 2^12 input combinations.
//
// This is the simulation counterpart of `GateNext.pack_identity`, which the Lean kernel checks
// over the same 4096 combinations.  It does not prove anything about the Verilog — nothing
// links the exporter to Lean's semantics — but it does catch a wrong bus layout or a wrong
// template body, which is exactly what the export could get wrong.
//
// Bus layout (see Verilog.lean):
//   st = {q2[2:0], full, ptr[2:0]}
//   d  = {data, addr[1:0], we, gnext[2:0], st'[6:0]}
#include "Vnext_state.h"
#include "verilated.h"
#include <cstdio>

// `ungray` of Gray.lean at width 3.
static unsigned ungray3(unsigned q) { return (q ^ (q >> 1) ^ (q >> 2)) & 7u; }

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Vnext_state *dut = new Vnext_state;
  unsigned long checked = 0;

  for (unsigned st = 0; st < 128; ++st)
    for (unsigned q1 = 0; q1 < 8; ++q1)
      for (unsigned inc = 0; inc < 2; ++inc)
        for (unsigned data = 0; data < 2; ++data) {
          dut->st = st;
          dut->q1 = q1;
          dut->inc = inc;
          dut->data = data;
          dut->eval();

          const unsigned ptr = st & 7u, full = (st >> 3) & 1u, q2 = (st >> 4) & 7u;
          const unsigned ok = (inc && !full) ? 1u : 0u;              // wNext: inc && !st.full
          const unsigned ptrn = ok ? ((ptr + 1u) & 7u) : ptr;        // the incremented pointer
          const unsigned fulln = (ptrn == ((ungray3(q2) + 4u) & 7u)) ? 1u : 0u;
          const unsigned q2n = q1;                                   // second synchroniser stage
          const unsigned gnext = (ptrn ^ (ptrn >> 1)) & 7u;          // gray ptr'
          const unsigned we = ok, addr = ptr & 3u;                   // memory write command
          const unsigned expected = ptrn | (fulln << 3) | (q2n << 4) | (gnext << 7) |
                                    (we << 10) | (addr << 11) | (data << 13);

          if ((unsigned)dut->d != expected) {
            printf("MISMATCH st=%02x q1=%u inc=%u data=%u: netlist %04x, wNext %04x\n", st, q1,
                   inc, data, (unsigned)dut->d, expected);
            return 1;
          }
          ++checked;
        }

  printf("next_state: all %lu input combinations agree with wNext\n", checked);
  dut->final();
  delete dut;
  return 0;
}
