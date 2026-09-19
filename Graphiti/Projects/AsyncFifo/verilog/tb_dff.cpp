// Differential test: the exported gate-level flip-flop against the Lean model it was generated
// from, on the same stimulus, one Verilog time unit per instant of the Lean timeline.
//
// This is the test that says the exporter is faithful.  `Dff.dffOut` is the Lean netlist's own
// output function, `dff_trace.txt` is its trace, and the module here is what VerilogGates.lean
// emitted from `Dff.dffLowered`.  If they agree instant for instant then `assign #1` is Lean's
// `gateOut` and the two really are the same circuit -- including the cross-coupled NAND latch,
// which is the part a simulator is most likely to get wrong.
//
// It also pins the convention everything else depends on: ONE TIME UNIT IS ONE INSTANT.  Drive
// the design off that timeline -- several units per clock phase, say -- and a correct circuit
// looks broken.
#include "Vdff.h"
#include "verilated.h"
#include <cstdio>
#include <string>
#include <fstream>
int main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);
  std::ifstream f("dff_trace.txt");
  std::string qref, clk, d, crn;
  std::getline(f, qref); std::getline(f, clk); std::getline(f, d); std::getline(f, crn);
  VerilatedContext ctx; Vdff dut{&ctx};
  int bad = 0, first = -1;
  for (size_t t = 0; t < qref.size(); t++) {
    dut.clk = clk[t] - '0'; dut.d = d[t] - '0'; dut.clrn = crn[t] - '0';
    // advance exactly one instant, letting every unit-delay gate fire
    uint64_t target = (uint64_t)t + 1;
    while (ctx.time() < target) {
      uint64_t n = target;
      if (dut.eventsPending() && dut.nextTimeSlot() < n) n = dut.nextTimeSlot();
      ctx.time(n); dut.eval();
    }
    dut.eval();
    int got = dut.q, want = qref[t] - '0';
    if (got != want) { if (first < 0) first = (int)t; bad++; }
  }
  if (bad) printf("dff: %d of %zu instants differ from Lean (first at t=%d)\n", bad, qref.size(), first);
  else printf("dff: all %zu instants agree with Lean's dffOut\n", qref.size());
  return bad ? 1 : 0;
}
