// Self-checking testbench for the gate-level export of the whole FIFO.
//
// The design under test is `async_fifo` from VerilogGates.lean: two clock domains of unit-delay
// gates, six `settling_dff` cells and nothing else sequential.  Built with --timing, so Verilator
// honours the `#1` on every gate, and ONE SIMULATION TIME UNIT IS ONE INSTANT of the Lean model
// -- the same unit the delay windows in the refinement theorem are counted in.  That
// correspondence is the whole point: with it, `assign #1` is exactly Lean's `gateOut`, and
// tb_dff.cpp checks the two agree instant for instant on the flip-flop.  Get it wrong -- advance
// several units per clock phase, say -- and the circuit is being driven off its timeline, which
// looks like the design failing.
//
// Data is one bit wide, as in the verified design, so a run is checked by the *sequence* of bits
// rather than by tagging items:
//
//   * every bit dequeued must be the next bit enqueued  (FIFO order, no corruption);
//   * the number of items in flight never exceeds the depth, 4;
//   * a run must actually move data, or the checks above would pass vacuously.
//
// Conventions follow the Lean model: a rising edge at instant t is clk(t)=1 with clk(t-1)=0, and
// the enqueue/dequeue decision at that edge uses the state settled just before it.  Clock periods
// are kept above the theorem's budget of 22 instants.
#include "Vasync_fifo.h"
#include "verilated.h"
#include <cstdio>
#include <deque>
#include <vector>

struct Scenario { const char* name; int wper, wph, rper, rph, wstop, steps; };

// A cheap deterministic bit source, so runs are reproducible.
static int bit_of(int t) { return (t * 2654435761u >> 13) & 1; }

// Advance simulation time to `until`, letting every scheduled gate delay fire on the way.
static void advance_to(VerilatedContext& ctx, Vasync_fifo& dut, uint64_t until) {
  while (ctx.time() < until) {
    uint64_t next = until;
    if (dut.eventsPending() && dut.nextTimeSlot() < next) next = dut.nextTimeSlot();
    ctx.time(next);
    dut.eval();
  }
  dut.eval();
}

static bool run(const Scenario& sc) {
  VerilatedContext ctx;                       // a fresh context per scenario: time starts at 0
  Vasync_fifo dut{&ctx};
  std::deque<int> inflight;
  std::vector<int> enq, deq;
  int pw = 0, pr = 0, maxOcc = 0;
  int prev_full = 0, prev_empty = 1, prev_rdata = 0;
  bool order_ok = true, depth_ok = true;

  for (int t = 0; t < sc.steps; t++) {
    // The clear is released at CLEAR_RELEASE and the theorem wants the first edge no earlier
    // than R = 17, so the clocks are held low through the reset.
    const int START = 24;
    int wclk = (t >= START) && ((t % sc.wper) >= sc.wph);
    int rclk = (t >= START) && ((t % sc.rper) >= sc.rph);
    // The theorem assumes InOK S with S = 17: the inputs must be stable for 17 instants before
    // an edge.  So they change once per clock period, at the period boundary, which is half a
    // period before the edge -- not every instant, which would drive the circuit outside the
    // regime the refinement is about.
    int wcyc = t / sc.wper, rcyc = t / sc.rper;
    int winc = (t < sc.wstop) && (bit_of(wcyc + 7) || bit_of(wcyc + 11));
    int rinc = bit_of(rcyc + 3) || bit_of(rcyc + 5);
    int wrise = wclk && !pw, rrise = rclk && !pr;
    // The decision at an edge uses the state settled before it: the flags sampled at the end of
    // the previous instant, while the clock was still low.
    if (wrise && winc && !prev_full) { inflight.push_back(bit_of(wcyc)); enq.push_back(bit_of(wcyc)); }
    if (rrise && rinc && !prev_empty) {
      int got = prev_rdata;
      if (inflight.empty()) order_ok = false;
      else { if (got != inflight.front()) order_ok = false; inflight.pop_front(); }
      deq.push_back(got);
    }
    if ((int)inflight.size() > maxOcc) maxOcc = (int)inflight.size();
    if ((int)inflight.size() > 4) depth_ok = false;

    dut.winc = winc; dut.rinc = rinc; dut.wdata = bit_of(wcyc);
    dut.wclk = wclk; dut.rclk = rclk;
    advance_to(ctx, dut, (uint64_t)t + 1);       // exactly one instant of the Lean timeline
    prev_full = dut.full; prev_empty = dut.empty; prev_rdata = dut.rdata;
    pw = wclk; pr = rclk;
  }

  bool live = deq.size() >= 4;
  bool ok = order_ok && depth_ok && live;
  printf("%-44s enq=%zu deq=%zu maxOcc=%d  %s%s%s%s\n", sc.name, enq.size(), deq.size(), maxOcc,
         ok ? "PASS" : "FAIL", order_ok ? "" : " [order]", depth_ok ? "" : " [depth]",
         live ? "" : " [no data moved]");
  return ok;
}

int main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);
  Scenario scs[] = {
    // Periods are comfortably above the theorem's budget: P >= 22, and half a period >= S = 17.
    {"slow writer, fast reader (w=48, r=40)",  48, 24, 40, 20, 100000, 6000},
    {"fast writer, slow reader (w=40, r=48)",  40, 20, 48, 24, 100000, 6000},
    {"equal rates (w=44, r=44)",               44, 22, 44, 22, 100000, 6000},
    {"writer stops halfway, reader drains",    40, 20, 44, 22,   3000, 6000},
  };
  bool all = true;
  for (auto& sc : scs) all &= run(sc);
  printf("%s\n", all ? "async_fifo: all scenarios pass" : "async_fifo: FAILURES");
  return all ? 0 : 1;
}
