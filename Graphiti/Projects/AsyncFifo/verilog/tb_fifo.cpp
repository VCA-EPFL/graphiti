// Self-checking testbench for the gate-level export of the whole FIFO.
//
// The design under test is `async_fifo` from VerilogGates.lean: two clock domains of unit-delay
// gates, six `settling_dff` cells and nothing else sequential.  Data is one bit wide, as in the
// verified design, so a run is checked by the *sequence* of bits rather than by tagging items:
//
//   * every bit dequeued must be the next bit enqueued  (FIFO order, no corruption);
//   * the number of items in flight never exceeds the depth, 4;
//   * a run must actually move data, or the checks above would pass vacuously.
//
// Conventions follow the Lean model: at instant t the enqueue/dequeue decision uses the state
// before the edge at t, and a rising edge at t is clk(t)=1 with clk(t-1)=0.  Clock periods are
// kept above the theorem's budget (22) although Verilator collapses the unit delays.
#include "Vasync_fifo.h"
#include "verilated.h"
#include <cstdio>
#include <deque>
#include <vector>

static vluint64_t main_time = 0;
double sc_time_stamp() { return (double)main_time; }

struct Scenario { const char* name; int wper, wph, rper, rph, wstop, steps; };

// A cheap deterministic bit source, so runs are reproducible.
static int bit_of(int t) { return (t * 2654435761u >> 13) & 1; }

static bool run(const Scenario& sc) {
  Vasync_fifo dut;
  std::deque<int> inflight;
  std::vector<int> enq, deq;
  int pw = 0, pr = 0, maxOcc = 0;
  bool order_ok = true, depth_ok = true;

  for (int t = 0; t < sc.steps; t++) {
    main_time = t;
    int wclk = ((t % sc.wper) >= sc.wph), rclk = ((t % sc.rper) >= sc.rph);
    int winc = (t < sc.wstop) && (bit_of(t + 7) || bit_of(t + 11));
    int rinc = bit_of(t + 3) || bit_of(t + 5);
    dut.winc = winc; dut.rinc = rinc; dut.wdata = bit_of(t);
    dut.eval();                                   // settle on the new inputs, clocks unchanged

    int wrise = wclk && !pw, rrise = rclk && !pr;

    // The two clocks are independent, so their edges are applied in separate deltas: letting
    // them land together would make the synchroniser sample a pointer changing in the same
    // instant, a race the real circuit does not have and the Lean model does not describe.
    int accept = wrise && winc && !dut.full;      // `full` is registered in the write domain
    if (accept) { inflight.push_back(bit_of(t)); enq.push_back(bit_of(t)); }
    dut.wclk = wclk; dut.eval();

    int emit = rrise && rinc && !dut.empty;       // `empty` is registered in the read domain
    if (emit) {
      int got = dut.rdata;
      if (inflight.empty()) { order_ok = false; }
      else { if (got != inflight.front()) order_ok = false; inflight.pop_front(); }
      deq.push_back(got);
    }
    dut.rclk = rclk; dut.eval();

    if ((int)inflight.size() > maxOcc) maxOcc = (int)inflight.size();
    if ((int)inflight.size() > 4) depth_ok = false;
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
    {"slow writer, fast reader (w=34, r=24)",  34, 17, 24, 12, 100000, 4000},
    {"fast writer, slow reader (w=24, r=34)",  24, 12, 34, 17, 100000, 4000},
    {"equal rates (w=26, r=26)",               26, 13, 26, 13, 100000, 4000},
    {"writer stops halfway, reader drains",    24, 12, 30, 15,   2000, 4000},
  };
  bool all = true;
  for (auto& sc : scs) all &= run(sc);
  printf("%s\n", all ? "async_fifo: all scenarios pass" : "async_fifo: FAILURES");
  return all ? 0 : 1;
}
