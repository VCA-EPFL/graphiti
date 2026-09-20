/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Gray
import Graphiti.Projects.AsyncFifo.Streams
import Graphiti.Projects.AsyncFifo.Spec
import Graphiti.Projects.AsyncFifo.Domains
import Graphiti.Projects.AsyncFifo.Filtered
import Graphiti.Projects.AsyncFifo.Invariant
import Graphiti.Projects.AsyncFifo.Modules
import Graphiti.Projects.AsyncFifo.Refinement
import Graphiti.Projects.AsyncFifo.Example
import Graphiti.Projects.AsyncFifo.Verilog
import Graphiti.Projects.AsyncFifo.VerilogGates
import Graphiti.Projects.AsyncFifo.Timed
import Graphiti.Projects.AsyncFifo.TimedProof
import Graphiti.Projects.AsyncFifo.TimedRefinement
import Graphiti.Projects.AsyncFifo.TimedProofR
import Graphiti.Projects.AsyncFifo.TimedRefinementR
import Graphiti.Projects.AsyncFifo.DomainsRefine
import Graphiti.Projects.AsyncFifo.Lifting
import Graphiti.Projects.AsyncFifo.Gates
import Graphiti.Projects.AsyncFifo.GateNext
import Graphiti.Projects.AsyncFifo.GateNextR
import Graphiti.Projects.AsyncFifo.GateLifting
import Graphiti.Projects.AsyncFifo.GateLiftingR
import Graphiti.Projects.AsyncFifo.Dff
import Graphiti.Projects.AsyncFifo.DffTiming
import Graphiti.Projects.AsyncFifo.BusReg
import Graphiti.Projects.AsyncFifo.BusRegTiming
import Graphiti.Projects.AsyncFifo.StReg
import Graphiti.Projects.AsyncFifo.StRegR
import Graphiti.Projects.AsyncFifo.StRegTiming
import Graphiti.Projects.AsyncFifo.StRegRTiming
import Graphiti.Projects.AsyncFifo.EnReg
import Graphiti.Projects.AsyncFifo.EnRegTiming
import Graphiti.Projects.AsyncFifo.Mem
import Graphiti.Projects.AsyncFifo.Bank
import Graphiti.Projects.AsyncFifo.BankR
import Graphiti.Projects.AsyncFifo.GateBank
import Graphiti.Projects.AsyncFifo.GateBankR
import Graphiti.Projects.AsyncFifo.ReadMux
import Graphiti.Projects.AsyncFifo.GateRead
import Graphiti.Projects.AsyncFifo.GateRegs
import Graphiti.Projects.AsyncFifo.GateSync
import Graphiti.Projects.AsyncFifo.Sync
import Graphiti.Projects.AsyncFifo.Metastability
import Graphiti.Projects.AsyncFifo.SyncSettle
import Graphiti.Projects.AsyncFifo.SyncStage

/-!
# A verified asynchronous FIFO in Graphiti

This project applies the methodology of Emily Kobler's report on loopy combinational
circuits (signals as lists ordered by prefix, blocks as Graphiti modules that store their
inputs, correctness by refinement, timing assumptions as filters in the specification) to a
*sequential* circuit with two clock domains: the classic Gray-code asynchronous FIFO
(Cummings' design).

The development is layered.  At the register level (`Modules.lean`) the two clock domains are
Moore machines; their outputs are exact streams.  At the *filtered* level the domains only
promise their outputs outside clk-to-q windows (`kq`) and while their clock (`P`) and inputs
(`S`) respect the timing assumptions — the report's style: the model stays total and the
specification says nothing after a violation.  At the *timed* level (`Timed.lean`) the write
domain is a graph of blocks with delay windows, setup times and a metastable synchroniser stage.
Finally, at the *gate* level both clock domains' logic and their whole state are netlists of
unit-delay gates: the next-state logic (`GateNext.lean`, `GateNextR.lean`), and every stateful
block --- the flip-flop (`Dff.lean`), the registers built from it (`BusReg.lean`, `StReg.lean`,
`StRegR.lean`), the memory cell (`EnReg.lean`), the register file (`Mem.lean`) and the banks
that hold them (`Bank.lean`, `BankR.lean`) --- each against the contract `Timed.lean` states
for it.  `GateLiftingR.asyncFifoGatesRW_refines` is the whole FIFO, both domains as gates,
against `fifoSpec`.

Two blocks stay above the gate level, each for a stated reason.  The synchroniser's first stage
is the subject of `Metastability.lean`, below.  The read port is combinational, but its input
is the write domain's memory as a *function*-valued stream, so a netlist for it would first ask
for that wire to be unpacked into bits; its delay window `rdly` is threaded through the proof
(`Filtered.MemHold`, `TimedProofR.rdata_correct`) and is what the read clock must accommodate
on top of its clk-to-q.

One assumption stays an assumption, and `Metastability.lean` says why.  The synchroniser's
first stage is a netlist like any other --- `Sync.lean` builds it and proves `sync_refines`
about it --- but it samples a bus from the other clock domain, so nothing is known about its
setup window, and `dff_metastable` exhibits a clean clock, a released clear and a data stream
glitching inside the aperture for which the netlist **oscillates for ever**: the cross-coupled
pair sits at its balance point and a deterministic discrete model has no noise to push it off.
So `syncNetlist ⊑ Timed.syncReg` is not unproved but false, and the fault is the model's: a
real stage resolves after a random time with an exponentially decaying tail, which is an MTBF
argument and not a Boolean one (a device that always decided within a bounded time would be a
bounded-time arbiter).  `Timed.syncReg`, whose capture and whose output during settling are
read off an oracle, is therefore where this development *writes the assumption down* --- though
it is no longer a primitive of the circuit: `GateSync.lean` replaces it by three one-bit
flip-flops, so the assumption is written down per bit (`SyncStage.settleOut1_settleOut`).  The *second* stage needs no such treatment: its
data is `syncOut`, stable from `stl` instants after an edge, so it meets an ordinary aperture
and lives in the register bank, as gates.

`SyncSettle.lean` reduces that assumption to its smallest form.  `syncReg` grants two freedoms
at *bus* granularity --- which bits of a sample resolved to the new value, and what is seen
while the stage settles --- and `settle_orc` shows both are computed, not assumed: three bits
each meeting `Timed.SettleOut` (one clause about one bit: from `stl` instants after an edge the
bit does not move, and it is one of the two values the wire showed at the ends of the aperture)
pack into exactly `syncOut`, for an oracle read off those bits.  `stage_settles_of_aperture`
then closes the circle: that per-bit clause is a *theorem* for our flip-flop wherever its data
is stable over the aperture (`Dff.dffOut_settleOut`).  So what is assumed, in the end, is one
hypothesis about one bit of one register --- that the first stage's data meets its aperture ---
and nothing else.

The clear is threaded, and the way it is threaded is the shape of the whole argument.  A netlist
of gates has no defined state until something puts it there, so `Timed.regBank` has a `clrn`
port the register level did not, fed by a `clearSrc` node *inside* the write domain --- the
domain's interface is the one it always had.  And what the bank promises is guarded: its
contracts (`RegOutG`, `BusRegOutG`, `MemOutG`) bind at an instant only where the clock and the
clear have behaved up to that instant (`GateOK P pw Rr Rc`).  That is the same discipline as the
domains' own relations, per instant and never over a whole run, so a block is still right at
every instant before a violation.  `Timed.RegAt`, `BusWinAt` and `MemAt` are the per-instant
clauses the guarded and unguarded contracts share, and `TimedRefinement.Psi.gate_of` is the one
place where the netlist's extra filters are discharged from the domain's.

`Bank.lean` delivers them in that form (`bank_stG`, `bank_grayG`, `bank_memG`)
and the passage from its block-wide theorems is one idea: a netlist is causal, so to read a
contract at `t` one applies the whole-history theorem to the inputs **cut at `t`** --- the cut
circuit computes the same value there, and the filters over the cut history are exactly the
filters before `t`.  For that to work every block must report exactly one instant past its own
inputs, which is why `Mem.memOut` reports against the file's inputs rather than against its
cells: the packer sees only cells, whose enables the decoder carries up to three instants
further, so on its own it has to subtract that depth and would then fall short of `t` after the
cut.  Read against the file's inputs the bound is exact (`W_en_length_le`, `memLen_le_enLen`).

`GateBank.lean` makes the bank a block of the timed write domain, and one thing had to be put
right first.  A block can only ever claim a *prefix* of what it computes --- its own nodes hold
prefixes of what drives them --- so `v <+: stOut …` is all a register's specification can say,
and that phrasing keeps no record of which prefix was said: the abstraction permits reporting
less later than before.  The circuit never does that (its wires only grow); the abstraction had
simply forgotten.  So each register, the register file and the bank now *record what they have
reported* and only extend it, which is where that fact belongs --- at the block that earns it
--- and `Timed.regBank`'s outputs are then met directly.  With that, `GateLifting.wdomGates` is
the write domain with **both** its next-state logic and its whole state as netlists, and the
only block of it that is not gates is `Timed.syncReg`.

The **read domain** is now timed too (`Timed.rdomTimed`, `TimedProofR.lean`,
`TimedRefinementR.lean`, `Lifting.asyncFifoTimedR_refines`): the same four blocks as the write
domain and one more, the read port.  Two things there are its own.  `empty` powers up *high* ---
a FIFO starts empty --- so `RSt`'s `default` has `empty := true`, which a bank of flip-flops
cleared to low cannot show: the gate-level bank will store the complement and invert on the way
out, one inverter and no new ports (Cummings puts an asynchronous preset on that one flip-flop
instead).  And a memory read port is not a combinational block over a bus: `CombOut` over the
array would demand the *whole memory* stand still over the block's window, when a write to any
other entry is invisible to a read port.  `Timed.ReadOut` is its contract --- what must hold over
the window is the address and *the word that address selects*.

What is left: the read domain's gate level, and the read port's window.  That window is the one
place a read-domain block depends on the *other* domain's timing, so opening it belongs in
`Invariant.lean` beside `mem_read`, whose margin `e < t - P_r - lat - 1` should give it directly.
The results, all with standard axioms and no `sorry`:

    Lifting.asyncFifo_refines :
      su < P_w → su < P_r → stl < P_w → stl < P_r →
      [e| asyncFifoLowered, (env α n lat stl su).find? ] ⊑ fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r

    Lifting.asyncFifoTimed_refines :
      kq + su + dmax + 2 ≤ P_w → stl + su + dmax + 2 ≤ P_w → su + dmax + 1 ≤ S_w →
      dmin ≤ dmax → dmax + su + 1 ≤ R_w →
      kq + su < P_w → kq + su < P_r → stl < P_w → stl < P_r →
      asyncFifoTimed α n lat stl su kq P_r S_r R_r pw_r dmin dmax ⊑ fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r

    Lifting.asyncFifoTimedR_refines :
      the same, with the read domain timed as well (its own delay window and filters)

    GateLifting.asyncFifoGates_refines :
      6 ≤ Rc → 22 ≤ P_w → stl + 18 ≤ P_w → 17 ≤ S_w → 17 ≤ R_w →
      12 ≤ P_w → 3 ≤ pw_w → Rc + 3 ≤ R_w → 12 < P_r → stl < P_w → stl < P_r →
      asyncFifoGates lat stl P_r S_r R_r pw_r Rc ⊑ fifoSpec Bool P_w P_r S_w S_r R_w R_r pw_w pw_r
      -- the write domain here is gates throughout: its next-state logic and its whole state

    Dff.dff_refines       : dffNetlist ⊑ dffSpec      -- seven gates, with the clear
    Dff.dffOut_regOut     : … → RegOut 4 1 false clk … (dffOut clk d crn)
    Dff.dffOut_window     : … → the output is glitch-free across an edge
    BusReg.reg_refines    : busNetlist ⊑ busSpec      -- three flip-flops, the Gray pointer
    BusReg.busOut_busRegOut : … → BusRegOut 4 1 clk …
    StReg.reg_refines     : stNetlist ⊑ stSpec        -- seven flip-flops, the state record
    StReg.stOut_regOut    : … → RegOut 4 1 default clk …
    EnReg.en_refines      : enNetlist ⊑ enSpec        -- a cell: flip-flop and multiplexer
    EnReg.cell_value      : … → low until the first write, then the last write's data
    Mem.mem_refines       : memNetlist ⊑ memSpec      -- decoder and four cells
    Mem.memOut_memOut     : … → MemOut 4 8 clk we addr data …
    Bank.bank_refines     : bankNetlist ⊑ bankSpec    -- the three blocks, over the bus
    Bank.bank_st/gray/mem : the output relations of `Timed.regBank`; the `full` flag is a
                            projection of the state, so `GateBank` reads it off `bank_st`
    Bank.bank_stG/grayG/memG : the same, per instant --- exactly what `regBank` asks
    GateBank.bank_refines_regBank : 6 ≤ Rc → bankNetlist ⊑ Timed.regBank Bool 4 8 12 3 (Rc+3) Rc
    BankR.bank_refines    : the read domain's bank, two registers, no register file
    GateBankR.bank_refines_rregBank : 6 ≤ Rc → bankNetlist ⊑ Timed.rregBank 4 8 12 3 (Rc+3) Rc
    GateNextR.gateNextR_refines : gateNextR ⊑ Timed.rnextBlock 0 8
    Sync.sync_refines     : syncNetlist ⊑ syncSpec    -- the two synchroniser stages
    Dff.dff_metastable    : with the data glitching in the aperture, the output never settles
    Dff.dff_metastable_whole_period : … and not before the next edge, a whole clock period
    Dff.dffOut_settleOut  : the netlist *is* a `Timed.settlingDff` wherever its data is stable
                            over the aperture --- so that hypothesis is the whole assumption
    SyncSettle.settle_orc : three bits meeting `SettleOut` ARE a `Timed.syncReg` --- the oracle
                            is computed from them, so the bus-level assumption is the per-bit one
    SyncSettle.stage_settles_of_aperture : and that per-bit clause is a theorem wherever the
                            aperture holds, so the assumption is exactly the aperture failing
    GateSync.stage_refines : stageNetlist lat su stl ⊑ Timed.syncReg lat su stl --- so `syncReg`
                            is a netlist too, and nothing in the circuit is a bus-level primitive

built from `Refinement.refinesF` (the circuit over filtered domains refines the specification
when `kq + su < P` and `stl < P` for both clocks), `TimedRefinement.wdomTimed_refines` (the
timed write domain refines the filtered one under the delay constraints),
`GateNext.gateNext_refines` (the netlist refines the timed next-state block with delay window
`[0, 8]`), the exact-to-filtered refinements of `DomainsRefine.lean`, and the graph-level
lifting of `Lifting.lean`, `GateLifting.lean` and `GateLiftingR.lean`.

## Files

* `Gray.lean` — the Gray code on `BitVec`, its inverse, and the key lemma that a per-bit
  mixture of two consecutive Gray codes is one of them (`gray_succ_choice`).
* `Streams.lean` — streams, the prefix order, Moore machines over streams, event lists.
* `Spec.lean` — the specification `FifoOK P_w P_r S_w S_r R_w R_r`: at every instant up to which both
  clocks have respected their minimum periods and the synchronous inputs their setup windows,
  the dequeued values are a prefix of the enqueued values.  Prefix-closed (`FifoOK.mono`).
* `Domains.lean` — the write and read clock domains as Moore machines with an explicit timing
  model of the crossing (`lat`, `stl`, `su`, oracle streams), and the machine-level invariants.
* `Filtered.lean` — the relaxed output relations of the domains (`WGrayF`, `WFullF`, `WMemF`,
  `RGrayF`, `REmptyF`, `RDataF`): filters, clk-to-q windows with glitch-free bits, memory
  write windows; monotone and prefix-closed, satisfied by the exact outputs.
* `Invariant.lean` — the global invariant and the temporal theorem `fifo_correctF` against
  relaxed wires (`sample_choice`: what a sampler sees through a wire inside the windows is
  the Gray code of a count within the window), and the exact `fifo_correct` as the case
  `kq = 0`.
* `Modules.lean` — the Graphiti modules (exact and filtered domains, oracles, the
  specification), the circuit `[graphEnv| … ]`, and its reductions with `def_module`.
* `Refinement.lean` — the simulation relation and `refinesF : asyncFifoF ⊑ fifoSpec`.
* `Timed.lean` — the timed RTL components (`CombOut` with delay window and stability
  filter, `RegOut`/`BusRegOut` with clk-to-q window and setup, `MemOut`, the metastable
  `syncOut`), their monotonicity, and the write domain rebuilt from them (`wdomTimed`).
  Blocks with nondeterministic outputs remember what they emitted.  The register contracts are
  shaped after Kobler's filtered flip-flop theorem (`CombinationalStream.lean`, clk-to-q 4,
  setup 2); `DffTiming.lean` discharges them for our own flip-flop, at clk-to-q 3 and setup 1.
* `TimedProof.lean` — the delay analysis: `edge_value` and `st_correct` relate the streams
  between the timed blocks to the register-level machine; `full_correct`, `gray_correct`,
  `mem_correct` derive the relaxed relations.
* `TimedRefinement.lean` — `wdomTimed_refines : wdomTimed ⊑ writeDomainF`.
* `DomainsRefine.lean` — `writeDomain ⊑ writeDomainF`, `readDomain ⊑ readDomainF`.
* `Lifting.lean` — `ExprLow.refines_env` (componentwise refinement across environments of the
  same lowered graph), the timed circuit `asyncFifoTimed`, and the two end-to-end theorems.
* `Gates.lean` — unit-delay gates and forks as Graphiti modules, in Kobler's convention: a gate
  emits one instant past its inputs, since its output at `t` is its function of the inputs at
  `t - 1`.  That instant is what lets a stream enter a feedback loop; a gate that truncated to
  its shortest input would be sound and useless, and every cycle of such a netlist would be
  dead.  Also the wire contract `Comb` (logic depth window, composed gate by gate), the
  boundary adapter `cut3` (what a block *reports*, as opposed to what its gates compute), and
  arithmetic helpers on stream lengths.
* `GateNext.lean` — the write domain's next-state logic for
  depth 4 and 1-bit data as a netlist of 16 gates, 9 forks and two bus adapters, and
  `gateNext_refines : gateNext ⊑ nextBlock Bool 0 8` (delay window `[0, 8]`; the functional
  identity is checked by the kernel over all input bits).
* `GateNextR.lean` — the same for the read domain, which is
  the write domain's netlist minus the memory command (no data, no write enable, no address) and
  with one gate changed: the write side compares its pointer with `ungray q2 + 2^n`, whose top
  bit is the complement of `q2`'s, so its top comparison is an XOR, while the read side compares
  with `ungray q2` and uses three XNORs.  Dropping the memory command costs one thing: the write
  netlist's `we` output is one gate from `inc`, so its packer never runs more than an instant
  ahead of `inc`, whereas here `inc` reaches the record through the enable and a half-adder.  So
  the packer takes the block's own `st`, `inc` and `q1` as reference streams and truncates to
  them --- the boundary cut of `Gates.cut3`, folded into the packer because the bus is a record.
  `gateNextR_refines : gateNextR ⊑ rnextBlock 0 8`.
* `GateRegs.lean` — the composition of the storage
  netlists.  Every storage element is proved twice — as a contract (`Dff.dffSpec`, `EnReg.enSpec`,
  `BusReg.busSpec`, `StReg.stSpec`, `Mem.memSpec`) and as a netlist of gates refining it — but the
  graphs above them name the *contracts*, so the netlists were proved without being composed into
  anything.  This file does the composition bottom up, six `ExprLow.refines_env` steps, ending in
  `bankG_refines` and `bankRG_refines`: the two register banks with every flip-flop, every memory
  cell and every bus expanded to gates.  `GateLifting`/`GateLiftingR` then give the domains those
  banks, so the main theorem's leaves are gates, wiring, `Timed.clearSrc` (the reset source, which
  is environment rather than hardware) and `SyncStage.settlingDffO`.
* `GateSync.lean` — `stage_refines`, the synchroniser
  stage of `SyncStage.lean` (three `settlingDffO`, a fork, the two projections and a packer)
  refining `Timed.syncReg`.  `SyncStage.syncOut_pack` is what makes it go through: the bus-level
  stream *is* the three bits packed, so the output claim is monotonicity of one bit, three times.
  With it, `wenvG` and `renvG` give the sync node a netlist like every other node.
* `GateLifting.lean` — the netlists plugged into the write domain and the FIFO:
  `asyncFifoGates_refines`.
* `GateLiftingR.lean` — the same for the read domain (`rdomGates_refines_timed`), and the FIFO
  with *both* domains as gates: `asyncFifoGatesRW_refines`.
* `Dff.lean` — the edge-triggered D flip-flop with asynchronous
  clear as a netlist of thirteen nodes, the six-bit automaton that solves its feedback loops,
  and `dff_refines : dffNetlist ⊑ dffSpec`.  The invariant is structural — each node holds a
  prefix of what drives it — and the correspondence with the automaton is derived from it by one
  induction, which is what makes a growth of the inputs free.  The clear is not decoration: every wire of a
  netlist of these gates is low at instant `0`, and from the all-low state the cross-coupled
  pair oscillates for ever, so without a clear the flip-flop never holds a defined value.  The
  clear also gates the output (`q = and n5 clrn`), which costs one instant of clk-to-q and buys
  a defined output from instant `0` — otherwise the output NAND reads `true` at instant `1`,
  whatever the circuit, and `RegOut` would be unsatisfiable by any netlist of these gates.
* `BusReg.lean` — three flip-flops as the three-bit Gray
  pointer register, with the bus split into bits on the way in and reassembled on the way out
  (`bus_refines`).  The flip-flops appear as the block they refine, not as their netlists;
  substituting the netlists is `ExprLow.refines_env`'s job, once, at the top.
* `StRegR.lean` / `StRegRTiming.lean` — the read domain's seven-bit state register, the same
  table at the read domain's record.  One bit is not the flag itself: a flip-flop clears to
  `false` and a FIFO powers up *empty*, so the register stores `!empty` and `stBit_all` puts it
  back the right way up.  The bank then needs no set-reset flip-flop and no inverted clear.
* `BankR.lean` / `GateBankR.lean` — the read domain's register bank: `Bank.lean` without the
  register file, three output ports instead of four.
* `BusRegTiming.lean` — the bus contracts from the bit ones: `busOut_regOut` (`RegOut` at
  clk-to-q 4, setup 1) and `busOut_busRegOut` (the glitch-free window of `BusRegOut`, which is
  what a Gray-coded pointer needs to cross clock domains).  A bus is its bits: each clause is
  the per-bit clause assembled by `bv3`.
* `StReg.lean`, `StRegTiming.lean` — the same, seven flip-flops wide, for the write domain's
  state record (`WSt 2`: pointer, `full`, second synchroniser stage).  Generated from the same
  table as `BusReg.lean`; a record is its bits, so `RegOut` for it is the seven bit contracts
  assembled by `stBit_all`.
* `EnReg.lean` — one cell of the register file, a flip-flop
  whose `d` input comes from a multiplexer reading the flip-flop's own output (`en_refines`).
  That loop is why the cell is a netlist of eleven gates with its own automaton rather than a
  graph of blocks: a block's output is a function of the streams it was *given*, and here the
  flip-flop is given a stream that depends on what it produces.  Nothing is lost — the six
  flip-flop wires of `enRun` are `dffRun` driven by the multiplexer's stream — and the clock
  gating that would avoid the loop would need the enable stable over the clock's whole high
  phase, which the write side does not promise.
* `EnRegTiming.lean` — the cell's contract.  `enRun_ff` takes the cell's automaton apart again:
  its six flip-flop wires are `dffRun` driven by the multiplexer's stream, so the flip-flop's
  theorems apply with `d := mStream`, and what is left is what the multiplexer does.  It is two
  gates deep, so the cell's setup window (`5`) is wider than the flip-flop's (`1`), and the
  clock must be slow enough (`ClockOK 12`) that the cell's own output has settled before the
  next edge reaches the multiplexer.  `cell_value` closes the loop by induction along the
  stream: low until the first write, then the data of the last write, held across the
  non-writing edges — including inside the clock-to-q window, where the glitch-free clause is
  what rules out a third value.
* `Mem.lean` — the register file: an address decoder (two inverters, four matches, four write
  enables) and four cells of `EnReg.lean`.  Nothing here has feedback — the loop of a memory
  lives inside the cell — so the cells are the blocks they were proved to refine.  `W_en_getD`
  is the decoder's side of the argument: three gates deep, so at an edge whose enable and
  address were stable it shows exactly "this entry is being written".
* `Bank.lean` — the write domain's register bank: the seven-bit state register, the three-bit
  Gray pointer, the `full` bit and the register file, over the fields of the next-state bus
  (`bank_refines`).  `bank_st`, `bank_gray`, `bank_mem` read the blocks' contracts back in the
  bank's terms — they are the output relations of `Timed.regBank`, and the `full` flag needs no
  relation of its own because it is a projection of the state register.  The bank has one port
  the register-level model does not: the clear.
* `Sync.lean` — the two-flip-flop synchroniser, two `BusReg` stages in series
  (`sync_refines`).  It is deliberately *not* related to `Timed.syncReg`: see
  `Metastability.lean`.
* `Metastability.lean` — the boundary of the gate level.  `dff_metastable` is one concrete run
  of the flip-flop of `Dff.lean` — a clean clock (`clkM_filters`: `ClearOK 2`, `ResetOK 5`,
  `PulseOK 3`), a released clear, and data with a one-instant pulse inside the aperture
  `[e-2, e]` — whose output alternates at every instant from the end of the clock-to-q window
  onwards and never settles, while the same run with the data settled before the aperture
  (`dff_settles`) gives the captured value.  So the first synchroniser stage's correctness is
  not a property of its netlist; it stays the oracle-driven `Timed.syncReg`.
* `DffTiming.lean` — what that automaton does in time: `dffOut_regOut` (`Timed.lean`'s `RegOut`
  as written there, clk-to-q 4, setup 1), `dffOut_window` (glitch-free across an edge: the
  one-bit case of `BusRegOut`), `settled_at`.  One filter is new at this level: `PulseOK 3`,
  pulses at least three instants wide — `ClockOK P` only keeps edges apart, which a netlist's
  loops do not care about.
* `gen/memprobe.py` — profiles a Lean file declaration by declaration under a memory cap.  It
  is a debugging tool; nothing in the development is generated.
* `Example.lean` — the register-level model is executable; four concrete traces are checked
  with `#guard`, including one where the read clock is too fast for the settling time and the
  FIFO does misbehave.
* `Verilog.lean` — export to Verilog through the framework's template netlister, with a small
  extension declaring internal nets with their widths, and a second exporter that walks a
  lowered expression (`build_verilog_of_exprLow`), used to emit the write domain's next-state
  gate netlist on its own (`gateNextVerilog`).
* `VerilogGates.lean` — **the whole FIFO as gate-level Verilog** (`asyncFifoGates`).  Fifteen
  modules, each generated from the very `ExprLow` a refinement theorem is about, wired in the
  proof's own hierarchy: `dff` and `enreg` from gates, `busreg`/`streg` from `dff`, `mem` from
  `enreg`, `bank`/`bankr` from those, `sync_stage` from `settling_dff`, then `wdom`, `rdom` and
  `async_fifo`.  Verilator lints it clean and yosys maps it to 246 gates, of which the only
  sequential primitives are the six `settling_dff` cells — every ordinary flip-flop is gates.
  The cells that are not hardware are called out as such: `settling_dff` carries the
  metastability assumption, `clear_src` and `oracle` model the environment.  `verilog/` holds
  the Makefile and a Verilator testbench checking the exported next-state netlist against
  `wNext` on all 4096 input combinations.  A register-level export with hand-written
  clock-domain bodies used to live in `Verilog.lean`; it was removed once this covered the whole
  design, so `verilog/tb.cpp` and `expected.txt` are now orphaned (they drive 8-bit data, which
  the verified design does not have).

## The circuit

The write domain holds an `(n+1)`-bit binary write pointer, the `full` flag, the memory and
a two-stage synchroniser for the Gray-coded read pointer.  The read domain holds the read
pointer, the `empty` flag and a two-stage synchroniser for the Gray-coded write pointer.
Read data is the memory word at the read address (first-word-fall-through).  Each domain
is a Moore machine over global discrete time: at a rising edge of its clock the whole
register state is updated, and the outputs at instant `t` are functions of the state
before the edge at `t`.  Consequently an output stream is one element longer than the
shortest input stream; this "delay" is what lets information flow around the loop
`write domain → read domain → write domain` — with combinational (same-length) outputs the
composed circuit would never produce anything, which is the report's observation about loops
made concrete.

## The timing model

The crossing is described by explicit parameters.  With wire latency `lat`, a synchroniser
edge at instant `t` samples the value the other domain produced at `t - lat`, and its bits
resolve between that value and the one `su + 1` instants earlier (the sampler's setup window).
Because the bus may be changing, each bit resolves independently to its old or its new value
(metastability), and for `stl` instants after the edge the first stage's output is
unpredictable; the second stage samples it at the next edge.  All of this nondeterminism is
made explicit through *oracle* streams (per instant: a selection mask and the unpredictable
value) produced by unconstrained oracle modules of the circuit, so the domains are
deterministic given their inputs and every theorem quantifies over every resolution.  The
register `since` (instants since the last edge) plays the role of the report's delay filter.
`Gray.gray_succ_choice` shows that a settled sample of a Gray-coded counter is always an
old or a new count, never garbage; this is where the Gray code does its work.

At the timed level the write domain's registers additionally have a clk-to-q window `kq`
(unconstrained, but glitch-free bit by bit, for `kq` instants after an edge) and a setup time
`su`, and its next-state logic a propagation delay in `[dmin, dmax]`.

## The specification and the proofs

The specification is a single module, parametrised by the clock periods `P_w`, `P_r`, the
input setup windows `S_w`, `S_r` and the reset times `R_w`, `R_r` it assumes, whose state is
the eight interface streams.  Inputs may only grow.  An output may be extended as long as
`FifoOK P_w P_r S_w S_r R_w R_r` holds: at every instant where all signals are known *and, so
far, both clocks have kept their edges at least a period apart, the synchronous inputs have
been stable before each edge, and no edge came before the reset time*, the dequeued values
form a prefix of the enqueued values.  The reset filter is what a gate-level implementation
needs: its outputs are low until its inputs have propagated, so the first edge must wait.  These assumptions are filters in the
sense of the report: the physical circuit cannot refuse a bad clock, the model stays total,
and the specification promises nothing from the first violation onwards.  Flags may be
conservative, as a real asynchronous FIFO's must be.

Because `FifoOK` is a prefix-closed relation rather than a filtered function, the
specification can always emit exactly the implementation's output, so no input buffers and
no speculation modules are needed.  The simulation relation of `Refinement.lean` has the
report's three groups of clauses: inputs agree, each wire is a prefix of the stream its driver
emitted, and the emitted streams satisfy their relaxed relations for the driver's current
inputs.  Input and internal transitions are discharged by monotonicity; output transitions
reduce to `fifo_correctF`, an induction over time with an invariant tying the pointers,
synchroniser registers, `since` counters, flags and memory to the numbers of values enqueued
and dequeued so far.  `kq + su < P` makes a sampling window (extended by the driver's clk-to-q
window) contain at most one edge of the driver, so a sample is a mixture of at most two
consecutive counts; `stl < P` makes the second stage always sample a settled first stage.

The timed write domain is handled once more by refinement (`TimedRefinement.lean`), with a
simulation relation that records the wiring between the blocks and each block's contract for
its current inputs, and a delay analysis (`TimedProof.lean`) showing by induction over the
edges that the bus loaded at every edge is stable over the setup window and equal to the
register-level next state.  The constraints are the expected ones: a period must fit
clk-to-q, the logic delay and a setup window, or the synchroniser's settling time, the logic
delay and a setup window; the inputs must be stable long enough before an edge for the logic
to have absorbed them.

## What is proved, and what is not

Proved: under the timing assumptions, no data is lost, duplicated, reordered, or read before
being written, for every data type, depth, latency, and every metastability resolution — for
the register-level circuit, and for the circuit whose write domain is built from timed blocks
with any window and delay parameters satisfying the constraints.  `Example.lean` shows the
hypotheses are not decorative: with a read clock period no larger than the settling time, the
register-level circuit reads values that were never written (and the specification, as
intended, says nothing about that trace).

The block contracts of `Timed.lean` are assumptions on the lower stages: a register that
settles within `kq` and, when it crosses clock domains, transitions bit by bit; a register file
that is correct only while its writes have respected their setup windows; combinational logic
that settles within `dmax` on stable inputs; a synchroniser stage that resolves within `stl`.
The last one is irreducibly an assumption (a boolean unit-delay gate model oscillates forever
in the metastable case); the others are meant to be discharged by gate-level refinements, the
register ones from Kobler's flip-flop theorem once it carries the glitch-free clause.

The Verilog export is not verified: the framework's exporter is purely syntactic and has no
semantics linking it to Lean.  Its two halves differ in how much they leave to inspection.  In
the register-level export the leaf bodies are hand-written behavioural code, so the whole
design is only as good as reading them.  The gate-level export is generated from
`GateNext.gateNextExpr`, the expression the refinement theorem is about, and its leaves are
gates whose bodies are one line each; a Verilator testbench checks it against `wNext` on all
4096 input combinations.  The timed blocks are relational, hence not executable; their
consistency is argued, not tested.

Not proved: any accuracy or liveness property of `full` and `empty` (bounds of the form "if
an element has been present since `t₀` then `empty` is low from `t₀ + lat + 2·P_r + 1`" are
the natural next theorems); the timed read domain (symmetric to the write domain); the
lower stages of the descent.
-/
