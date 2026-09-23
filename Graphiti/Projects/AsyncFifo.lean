/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gray
import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.TopSpec
import Graphiti.Projects.AsyncFifo.TopGates
import Graphiti.Projects.AsyncFifo.components.level2.Domains
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Filtered
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Invariant
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Modules
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Refinement
import Graphiti.Projects.AsyncFifo.Evidence.Example
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Verilog
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.VerilogGates
import Graphiti.Projects.AsyncFifo.components.level3.Contracts
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.TimedProof
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.TimedRefinement
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.TimedProofR
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.TimedRefinementR
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Lifting
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteNext
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadNext
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteDomainGates
import Graphiti.Projects.AsyncFifo.TopSpec
import Graphiti.Projects.AsyncFifo.TopRefinement
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Dff
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.DffTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusReg
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusRegTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteState
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadState
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteStateTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadStateTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.EnReg
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.EnRegTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.RegFile
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteBank
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadBank
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteBankContract
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadBankContract
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadPort
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadPortContract
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncStageContract
import Graphiti.Projects.AsyncFifo.Evidence.Metastability
import Graphiti.Projects.AsyncFifo.Evidence.PlainSync
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncSettle
import Graphiti.Projects.AsyncFifo.components.level5.SyncStage
import Graphiti.Projects.AsyncFifo.ReadingSurface
import Graphiti.Projects.AsyncFifo.Architecture
import Graphiti.Projects.AsyncFifo.components.level6.WriteBank
import Graphiti.Projects.AsyncFifo.components.level6.ReadBank
import Graphiti.Projects.AsyncFifo.components.level4.WriteNext
import Graphiti.Projects.AsyncFifo.components.level4.ReadNext

/-!
# A verified asynchronous FIFO in Graphiti

This project applies the methodology of Emily Kobler's report on loopy combinational
circuits (signals as lists ordered by prefix, blocks as Graphiti modules that store their
inputs, correctness by refinement, timing assumptions as filters in the specification) to a
*sequential* circuit with two clock domains: the classic Gray-code asynchronous FIFO
(Cummings' design), down to unit-delay gates.

## What you have to read

* **`TopSpec.lean`** --- what the FIFO must do.  `FifoOK` is the property; `fifoSpec` is that
  property as a Graphiti module.
* **`components/levelN/`** --- the components, one file each.  Every component `X` has an
  implementation (`X.xImpl`: a graph whose nodes are the *specifications* of components one level
  down, or gates) and a specification (`X.xSpec`).  A component may only use components of a
  strictly lower level, and never another component's implementation.
* **`TopGates.lean`** --- the circuit the main theorem is about: each implementation with its
  children's specifications replaced by their gates (`X.gates`), bottom up, to
  `asyncFifoGates`.
* **`TopRefinement.lean`** --- the theorems: `X.impl_refines : X.xImpl ⊑ X.xSpec` for every
  component, and the main theorem `asyncFifoGates_refines : asyncFifoGates ⊑ fifoSpec`, which is
  the top layer's theorem with the two clock domains' gates substituted in.  A compiled instance
  shows its thirteen hypotheses can hold together.

Everything else is how it is proved (`ProofWriteOnly/`) or evidence that the assumptions are
honest (`Evidence/`).  Three things are checked by the build rather than asserted:

* `ReadingSurface.lean`: the statements of every theorem in `TopRefinement.lean` --- following
  every definition, never entering a proof --- mention nothing declared in `ProofWriteOnly/`; the
  component levels are a stratification; and no component uses another's implementation.
* `Architecture.lean`: `components/architecture.svg`, one box per component, one band per level,
  an arrow to each component it uses (transitively reduced), is regenerated from the code and
  the build fails if the checked-in `.dot` or `.svg` has drifted.

## The components

    level 0  Streams, Gray             signals, the prefix order, Moore machines; Gray codes
    level 1  Filters, Gates            the timing filters; unit-delay gates, forks, boundary cuts
    level 2  Domains                   the register-level machines the domains are specified by
    level 3  Contracts                 the timed contracts the block specifications are written in
             Dff                       dffImpl: seven gates          dffSpec: flip-flop with clear
             Oracle                    a source of arbitrary streams (metastability resolution)
    level 4  BusReg, WriteState,       registers of 3 and 7 flip-flops over dffSpec
             ReadState
             EnReg                     a memory cell: flip-flop behind a multiplexer
             WriteNext, ReadNext       next-state logic as gates     nextSpec: window [0, 8]
             ReadPort                  the read multiplexer as gates readSpec: window [3, 5]
    level 5  RegFile                   decoder and four cells over enSpec
             SyncStage                 three settling flip-flops     syncSpec: the first stage
    level 6  WriteBank, ReadBank       the registers (and the register file) over their specs
    level 7  WriteDomain, ReadDomain   bank, next-state logic, synchroniser (and read port)
                                       wdomSpec / rdomSpec: the register-level machine, filtered
    level 8  Fifo                      the two domains and two oracles  asyncFifoImpl / fifoSpec

The leaves of `asyncFifoGates` are gates, forks, wiring, the clear source `clearSrc` and the
oracle (the environment), and the settling flip-flop `SyncStage.settlingDffO` --- the one
primitive that is assumed rather than built, below.

## The circuit

The write domain holds an `(n+1)`-bit binary write pointer, the `full` flag, the memory and
a two-stage synchroniser for the Gray-coded read pointer.  The read domain holds the read
pointer, the `empty` flag and a two-stage synchroniser for the Gray-coded write pointer.
Read data is the memory word at the read address (first-word-fall-through).  Each domain
is a Moore machine over global discrete time: at a rising edge of its clock the whole
register state is updated, and the outputs at instant `t` are functions of the state
before the edge at `t`.  Consequently an output stream is one element longer than the
shortest input stream; this "delay" is what lets information flow around the loop
`write domain → read domain → write domain` --- with combinational (same-length) outputs the
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

Below the domains, blocks have a clk-to-q window `kq` (unconstrained, but glitch-free bit by bit
on a bus that crosses domains), a setup time `su`, and combinational logic a propagation delay
in `[dmin, dmax]`: the vocabulary of `components/level3/Contracts.lean`.

## The specification and the proofs

The specification is a single module, parametrised by the clock periods `P_w`, `P_r`, the
input setup windows `S_w`, `S_r`, the reset times `R_w`, `R_r` and the minimum pulse widths it
assumes, whose state is the interface streams.  Inputs may only grow.  An output may be extended
as long as `FifoOK` holds: at every instant where all signals are known *and, so far, both clocks
have respected their filters*, the dequeued values form a prefix of the enqueued values.  These
assumptions are filters in the sense of the report: the physical circuit cannot refuse a bad
clock, the model stays total, and the specification promises nothing from the first violation
onwards.  Flags may be conservative, as a real asynchronous FIFO's must be.

**The top layer** (`asyncFifoImpl_refines`, proved in `ProofWriteOnly/Refinement.lean`).  The
simulation relation has the report's three groups of clauses: inputs agree, each wire is a
prefix of the stream its driver emitted, and the emitted streams satisfy their domain's
specification for the driver's current inputs.  Output transitions reduce to `fifo_correctF`
(`ProofWriteOnly/Invariant.lean`), an induction over time with an invariant tying the pointers,
synchroniser registers, `since` counters, flags and memory to the numbers of values enqueued and
dequeued.  `kq + su < P` makes a sampling window contain at most one edge of the driver, so a
sample is a mixture of at most two consecutive counts; `stl < P` makes the second stage always
sample a settled first stage.

**The domains** (`wdomImpl_refines`, `rdomImpl_refines`; `ProofWriteOnly/TimedRefinement.lean`
and `…R.lean`, with the delay analyses `TimedProof.lean`, `TimedProofR.lean`).  The simulation
relation records the wiring between the blocks and each block's contract for its current inputs;
the delay analysis shows by induction over the edges that the bus loaded at every edge is stable
over the setup window and equal to the register-level next state.  A period must fit clk-to-q,
the logic delay and a setup window, or the synchroniser's settling time, the logic delay and a
setup window.

**The blocks** (`X.impl_refines` for the banks, registers, cells, next-state logic and read
port).  Each netlist proof is a structural invariant --- every wire holds a prefix of what
drives it (`ProofWriteOnly/NetlistWf.lean`) --- plus, for the stateful blocks, an automaton that
solves the feedback loop (`Dff.lean`, `EnReg.lean`) and timing lemmas (`…Timing.lean`) that
read the blocks' contracts off it.

**Substitution** (`ExprLow.refines_env`, `ProofWriteOnly/Lifting.lean`): a graph read in two
environments refines itself when every node does.  `StorageGates.lean`, `WriteDomainGates.lean`,
`ReadDomainGates.lean` and `FifoGates.lean` apply it bottom up to reach `asyncFifoGates`.

## Design notes

*The clear.*  A netlist of gates has no defined state until something puts it there
(`Dff.lean`: from the all-low state the flip-flop oscillates for ever), so each bank has a `clrn`
port the register-level machine did not, fed by a `clearSrc` node *inside* its domain --- the
domain's interface is the one it always had.  What the bank promises is guarded: its contracts
bind at an instant only where the clock and the clear have behaved up to that instant (`GateOK`).
`TimedRefinement.Psi.gate_of` is the one place where those extra filters are discharged from the
domain's.

*Reading a contract at one instant.*  A netlist is causal, so to read a contract at `t` one
applies the whole-history theorem to the inputs **cut at `t`**: the cut circuit computes the same
value there, and the filters over the cut history are exactly the filters before `t`.  For that
every block reports exactly one instant past its own inputs, which is why `RegFile.memOut`
reports against the file's inputs rather than its cells'.

*Reports only grow.*  A block can only claim a prefix of what it computes, and `v <+: out …` alone
keeps no record of which prefix was claimed.  So each register, the register file and the banks
record what they have reported and only extend it --- the circuit never does otherwise, its
wires only grow.

*The read domain's `empty`* powers up high, which flip-flops cleared to low cannot show: the
state register stores `!empty` and inverts it on the way out (`ReadState.lean`).

## The one assumption

The synchroniser's first stage samples a bus from the other clock domain, so nothing is known
about its setup window, and `Dff.dff_metastable` (`Evidence/Metastability.lean`) exhibits a clean
clock, a released clear and data glitching inside the aperture for which the seven-gate
flip-flop **oscillates for ever**.  In a deterministic discrete model there is no noise to push a
bistable off its balance point, so "the first stage settles" is not unproved but false of the
netlist (`Evidence/PlainSync.lean` builds the plain two-flip-flop synchroniser and states what
it does compute).  A real stage resolves after a random time with an exponentially decaying
tail --- an MTBF argument, not a Boolean one.

So it is assumed, in its smallest form: `SyncStage.settlingDffO`, one clause about one bit
(`Timed.SettleOut`: from `stl` instants after an edge the bit does not move, and it is one of the
two values the wire showed at the ends of the aperture), three per domain.  `SyncSettle.settle_orc`
shows the bus-level stage (`syncSpec`, whose oracle says which bits resolved) is exactly three
such bits, and `Dff.dffOut_settleOut` shows the clause is a *theorem* for the gate flip-flop
wherever its data meets the aperture --- so what is assumed is precisely the aperture failing,
and nothing else.  The second stage needs no such treatment: its data is stable from `stl`
instants after an edge, so it is an ordinary register of the bank, as gates.

## What is proved, and what is not

Proved, with standard axioms and no `sorry`: under the timing assumptions, the circuit of gates
(depth `4`, 1-bit data) never loses, duplicates, reorders, or invents data, for every
metastability resolution; and every component meets its specification, the domains and the top
layer for every data type, depth and latency.  `Evidence/Example.lean` shows the hypotheses are
not decorative: with a read clock period no larger than the settling time, the register-level
machine reads values that were never written.

The Verilog export (`ProofWriteOnly/VerilogGates.lean`, `verilog/`) is not verified: the
exporter is syntactic.  It is generated from the very expressions the theorems are about, its
leaves are one-line gates, and Verilator testbenches check it (the next-state netlists on all
4096 input combinations, the flip-flop against the Lean model instant by instant, the whole FIFO
across four clock ratios).

Not proved: any accuracy or liveness property of `full` and `empty` --- bounds of the form "if an
element has been present since `t₀` then `empty` is low from `t₀ + lat + 2·P_r + 1`" are the
natural next theorems.  Everything is a safety refinement: a circuit that never reported
anything would satisfy it.
-/
