/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.components.level2.Domains
import Graphiti.Projects.AsyncFifo.components.level1.Filters

/-!
# Contracts: what a timed block promises at one instant

The vocabulary the block specifications are written in.  Following Kobler's translation pattern
each block is a Graphiti module storing its input streams; input rules extend a stream
strictly; output rules emit a stream related to the stored inputs by one of these relations, and
extend the stream the block remembers having emitted.  What they add to her pattern is *timing*:

* `CombOut`: a combinational block with propagation delay in `[dmin, dmax]`.  Its output at
  instant `t` is `g` of the inputs at `t - dmax`, but only where the part of the inputs the block
  depends on (`dep`) has been constant over the whole window `[t - dmax, t - dmin]`.  Elsewhere
  the output is unconstrained: transients and glitches, and nothing at all during the first
  `dmax` instants (the specifications' reset filter keeps the clocks away from them).
  `ReadOut` is the same for a memory read port, which needs only the address and *the word it
  selects* held over the window, not the whole array.
* `RegAt kq su`: an edge-triggered register with clk-to-q window `kq` and setup `su`, at one
  instant.  After an edge at `e` whose data was stable over `[e - su - 1, e]`, the output is
  unconstrained for `kq` instants and equals the sampled data from `e + kq` until the next edge;
  after a violated edge nothing is promised until the next one.  This is the shape of Kobler's
  filtered flip-flop (delay filter, setup/hold filter).
* `BusWinAt`: what a register whose output crosses into another clock domain adds --- inside the
  clk-to-q window every bit is either the new bit or the bit shown at the edge (no glitches).
  `CleanEdges` is the side condition: every edge so far had stable data.
* `MemAt`: a register file, one such window per written entry, other entries untouched, and
  nothing promised once a write has violated its setup window (`WriteEdge`, `CleanWrites`).

`RegOutG`, `BusRegOutG` and `MemOutG` are those clauses over a whole stream, binding only at the
instants where a guard holds.  The guard a netlist of gates needs is `GateOK`: its clock pulses
wide enough for its internal loops to resolve, its clear released, no edge before that.  Like the
domain's own filters it is applied at each instant to the history *before* that instant, so a
block is still right at every instant before a violation.

Blocks with a nondeterministic output remember the stream they emitted and only ever extend it:
an output is a single physical history.  Every contract bounds the emitted stream by the horizon
of the block's inputs; a netlist of unit-delay gates computes further ahead than that, so a
gate-level block reports only what its inputs justify (`Gates.cut3`).
-/

namespace Graphiti.AsyncFifo.Contracts

/-- `x` is constant on the instants `a ≤ u ≤ b`, all of which are known. -/
def StableOn {κ : Type} (x : Nat → κ) (len a b : Nat) : Prop :=
  b < len ∧ ∀ u, a ≤ u → u ≤ b → x u = x b

/-- Output relation of a combinational block with delay window `[dmin, dmax]`, computing `g`
of the dependency cone `dep` of its inputs (`len` = number of known input instants). -/
def CombOut {κ ο : Type} [Inhabited ο] (dep : Nat → κ) (g : κ → ο) (len dmin dmax : Nat)
    (v : List ο) : Prop :=
  v.length ≤ len ∧
  ∀ t, dmax ≤ t → t < v.length → StableOn dep len (t - dmax) (t - dmin) →
    v.getD t default = g (dep (t - dmax))

/-- What an edge-triggered register promises at *one* instant: low until the first edge, and
the data the last settled edge saw once the clk-to-q window has passed. -/
def RegAt {β : Type} [Inhabited β] (kq su : Nat) (init : β) (clk : List Bool) (d : Nat → β) (dlen : Nat)
    (q : List β) (t : Nat) : Prop :=
  (NoEdge clk t → q.getD t default = init) ∧
  (∀ e, LastEdge clk e t → StableOn d dlen (e - su - 1) e → e + kq ≤ t → q.getD t default = d e)

/-- Every edge before `t` presented its data stable over the setup window.  This is to a
register what `CleanWrites` is to a register file, and a netlist needs it for the same reason:
an edge whose data moved may leave the circuit unsettled, and it will still be unsettled now.
The register's *value* clause does not need it --- a violated edge is forgotten at the next
clean one --- but the glitch-free clause does, because that one is about the circuit being
settled when the edge arrives. -/
def CleanEdges {β : Type} (clk : List Bool) (d : Nat → β) (dlen su t : Nat) : Prop :=
  ∀ e, e < t → riseAt clk e = true → StableOn d dlen (e - su - 1) e

/-- The glitch-free clause at one instant: inside the clk-to-q window every bit is the new bit
or the bit shown at the edge. -/
def BusWinAt {w : Nat} (kq su : Nat) (clk : List Bool) (d : Nat → BitVec w) (dlen : Nat)
    (q : List (BitVec w)) (t : Nat) : Prop :=
  CleanEdges clk d dlen su t → ∀ e, LastEdge clk e t → t < e + kq →
    ∀ i, (q.getD t 0#w).getLsbD i = (d e).getLsbD i ∨ (q.getD t 0#w).getLsbD i = (q.getD e 0#w).getLsbD i

/-- Output relation of an asynchronous memory **read port** with delay window `[dmin, dmax]`.

A read port is combinational, but not over a bus: it does not depend on the whole array.  What
it needs held over its window is the address, and the *word that address selects* --- a write to
any other entry is invisible to it, which is the point of having a memory rather than a
register.  `CombOut` over the array would demand the whole memory stand still. -/
def ReadOut {α : Type} [Inhabited α] {ι : Type} (dmin dmax : Nat) (addr : Nat → ι)
    (mem : Nat → ι → α) (len : Nat) (v : List α) : Prop :=
  v.length ≤ len ∧
  ∀ t, dmax ≤ t → t < v.length → StableOn addr len (t - dmax) (t - dmin) →
    (∀ u, t - dmax ≤ u → u ≤ t - dmin → mem u (addr (t - dmin)) = mem (t - dmin) (addr (t - dmin))) →
    v.getD t default = mem (t - dmin) (addr (t - dmin))

/-- Write event to entry `a` at edge `e`: an edge with write enable and this address, both
stable over the setup window. -/
def WriteEdge {ι α : Type} (a : ι) (clk : List Bool) (we : Nat → Bool) (addr : Nat → ι) (data : Nat → α)
    (dlen su e : Nat) : Prop :=
  riseAt clk e = true ∧ StableOn we dlen (e - su - 1) e ∧ StableOn addr dlen (e - su - 1) e ∧
  StableOn data dlen (e - su - 1) e ∧ we e = true ∧ addr e = a

/-- Every edge before `t` was clean for the register file: the write enable was stable over its
setup window, and so were the address and data when it was writing. -/
def CleanWrites {ι α : Type} (clk : List Bool) (we : Nat → Bool) (addr : Nat → ι) (data : Nat → α)
    (dlen su t : Nat) : Prop :=
  ∀ e, e < t → riseAt clk e = true → StableOn we dlen (e - su - 1) e ∧
    (we e = true → StableOn addr dlen (e - su - 1) e ∧ StableOn data dlen (e - su - 1) e)

/-- Output relation of a register file with clk-to-q window `kq`.  As long as every edge so far
was clean (`CleanWrites`), each entry shows its last written data from `kq` instants after the
writing edge, is unconstrained inside that window, and is untouched by writes to other
entries.  After a violated write nothing is promised: a glitching write enable or address may
corrupt any entry. -/
def MemAt {ι α : Type} [DecidableEq ι] [Inhabited α] (kq su : Nat) (clk : List Bool) (we : Nat → Bool)
    (addr : Nat → ι) (data : Nat → α) (dlen : Nat) (mem : List (ι → α)) (t : Nat) : Prop :=
  CleanWrites clk we addr data dlen su t → ∀ a : ι,
    ((∀ e, e < t → ¬ WriteEdge a clk we addr data dlen su e) → (mem.getD t (fun _ => default)) a = default) ∧
    (∀ e, e < t → WriteEdge a clk we addr data dlen su e →
      (∀ e', e < e' → e' < t → ¬ WriteEdge a clk we addr data dlen su e') → e + kq ≤ t →
      (mem.getD t (fun _ => default)) a = data e)

/-- The filters a netlist of gates needs of its clock and its clear, up to instant `t`. -/
structure GateOK (P pw Rr Rc : Nat) (clk crn : List Bool) (t : Nat) : Prop where
  period : ClockOK P clk t
  pulse : PulseOK pw clk t
  reset : ResetOK Rr clk t
  clear : ClearOK Rc crn t

/-- `RegOut`, binding only at the instants where the guard holds, and with the horizon `len`
given explicitly (a netlist reports no further than its clear is known either). -/
def RegOutG {β : Type} [Inhabited β] (kq su : Nat) (init : β) (G : Nat → Prop) (clk : List Bool)
    (d : Nat → β) (dlen len : Nat) (q : List β) : Prop :=
  q.length ≤ len + 1 ∧ ∀ t, t < q.length → G t → RegAt kq su init clk d dlen q t

/-- `BusRegOut`, likewise. -/
def BusRegOutG {w : Nat} (kq su : Nat) (G : Nat → Prop) (clk : List Bool) (d : Nat → BitVec w)
    (dlen len : Nat) (q : List (BitVec w)) : Prop :=
  RegOutG kq su 0#w G clk d dlen len q ∧ ∀ t, t < q.length → G t → BusWinAt kq su clk d dlen q t

/-- `MemOut`, likewise. -/
def MemOutG {ι α : Type} [DecidableEq ι] [Inhabited α] (kq su : Nat) (G : Nat → Prop)
    (clk : List Bool) (we : Nat → Bool) (addr : Nat → ι) (data : Nat → α) (dlen len : Nat)
    (mem : List (ι → α)) : Prop :=
  mem.length ≤ len + 1 ∧ ∀ t, t < mem.length → G t → MemAt kq su clk we addr data dlen mem t

end Graphiti.AsyncFifo.Contracts
