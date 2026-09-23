/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level1.Filters
import Graphiti.Projects.AsyncFifo.components.level0.Gray
import Graphiti.Projects.AsyncFifo.components.level0.Streams

/-!
# The two clock domains of the asynchronous FIFO, with explicit timing

The FIFO is the classic Cummings design with `2^n` entries:

* **Write domain** (clock `wclk`): an `(n+1)`-bit binary write pointer, a `full` flag,
  the memory, and a two-stage synchroniser `q1 → q2` sampling the *Gray-coded* read
  pointer coming from the other domain.  `full` is registered and compares the next
  write pointer with the (decoded) synchronised read pointer plus `2^n`.
* **Read domain** (clock `rclk`): an `(n+1)`-bit binary read pointer, an `empty` flag,
  and a two-stage synchroniser sampling the Gray-coded write pointer.  `empty` compares
  the next read pointer with the decoded synchronised write pointer.  The read data is
  the memory word at the read address (first-word-fall-through).

Each domain is a Moore machine (`Streams.lean`): at a rising edge of its clock the whole
register state is updated from the previous state and the inputs at that instant; the
outputs at instant `t` are functions of the state *before* the edge at `t`.

## Timing model of the clock-domain crossing

Two explicit parameters describe the physics of the crossing:

* `lat`, the **wire latency**: at an edge at instant `t` the first synchroniser stage
  samples the value the other domain produced at instant `t - lat`;
* `su`, the **setup window** of the sampler: the bits of the sample resolve between the
  value at `t - lat` and the value `su + 1` instants earlier;
* `stl`, the **settling time** of the first stage: because the sampled bus may be changing,
  the stage resolves each bit independently to its old or new value (metastability), and
  for `stl` instants after the edge its output is unpredictable.  The second stage samples
  the first at the next edge; if that edge comes too early, it samples garbage.

All nondeterminism is made explicit through an **oracle** input stream `Orc`: per instant
a selection mask (which bits resolve to the new value) and the unpredictable value.  The
domains are deterministic given their oracle, and the oracles are unconstrained modules of
the circuit (`Oracle.lean`, wired in by `Fifo.lean`), so the refinement theorem quantifies over every resolution.
The wires themselves are exact.

The temporal theorem `fifo_correct` (`ProofWriteOnly/Invariant.lean`) shows that, as long as the clocks
respect the periods `P_w`, `P_r` assumed by the specification and `stl < P`, `su < P` for both,
the second stage never samples an unsettled first stage and the FIFO property holds.  The
register `since` (instants since the last edge) is the report's "delay filter" counter.

This file holds the machines themselves: the domains' specifications (`WriteDomain.lean`,
`ReadDomain.lean`) are written in terms of them.  Their
length and indexing facts, their congruence lemmas and the machine-level invariants (`WInv`,
`RInv`) are in `ProofWriteOnly/Domains.lean`.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo
open Gray

/-- The oracle resolving the nondeterminism of one synchroniser at one instant. -/
structure Orc (n : Nat) where
  /-- which bits of the sampled bus resolve to the new value -/
  sel : BitVec (n+1)
  /-- the value observed while the first stage is still settling -/
  junk : BitVec (n+1)

/-- The value a wire with latency `lat` presents at instant `t`: the source's value at
`t - lat`, or the initial value `0` before anything has propagated. -/
def delayed {w : Nat} (lat : Nat) (s : List (BitVec w)) (t : Nat) : BitVec w :=
  if t < lat then 0#w else s.getD (t - lat) 0#w

/-- The other domain's bus as it arrives on the wire. -/
def wireOf (lat : Nat) (d : List (BitVec 3)) : List (BitVec 3) :=
  timeline (delayed lat d) (d.length + lat)

section Machines
open Gray

/-- Bit `i` of `mix sel a b` is bit `i` of `a` where `sel` is set and bit `i` of `b` elsewhere. -/
def mix {w : Nat} (sel a b : BitVec w) : BitVec w := (sel &&& a) ||| (~~~sel &&& b)

instance {n : Nat} : Inhabited (Orc n) := ⟨⟨0#(n+1), 0#(n+1)⟩⟩

end Machines

section Machines
open Gray
variable {α : Type} [Inhabited α] {n : Nat}

/-- Registers of the write domain.  `since` counts the instants since the last rising edge. -/
structure WReg (α : Type) (n : Nat) where
  ptr : BitVec (n+1)
  full : Bool
  mem : BitVec n → α
  q1 : BitVec (n+1)
  q2 : BitVec (n+1)
  since : Nat

/-- Inputs of the write domain at one instant: the rising-edge bit, the write request and
data, the delayed Gray read pointer at this instant and at the previous one, and the oracle. -/
structure WIn (α : Type) (n : Nat) where
  rise : Bool
  inc : Bool
  data : α
  rgNew : BitVec (n+1)
  rgOld : BitVec (n+1)
  orc : Orc n

def WReg.init (α : Type) [Inhabited α] (n stl : Nat) : WReg α n :=
  ⟨0#(n+1), false, fun _ => default, 0#(n+1), 0#(n+1), stl⟩

/-- One instant of the write domain with settling time `stl`. -/
def wstep (stl : Nat) (s : WReg α n) (i : WIn α n) : WReg α n :=
  if i.rise then
    let ok := i.inc && !s.full
    let ptr' := if ok then s.ptr + 1#(n+1) else s.ptr
    { ptr := ptr'
      full := ptr' == ungray s.q2 + BitVec.ofNat (n+1) (2 ^ n)
      mem := if ok then (fun a => if a = s.ptr.setWidth n then i.data else s.mem a) else s.mem
      q1 := mix i.orc.sel i.rgNew i.rgOld
      q2 := if stl ≤ s.since then s.q1 else i.orc.junk
      since := 0 }
  else { s with since := s.since + 1 }

def winp (lat su : Nat) (wclk winc : List Bool) (wdata : List α) (rgray : List (BitVec (n+1)))
    (orc : List (Orc n)) (t : Nat) : WIn α n :=
  ⟨riseAt wclk t, winc.getD t false, wdata.getD t default,
   delayed lat rgray t, delayed lat rgray (t - su - 1), orc.getD t default⟩

def wLen (lat : Nat) (wclk winc : List Bool) (wdata : List α) (rgray : List (BitVec (n+1)))
    (orc : List (Orc n)) : Nat :=
  min (min wclk.length winc.length) (min (min wdata.length (rgray.length + lat)) orc.length)

def wRun (lat stl su : Nat) (wclk winc : List Bool) (wdata : List α) (rgray : List (BitVec (n+1)))
    (orc : List (Orc n)) (t : Nat) : WReg α n :=
  run (wstep stl) (WReg.init α n stl) (winp lat su wclk winc wdata rgray orc) t

structure RReg (n : Nat) where
  ptr : BitVec (n+1)
  empty : Bool
  q1 : BitVec (n+1)
  q2 : BitVec (n+1)
  since : Nat

structure RIn (n : Nat) where
  rise : Bool
  inc : Bool
  wgNew : BitVec (n+1)
  wgOld : BitVec (n+1)
  orc : Orc n

def RReg.init (n stl : Nat) : RReg n := ⟨0#(n+1), true, 0#(n+1), 0#(n+1), stl⟩

def rstep (stl : Nat) (s : RReg n) (i : RIn n) : RReg n :=
  if i.rise then
    let ok := i.inc && !s.empty
    let ptr' := if ok then s.ptr + 1#(n+1) else s.ptr
    { ptr := ptr'
      empty := ptr' == ungray s.q2
      q1 := mix i.orc.sel i.wgNew i.wgOld
      q2 := if stl ≤ s.since then s.q1 else i.orc.junk
      since := 0 }
  else { s with since := s.since + 1 }

def rinp (lat su : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n))
    (t : Nat) : RIn n :=
  ⟨riseAt rclk t, rinc.getD t false, delayed lat wgray t, delayed lat wgray (t - su - 1), orc.getD t default⟩

def rLen (lat : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n)) : Nat :=
  min (min rclk.length rinc.length) (min (wgray.length + lat) orc.length)

def rRun (lat stl su : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n))
    (t : Nat) : RReg n :=
  run (rstep stl) (RReg.init n stl) (rinp lat su rclk rinc wgray orc) t

/-- Length of the read-data stream: it is combinational in the memory snapshot, so it is
only known while the memory is. -/
def rDataLen (lat : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n))
    (mem : List (BitVec n → α)) : Nat :=
  min (rLen lat rclk rinc wgray orc + 1) mem.length

/-- Read data at instant `t`: the memory word at the current read address. -/
def rval (lat stl su : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n))
    (mem : List (BitVec n → α)) (t : Nat) : α :=
  (mem.getD t (fun _ => default)) ((rRun lat stl su rclk rinc wgray orc t).ptr.setWidth n)

end Machines

section Machines
open Gray

/-- `e` is the last rising edge of `c` before instant `t`. -/
def LastEdge (c : List Bool) (e t : Nat) : Prop :=
  e < t ∧ riseAt c e = true ∧ ∀ e', e < e' → e' < t → riseAt c e' = false

/-- No rising edge of `c` before instant `t`. -/
def NoEdge (c : List Bool) (t : Nat) : Prop := ∀ e, e < t → riseAt c e = false

end Machines

section Settling
set_option linter.unusedSectionVars false
open Gray

/-- Register outputs are meaningful `kq` instants after the last edge, and before any edge. -/
def Settled (kq : Nat) (clk : List Bool) (t : Nat) : Prop :=
  NoEdge clk t ∨ ∃ e, LastEdge clk e t ∧ e + kq ≤ t

end Settling

section Records
variable {n : Nat}
variable (α : Type) [Inhabited α]

/-- The registers of the write domain other than the memory, the Gray pointer register and the
synchroniser: binary pointer, flag, second synchroniser stage. -/
structure WSt (n : Nat) where
  ptr : BitVec (n+1)
  full : Bool
  q2 : BitVec (n+1)

/-- The next-state logic of the write domain as a pure function: from the state, the write
request, and the current synchroniser output, it produces the next state, the next Gray
pointer (registered separately, so that the bus that crosses clock domains never glitches),
and the memory write command. -/
structure WNext (α : Type) (n : Nat) where
  st : WSt n
  gnext : BitVec (n+1)
  we : Bool
  addr : BitVec n
  data : α

/-- The power-on reset: a source that produces a clear satisfying `ClearOK Rc`.  It is internal
to the write domain, so the domain's interface is the one the register level already had --- a
netlist of gates has no defined state until something puts it there, but nothing outside needs
to know that. -/
@[drcomponents]
def clearSrc (Rc : Nat) : StringModule (List Bool) :=
  { inputs := ∅
    outputs := [ (↑"crn", ⟨List Bool, fun s v s' => s ⊏ v ∧ ClearOK Rc v v.length ∧ s' = v⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- A two-way fork (zero delay) for the clock, as in the report. -/
@[drcomponents]
def fork2 (β : Type) : StringModule (List β) :=
  { inputs := [ (↑"in", ⟨List β, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List β, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List β, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

end Records

section Records
variable {n : Nat}
variable (α : Type) [Inhabited α]

/-- The registers of the read domain that the bank holds. -/
structure RSt (n : Nat) where
  ptr : BitVec (n+1)
  empty : Bool
  q2 : BitVec (n+1)

/-- A FIFO starts empty. -/
instance : Inhabited (RSt n) := ⟨⟨0#(n+1), true, 0#(n+1)⟩⟩

/-- The next-state logic of the read domain: the next state and the next Gray pointer
(registered separately, so the bus that crosses clock domains never glitches). -/
structure RNext (n : Nat) where
  st : RSt n
  gnext : BitVec (n+1)

instance : Inhabited (RNext n) := ⟨⟨default, 0#(n+1)⟩⟩

end Records

section Records
variable {n : Nat}

def rNext (st : RSt n) (inc : Bool) (q1 : BitVec (n+1)) : RNext n :=
  let ok := inc && !st.empty
  let ptr' := if ok then st.ptr + 1#(n+1) else st.ptr
  { st := { ptr := ptr', empty := ptr' == Gray.ungray st.q2, q2 := q1 }
    gnext := Gray.gray ptr' }

end Records

section Records
variable {n : Nat}
variable (α : Type) [Inhabited α]

instance : Inhabited (WSt n) := ⟨⟨0#(n+1), false, 0#(n+1)⟩⟩

instance : Inhabited (WNext α n) := ⟨⟨default, 0#(n+1), false, 0#n, default⟩⟩

def wNext (st : WSt n) (inc : Bool) (data : α) (q1 : BitVec (n+1)) : WNext α n :=
  let ok := inc && !st.full
  let ptr' := if ok then st.ptr + 1#(n+1) else st.ptr
  { st := { ptr := ptr', full := ptr' == Gray.ungray st.q2 + BitVec.ofNat (n+1) (2 ^ n), q2 := q1 }
    gnext := Gray.gray ptr'
    we := ok
    addr := st.ptr.setWidth n
    data := data }

end Records

end Graphiti.AsyncFifo
