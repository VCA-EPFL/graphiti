/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.components.level2.Domains
import Graphiti.Projects.AsyncFifo.components.level1.Gates
import Graphiti.Projects.AsyncFifo.components.level4.BusReg
import Graphiti.Projects.AsyncFifo.components.level3.Contracts

/-!
# The synchroniser's first stage, bit by bit

`syncSpec` states the metastability assumption at the *bus* level: an oracle says, at every
instant, which bits of a sample resolved to the new value and what is observed while the stage
settles.  `SyncSettle.settle_orc` already shows that is no more than three per-bit clauses; this
file makes the circuit say so, by taking the stage apart into three one-bit registers.

`settleOut1 su stl clk d osel ojunk` is what one of them shows: it latches `d` at each edge,
choosing between the value at the edge and the value `su + 1` instants earlier according to
`osel`, shows `ojunk` for `stl` instants, and holds afterwards.  `syncOut_pack` is the point: the
bus-level `syncOut` *is* three of these, packed --- the oracle's `sel` and `junk` split per bit
and nothing is left over.

So the stage's netlist is three one-bit primitives plus wiring, and what the development assumes
about metastability is one clause about one bit, six times over (three bits, two domains).
`settleOut1_settleOut` (`ProofWriteOnly/`) checks that each of those primitives satisfies
`Timed.SettleOut`, the contract `Dff.dffOut_settleOut` proves of the real flip-flop wherever its
data meets the aperture.  `settlingDffO` is therefore the one leaf of the circuit that is not
built from gates: it is the metastability assumption, and `SyncStage.impl_refines :
syncImpl ⊑ syncSpec` is this component's theorem.  The second stage is an ordinary register of
the bank.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.SyncStage

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts
  Graphiti.AsyncFifo.BusReg

/-! ### One settling bit -/

/-- The state of one bit of the stage: the value it will settle to, and the instants since its
last edge. -/
structure SBit where
  val : Bool
  since : Nat

/-- Its inputs at one instant: the clock edge, the two ends of the aperture, and the oracle's
choice between them. -/
structure SBitIn where
  rise : Bool
  dNew : Bool
  dOld : Bool
  sel : Bool

def sbitStep (s : SBit) (i : SBitIn) : SBit :=
  if i.rise then ⟨if i.sel then i.dNew else i.dOld, 0⟩ else ⟨s.val, s.since + 1⟩

def sbitInp (su : Nat) (clk d osel : List Bool) (t : Nat) : SBitIn :=
  ⟨riseAt clk t, d.getD t false, d.getD (t - su - 1) false, osel.getD t false⟩

def sbitRun (su stl : Nat) (clk d osel : List Bool) (t : Nat) : SBit :=
  run sbitStep ⟨false, stl⟩ (sbitInp su clk d osel) t

def sbitLen (clk d osel ojunk : List Bool) : Nat :=
  min (min clk.length d.length) (min osel.length ojunk.length)

/-- **What one settling bit shows**: the oracle's junk while it settles, the latched value
afterwards. -/
def settleOut1 (su stl : Nat) (clk d osel ojunk : List Bool) : List Bool :=
  timeline (fun t => if (sbitRun su stl clk d osel t).since < stl then ojunk.getD t false
                     else (sbitRun su stl clk d osel t).val)
    (sbitLen clk d osel ojunk)

/-! ### The oracle, bit by bit -/

def selBit (i : Nat) (orc : List (Orc 2)) : List Bool := orc.map (fun o => o.sel.getLsbD i)
def junkBit (i : Nat) (orc : List (Orc 2)) : List Bool := orc.map (fun o => o.junk.getLsbD i)

/-! ### The netlist -/

/-- One settling bit as a block: this is the primitive, and the whole of what the development
assumes about metastability.  Its contract is `settleOut1_settleOut` --- `Timed.SettleOut` at
clk-to-q `stl` and setup `su`, which `Dff.dffOut_settleOut` proves of the real seven-gate
flip-flop wherever its data meets the aperture. -/
@[drcomponents]
def settlingDffO (su stl : Nat) :
    StringModule (List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"osel", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"ojunk", ⟨List Bool, fun s v s' => s.2.2.2 ⊏ v ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s' = s ∧
                    v = settleOut1 su stl s.1 s.2.1 s.2.2.1 s.2.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

/-- The wire from the other domain, split into bits: the latency is the wire's, the split is
the same projection `BusReg.unpack3` makes. -/
@[drcomponents]
def unpB (lat : Nat) : StringModule (List (BitVec 3)) :=
  { inputs := [ (↑"d", ⟨List (BitVec 3), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"b0", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 0 (wireOf lat s)⟩)
               , (↑"b1", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 1 (wireOf lat s)⟩)
               , (↑"b2", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 2 (wireOf lat s)⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The oracle, split into the two bits it grants each flip-flop. -/
@[drcomponents]
def unpO : StringModule (List (Orc 2)) :=
  { inputs := [ (↑"orc", ⟨List (Orc 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"s0", ⟨List Bool, fun s v s' => s' = s ∧ v = selBit 0 s⟩)
               , (↑"s1", ⟨List Bool, fun s v s' => s' = s ∧ v = selBit 1 s⟩)
               , (↑"s2", ⟨List Bool, fun s v s' => s' = s ∧ v = selBit 2 s⟩)
               , (↑"j0", ⟨List Bool, fun s v s' => s' = s ∧ v = junkBit 0 s⟩)
               , (↑"j1", ⟨List Bool, fun s v s' => s' = s ∧ v = junkBit 1 s⟩)
               , (↑"j2", ⟨List Bool, fun s v s' => s' = s ∧ v = junkBit 2 s⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-! ### The netlist

The three blocks wired together.  The clock forks to the three flip-flops, the bus splits into
its bits, the oracle splits into the six bits it grants, and the three settled bits are packed
back into a bus. -/

def stageGraph (lat su stl : Nat) := [graphEnv|
    clk [type="io"];
    d [type="io"];
    orc [type="io"];
    q [type="io"];

    unpB [type="unpB", typeImp=$(⟨_, unpB lat⟩)];
    unpO [type="unpO", typeImp=$(⟨_, unpO⟩)];
    clkF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    ff0 [type="sdff", typeImp=$(⟨_, settlingDffO su stl⟩)];
    ff1 [type="sdff", typeImp=$(⟨_, settlingDffO su stl⟩)];
    ff2 [type="sdff", typeImp=$(⟨_, settlingDffO su stl⟩)];
    pk [type="pack3", typeImp=$(⟨_, pack3⟩)];

    clk -> clkF [to="in"];
    d -> unpB [to="d"];
    orc -> unpO [to="orc"];

    clkF -> ff0 [from="out1", to="clk"];
    clkF -> ff1 [from="out2", to="clk"];
    clkF -> ff2 [from="out3", to="clk"];
    unpB -> ff0 [from="b0", to="d"];
    unpB -> ff1 [from="b1", to="d"];
    unpB -> ff2 [from="b2", to="d"];
    unpO -> ff0 [from="s0", to="osel"];
    unpO -> ff1 [from="s1", to="osel"];
    unpO -> ff2 [from="s2", to="osel"];
    unpO -> ff0 [from="j0", to="ojunk"];
    unpO -> ff1 [from="j1", to="ojunk"];
    unpO -> ff2 [from="j2", to="ojunk"];
    ff0 -> pk [from="q", to="b0"];
    ff1 -> pk [from="q", to="b1"];
    ff2 -> pk [from="q", to="b2"];

    pk -> q [from="q"];
  ]

@[drunfold_defs]
def stageLowered := (stageGraph 0 0 0).1.lower_TR |>.get rfl

def senvS (lat su stl : Nat) := (stageGraph lat su stl).2

/-- **The synchroniser's first stage: three settling flip-flops.** -/
def syncImpl (lat su stl : Nat) := [e| stageLowered, (senvS lat su stl).find? ]

section Spec
variable {n : Nat}

/-- State of the metastable synchroniser stage: the value it will settle to, and the number of
instants since its last edge. -/
structure SyncReg (n : Nat) where
  val : BitVec (n+1)
  since : Nat

structure SyncIn (n : Nat) where
  rise : Bool
  dNew : BitVec (n+1)
  dOld : BitVec (n+1)
  orc : Orc n

def syncStep (s : SyncReg n) (i : SyncIn n) : SyncReg n :=
  if i.rise then ⟨mix i.orc.sel i.dNew i.dOld, 0⟩ else ⟨s.val, s.since + 1⟩

/-- Inputs of the stage at instant `t`: the bus is read through a wire of latency `lat`, at
the edge and `su + 1` instants earlier. -/
def syncInp (lat su : Nat) (clk : List Bool) (d : List (BitVec (n+1))) (orc : List (Orc n)) (t : Nat) : SyncIn n :=
  ⟨riseAt clk t, delayed lat d t, delayed lat d (t - su - 1), orc.getD t default⟩

def syncLen (lat : Nat) (clk : List Bool) (d : List (BitVec (n+1))) (orc : List (Orc n)) : Nat :=
  min (min clk.length (d.length + lat)) orc.length

def syncRun (lat su stl : Nat) (clk : List Bool) (d : List (BitVec (n+1))) (orc : List (Orc n)) (t : Nat) : SyncReg n :=
  run syncStep ⟨0#(n+1), stl⟩ (syncInp lat su clk d orc) t

/-- Output of the synchroniser stage: junk while settling, the settled value otherwise.  The
junk at instant `t` is the oracle's, so the output is only known while the oracle is. -/
def syncOut (lat su stl : Nat) (clk : List Bool) (d : List (BitVec (n+1))) (orc : List (Orc n)) : List (BitVec (n+1)) :=
  timeline (fun t => if (syncRun lat su stl clk d orc t).since < stl then (orc.getD t default).junk
                     else (syncRun lat su stl clk d orc t).val)
    (syncLen lat clk d orc)

end Spec

section Spec
variable {n : Nat}
variable (α : Type) [Inhabited α]

/-- The metastable first synchroniser stage, sampling the other domain's Gray pointer through
a wire of latency `lat`.  Its output is determined by the oracle, and like every other block it
records what it has reported, so that its reports only grow --- which is what lets a netlist
stand in for it (`SyncStage.lean`). -/
@[drcomponents]
def syncSpec (lat su stl : Nat) :
    StringModule (List Bool × List (BitVec (n+1)) × List (Orc n) × List (BitVec (n+1))) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (BitVec (n+1)), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"orc", ⟨List (Orc n), fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List (BitVec (n+1)), fun s v s' => s.2.2.2 <+: v ∧
                    v <+: syncOut lat su stl s.1 s.2.1 s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

end Spec

end Graphiti.AsyncFifo.SyncStage
