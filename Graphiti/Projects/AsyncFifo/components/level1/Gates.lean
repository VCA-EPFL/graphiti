/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Streams

/-!
# Gates

Unit-delay boolean gates as Graphiti modules, in the style of Kobler's report: a gate stores
its input streams, and its output at instant `t ≥ 1` is the gate function of the inputs at
`t - 1`; at instant `0` it is low (`delay false`).  A gate reports its output only as far as
its inputs are known (one instant less than it could), so that outputs never outrun inputs.  Forks copy a stream with no
delay.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Gates

open Graphiti.AsyncFifo

/-! ### Gate semantics on streams

A gate has unit delay, so its output at instant `t` is its function of the inputs at `t - 1`,
and at instant `0` it is low: nothing has propagated yet.  That makes the output *one instant
longer* than its inputs -- the Moore convention of Kobler's report, and the reason information
can go round a loop at all.  A gate that truncated its output to its inputs' horizon would be
sound but useless: in a cycle every gate would wait for the one before it and no stream would
ever grow. -/

/-- Output of a two-input gate: low at `0`, then `f` of the inputs one instant earlier. -/
def gateOut (f : Bool → Bool → Bool) (a b : List Bool) : List Bool :=
  false :: List.zipWith f a b

/-- Output of a three-input gate (the flip-flop needs one). -/
def gate3Out (f : Bool → Bool → Bool → Bool) (a b c : List Bool) : List Bool :=
  false :: List.zipWith (fun x yz => f x yz.1 yz.2) a (b.zip c)

/-- Output of a one-input gate. -/
def gate1Out (f : Bool → Bool) (a : List Bool) : List Bool := false :: a.map f

/-! ### Gate modules -/

/-- A two-input gate with function `f`. -/
@[drcomponents]
def gate2 (f : Bool → Bool → Bool) : StringModule (List Bool × List Bool) :=
  { inputs := [ (↑"a", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"b", ⟨List Bool, fun s v s' => s.2 ⊏ v ∧ s' = (s.1, v)⟩) ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = gateOut f s.1 s.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], []) }

/-- A one-input gate with function `f`. -/
@[drcomponents]
def gate1 (f : Bool → Bool) : StringModule (List Bool) :=
  { inputs := [ (↑"a", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = gate1Out f s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- A three-input gate with function `f`. -/
@[drcomponents]
def gate3 (f : Bool → Bool → Bool → Bool) : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"a", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"b", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"c", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = gate3Out f s.1 s.2.1 s.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

/-- Zero-delay forks. -/
@[drcomponents]
def fork3 : StringModule (List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out3", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

@[drcomponents]
def fork4 : StringModule (List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out3", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out4", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

@[drcomponents]
def fork5 : StringModule (List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out3", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out4", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out5", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

@[drcomponents]
def fork7 : StringModule (List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out3", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out4", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out5", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out6", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out7", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-! ### Buses and their bits -/

/-- A three-bit bus from its bits, least significant first. -/
def bv3 (b0 b1 b2 : Bool) : BitVec 3 :=
  (BitVec.ofBool b0).setWidth 3 ||| ((BitVec.ofBool b1).setWidth 3 <<< 1) |||
    ((BitVec.ofBool b2).setWidth 3 <<< 2)

/-- A two-bit bus from its bits. -/
def bv2 (b0 b1 : Bool) : BitVec 2 :=
  (BitVec.ofBool b0).setWidth 2 ||| ((BitVec.ofBool b1).setWidth 2 <<< 1)

/-! ### The reporting policy of a block

A netlist of unit-delay gates computes further ahead than its inputs: each level of logic knows
its output one instant past the inputs it reads, which is exactly what lets a stream go round a
loop.  What a *block* may report is another matter.  The timing contracts the blocks are
proved against (`components/level3/Contracts.lean`) bound an output by the horizon of the block's inputs (plus the one instant a Moore block is entitled to,
since its output at `t` depends on its inputs strictly before `t`), and that bound is what makes
them monotone: if a block reported a value that a not-yet-known clock edge would change, the
stream it remembers could not stay valid as its inputs grow.

So a gate-level block ends in `cut3`, which passes its input on only as far as three reference
streams -- the block's own inputs -- are known, plus one.  This is not a gate: it computes
nothing, and reporting less than one knows is always sound. -/

/-- Report a stream as far as four reference streams are known, plus one instant. -/
@[drcomponents]
def cut4 : StringModule (List Bool × List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"r1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"r2", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"r3", ⟨List Bool, fun s v s' => s.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
              , (↑"r4", ⟨List Bool, fun s v s' => s.2.2.2.2 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧
                    v = s.1.take (min (min s.2.1.length s.2.2.1.length)
                      (min s.2.2.2.1.length s.2.2.2.2.length) + 1)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], []) }

/-- Report a stream as far as three reference streams are known, plus one instant. -/
@[drcomponents]
def cut3 : StringModule (List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"r1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"r2", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"r3", ⟨List Bool, fun s v s' => s.2.2.2 ⊏ v ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧
                    v = s.1.take (min (min s.2.1.length s.2.2.1.length) s.2.2.2.length + 1)⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

end Graphiti.AsyncFifo.Gates
