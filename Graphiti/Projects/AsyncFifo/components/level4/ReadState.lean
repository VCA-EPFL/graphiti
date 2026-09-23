/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.components.level1.Gates
import Graphiti.Projects.AsyncFifo.components.level3.Contracts
import Graphiti.Projects.AsyncFifo.components.level3.Dff

/-!
# The read domain's state register, from seven flip-flops

The read domain's state is an `RSt 2`: a three-bit pointer, the `empty` flag, and the three bits
of the second synchroniser stage.  Seven flip-flops, then, sharing a clock and a clear, with the
record split into bits on the way in and reassembled on the way out --- `WriteState.lean` at the read
domain's record.  The two files are line-for-line the same apart from the one bit below; see
`WriteState.lean` for why they are not one register generic in the record.

One bit is not the flag itself.  A flip-flop clears to `false`, and a FIFO powers up *empty*, so
the register stores `!empty`: the bank then needs no set-reset flip-flop and no inverted clear,
and `stBit` inverts it on the way in and `packStOut` on the way out.  Nothing outside this
register sees the inversion: it takes and reports `RSt 2` records, with `empty` meaning what
it says.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.ReadState

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Dff

/-! ### The record and its bits -/

/-- The seven bits of the read domain's state: the pointer, the *complement* of the flag (so
that the cleared register reads empty), the second stage. -/
def stBit (i : Nat) (x : RSt 2) : Bool :=
  if i < 3 then x.ptr.getLsbD i else if i = 3 then !x.empty else x.q2.getLsbD (i - 4)

def bitsOf (i : Nat) (d : List (RSt 2)) : List Bool := d.map (stBit i)

/-! ### The bus adapters -/

/-- Split the state record into its seven bits (the flag complemented). -/
@[drcomponents]
def unpackSt : StringModule (List (RSt 2)) :=
  { inputs := [ (↑"d", ⟨List (RSt 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"b0", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 0 s⟩)
               , (↑"b1", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 1 s⟩)
               , (↑"b2", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 2 s⟩)
               , (↑"b3", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 3 s⟩)
               , (↑"b4", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 4 s⟩)
               , (↑"b5", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 5 s⟩)
               , (↑"b6", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 6 s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The record assembled from its bits, known as far as every bit is. -/
def packStOut (b0 b1 b2 b3 b4 b5 b6 : List Bool) : List (RSt 2) :=
  timeline (fun t => ⟨bv3 (b0.getD t false) (b1.getD t false) (b2.getD t false), !(b3.getD t false),
      bv3 (b4.getD t false) (b5.getD t false) (b6.getD t false)⟩)
    (min (min (min b0.length b1.length) (min b2.length b3.length))
      (min (min b4.length b5.length) b6.length))

/-- Assemble the state record from its seven bits. -/
@[drcomponents]
def packSt : StringModule (List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"b0", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"b1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"b2", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"b3", ⟨List Bool, fun s v s' => s.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
              , (↑"b4", ⟨List Bool, fun s v s' => s.2.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩)
              , (↑"b5", ⟨List Bool, fun s v s' => s.2.2.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v, s.2.2.2.2.2.2)⟩)
              , (↑"b6", ⟨List Bool, fun s v s' => s.2.2.2.2.2.2 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List (RSt 2), fun s v s' => s' = s ∧
                    v = packStOut s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1
                      s.2.2.2.2.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], [], []) }

/-! ### The netlist -/

def stGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    q [type="io"];

    unp [type="unpackSt", typeImp=$(⟨_, unpackSt⟩)];
    clkF [type="fork7", typeImp=$(⟨_, fork7⟩)];
    crF [type="fork7", typeImp=$(⟨_, fork7⟩)];
    ff0 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff1 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff2 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff3 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff4 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff5 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff6 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    pk [type="packSt", typeImp=$(⟨_, packSt⟩)];

    clk -> clkF [to="in"];
    d -> unp [to="d"];
    clrn -> crF [to="in"];

    clkF -> ff0 [from="out1", to="clk"];
    clkF -> ff1 [from="out2", to="clk"];
    clkF -> ff2 [from="out3", to="clk"];
    clkF -> ff3 [from="out4", to="clk"];
    clkF -> ff4 [from="out5", to="clk"];
    clkF -> ff5 [from="out6", to="clk"];
    clkF -> ff6 [from="out7", to="clk"];
    crF -> ff0 [from="out1", to="clrn"];
    crF -> ff1 [from="out2", to="clrn"];
    crF -> ff2 [from="out3", to="clrn"];
    crF -> ff3 [from="out4", to="clrn"];
    crF -> ff4 [from="out5", to="clrn"];
    crF -> ff5 [from="out6", to="clrn"];
    crF -> ff6 [from="out7", to="clrn"];
    unp -> ff0 [from="b0", to="d"];
    unp -> ff1 [from="b1", to="d"];
    unp -> ff2 [from="b2", to="d"];
    unp -> ff3 [from="b3", to="d"];
    unp -> ff4 [from="b4", to="d"];
    unp -> ff5 [from="b5", to="d"];
    unp -> ff6 [from="b6", to="d"];
    ff0 -> pk [from="q", to="b0"];
    ff1 -> pk [from="q", to="b1"];
    ff2 -> pk [from="q", to="b2"];
    ff3 -> pk [from="q", to="b3"];
    ff4 -> pk [from="q", to="b4"];
    ff5 -> pk [from="q", to="b5"];
    ff6 -> pk [from="q", to="b6"];

    pk -> q [from="q"];
  ]

@[drunfold_defs]
def stLowered := stGraph.1.lower_TR |>.get rfl

/-- What each node of the graph is: the bus adapters and forks, and for each flip-flop its specification `Dff.dffSpec`. -/
def senv := stGraph.2

/-- **The state register**: the graph, each child standing for its specification. -/
def stImpl := [e| stLowered, senv.find? ]

/-! ### The specification -/

/-- What the register reports: each bit of the bus through its own flip-flop. -/
def stOut (clk : List Bool) (d : List (RSt 2)) (crn : List Bool) : List (RSt 2) :=
  packStOut (dffOut clk (bitsOf 0 d) crn) (dffOut clk (bitsOf 1 d) crn) (dffOut clk (bitsOf 2 d) crn) (dffOut clk (bitsOf 3 d) crn) (dffOut clk (bitsOf 4 d) crn) (dffOut clk (bitsOf 5 d) crn) (dffOut clk (bitsOf 6 d) crn)

/-- The seven-bit state register of the read domain as a single block. -/
@[drcomponents]
def stSpec : StringModule (List Bool × List (RSt 2) × List Bool × List (RSt 2)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (RSt 2), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List (RSt 2), fun s v s' => s.2.2.2 <+: v ∧
                    v <+: stOut s.1 s.2.1 s.2.2.1 ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

end Graphiti.AsyncFifo.ReadState
