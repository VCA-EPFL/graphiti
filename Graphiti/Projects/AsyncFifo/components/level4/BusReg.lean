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
import Graphiti.Projects.AsyncFifo.components.level3.Dff

/-!
# A three-bit register from three flip-flops

The Gray pointer of the write domain is a three-bit register, and this is that register: three
flip-flops sharing a clock and a clear, with the bus split into bits on the way
in and reassembled on the way out.

The two adapters are not gates.  They are the same reinterpretation of a bus as its bits that
`WriteNext.lean` uses, with no delay of their own: a netlist has no notion of a bus, only of
wires, and the boundary is where the two views meet.

Each flip-flop node is the flip-flop's *specification*, `dffSpec`, as in every component: the
gates are substituted in at the top (`TopGates.lean`), and refining component by component is
what keeps each proof the size of one block.  `BusReg.impl_refines : busImpl ⊑ busSpec`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.BusReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Dff

/-! ### The bus adapters -/

/-- The bits of a bus, as far as the bus is known. -/
def bitsOf (i : Nat) (d : List (BitVec 3)) : List Bool := d.map (·.getLsbD i)

/-- Split a bus into its three bits. -/
@[drcomponents]
def unpack3 : StringModule (List (BitVec 3)) :=
  { inputs := [ (↑"d", ⟨List (BitVec 3), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"b0", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 0 s⟩)
               , (↑"b1", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 1 s⟩)
               , (↑"b2", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 2 s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The bus assembled from its bits, known as far as every bit is. -/
def pack3Out (b0 b1 b2 : List Bool) : List (BitVec 3) :=
  timeline (fun t => bv3 (b0.getD t false) (b1.getD t false) (b2.getD t false))
    (min (min b0.length b1.length) b2.length)

/-- Assemble a bus from its three bits. -/
@[drcomponents]
def pack3 : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"b0", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"b1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"b2", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List (BitVec 3), fun s v s' => s' = s ∧ v = pack3Out s.1 s.2.1 s.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

/-! ### The netlist -/

def busGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    q [type="io"];

    unp [type="unpack3", typeImp=$(⟨_, unpack3⟩)];
    clkF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    crF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    ff0 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff1 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff2 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    pk [type="pack3", typeImp=$(⟨_, pack3⟩)];

    clk -> clkF [to="in"];
    d -> unp [to="d"];
    clrn -> crF [to="in"];

    clkF -> ff0 [from="out1", to="clk"];
    clkF -> ff1 [from="out2", to="clk"];
    clkF -> ff2 [from="out3", to="clk"];
    crF -> ff0 [from="out1", to="clrn"];
    crF -> ff1 [from="out2", to="clrn"];
    crF -> ff2 [from="out3", to="clrn"];
    unp -> ff0 [from="b0", to="d"];
    unp -> ff1 [from="b1", to="d"];
    unp -> ff2 [from="b2", to="d"];
    ff0 -> pk [from="q", to="b0"];
    ff1 -> pk [from="q", to="b1"];
    ff2 -> pk [from="q", to="b2"];

    pk -> q [from="q"];
  ]

@[drunfold_defs]
def busLowered := busGraph.1.lower_TR |>.get rfl

/-- What each node of the graph is: the bus adapters and forks, and for each flip-flop its specification `Dff.dffSpec`. -/
def benv := busGraph.2

/-- **The three-bit register**: the graph, each child standing for its specification. -/
def busImpl := [e| busLowered, benv.find? ]

/-! ### The specification -/

/-- What the register reports: each bit of the bus through its own flip-flop. -/
def busOut (clk : List Bool) (d : List (BitVec 3)) (crn : List Bool) : List (BitVec 3) :=
  pack3Out (dffOut clk (bitsOf 0 d) crn) (dffOut clk (bitsOf 1 d) crn) (dffOut clk (bitsOf 2 d) crn)

/-- The three-bit register as a single block. -/
@[drcomponents]
def busSpec : StringModule (List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (BitVec 3), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List (BitVec 3), fun s v s' => s.2.2.2 <+: v ∧
                    v <+: busOut s.1 s.2.1 s.2.2.1 ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

end Graphiti.AsyncFifo.BusReg
