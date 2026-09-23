/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.components.level3.Contracts
import Graphiti.Projects.AsyncFifo.components.level4.BusReg
import Graphiti.Projects.AsyncFifo.components.level4.ReadState

/-!
# The read domain's register bank

The read domain's state: a seven-bit state register, the three-bit Gray
pointer that crosses into the write domain, and the `empty` flag (a projection of the state).
This file wires the two registers together --- each as its specification --- and unpacks the
next-state bus that feeds them.  `bankSpec` is the bank's timed contract, and
`ReadBank.impl_refines` (`TopRefinement.lean`) the proof that the implementation meets it.

It is `WriteBank.lean` without the register file: the read domain holds no memory of its own, it only
addresses the write domain's.  So there are three output ports instead of four, and two
registers instead of three.

Like the write bank, it has one port the register-level model does not: the clear.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.ReadBank

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts
  Graphiti.AsyncFifo.Dff

/-! ### The next-state bus and its fields -/

def stOf (d : List (RNext 2)) : List (RSt 2) := d.map (·.st)
def gnextOf (d : List (RNext 2)) : List (BitVec 3) := d.map (·.gnext)

/-- Split the next-state bus into the two streams the bank's registers read. -/
@[drcomponents]
def unpackNext : StringModule (List (RNext 2)) :=
  { inputs := [ (↑"d", ⟨List (RNext 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s' = s ∧ v = stOf s⟩)
               , (↑"gnext", ⟨List (BitVec 3), fun s v s' => s' = s ∧ v = gnextOf s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The `empty` flag is a bit of the state register. -/
@[drcomponents]
def emptyOf : StringModule (List (RSt 2)) :=
  { inputs := [ (↑"q", ⟨List (RSt 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"empty", ⟨List Bool, fun s v s' => s' = s ∧ v = s.map (·.empty)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-! ### The netlist -/

def bankGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    st [type="io"];
    empty [type="io"];
    gray [type="io"];

    unpN [type="unpackNext", typeImp=$(⟨_, unpackNext⟩)];
    clkF [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    crF [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    stR [type="streg", typeImp=$(⟨_, ReadState.stSpec⟩)];
    stF [type="forkSt", typeImp=$(⟨_, fork2 (RSt 2)⟩)];
    emptyA [type="emptyOf", typeImp=$(⟨_, emptyOf⟩)];
    grR [type="busreg", typeImp=$(⟨_, BusReg.busSpec⟩)];

    clk -> clkF [to="in"];
    d -> unpN [to="d"];
    clrn -> crF [to="in"];

    clkF -> stR [from="out1", to="clk"];
    clkF -> grR [from="out2", to="clk"];
    crF -> stR [from="out1", to="clrn"];
    crF -> grR [from="out2", to="clrn"];
    unpN -> stR [from="st", to="d"];
    unpN -> grR [from="gnext", to="d"];
    stR -> stF [from="q", to="in"];
    stF -> emptyA [from="out2", to="q"];

    stF -> st [from="out1"];
    emptyA -> empty [from="empty"];
    grR -> gray [from="q"];
  ]

@[drunfold_defs]
def bankLowered := bankGraph.1.lower_TR |>.get rfl

/-- What each node of the graph is: the splitter and forks, and the state register and the Gray-pointer register by their
specifications. -/
def kenv := bankGraph.2

/-- **The read domain's register bank**: the graph, each child standing for its specification. -/
def bankImpl := [e| bankLowered, kenv.find? ]

section Spec
variable {n : Nat}
variable (α : Type) [Inhabited α]

/-- State of the read domain's register bank. -/
structure RRegSt (n : Nat) where
  clk : List Bool
  d : List (RNext n)
  crn : List Bool
  st_q : List (RSt n)
  empty_q : List Bool
  gray_q : List (BitVec (n+1))

/-- How far the bank's inputs are known. -/
def RRegSt.horizon (s : RRegSt n) : Nat := min (min s.clk.length s.d.length) s.crn.length

/-- The register bank of the read domain: the state, the `empty` flag (a projection of it) and
the Gray pointer that crosses into the other domain.  Guarded like the write domain's
(`GateOK`), and with no memory. -/
@[drcomponents]
def bankSpec (kq su P pw Rr Rc : Nat) : StringModule (RRegSt n) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.clk ⊏ v ∧ s' = { s with clk := v }⟩)
              , (↑"d", ⟨List (RNext n), fun s v s' => s.d ⊏ v ∧ s' = { s with d := v }⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.crn ⊏ v ∧ s' = { s with crn := v }⟩)
              ].toAssocList
    outputs := [ (↑"st", ⟨List (RSt n), fun s v s' => s.st_q <+: v ∧
                    RegOutG kq su default (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).st) s.d.length s.horizon v ∧
                    s' = { s with st_q := v }⟩)
               , (↑"empty", ⟨List Bool, fun s v s' => s.empty_q <+: v ∧
                    (∃ q, RegOutG kq su default (GateOK P pw Rr Rc s.clk s.crn) s.clk
                            (fun u => (s.d.getD u default).st) s.d.length s.horizon q ∧
                          v = q.map (fun st => st.empty)) ∧
                    s' = { s with empty_q := v }⟩)
               , (↑"gray", ⟨List (BitVec (n+1)), fun s v s' => s.gray_q <+: v ∧
                    BusRegOutG kq su (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).gnext) s.d.length s.horizon v ∧
                    s' = { s with gray_q := v }⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], [], []⟩ }

end Spec

end Graphiti.AsyncFifo.ReadBank
