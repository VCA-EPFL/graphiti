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
import Graphiti.Projects.AsyncFifo.components.level4.BusReg
import Graphiti.Projects.AsyncFifo.components.level4.WriteState
import Graphiti.Projects.AsyncFifo.components.level5.RegFile

/-!
# The write domain's register bank

The write domain's state: a seven-bit state register, the three-bit Gray
pointer that crosses into the read domain, the `full` flag (a projection of the state), and the
four-entry register file.  This file wires the three blocks together --- each as its specification --- and unpacks the
next-state bus that feeds them.  `bankSpec` is the bank's timed contract, and
`WriteBank.impl_refines` (`TopRefinement.lean`) the proof that the implementation meets it.

The bank has one port the register-level model does not: the clear.  That is the finding of
`Dff.lean` working its way up -- a netlist of gates has no defined state until something puts
it there -- and it is why the write domain, and in the end the FIFO, need a reset input of
their own.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.WriteBank

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts
  Graphiti.AsyncFifo.Dff

/-! ### The next-state bus and its fields -/

def stOf (d : List (WNext Bool 2)) : List (WSt 2) := d.map (·.st)
def gnextOf (d : List (WNext Bool 2)) : List (BitVec 3) := d.map (·.gnext)
def weOf (d : List (WNext Bool 2)) : List Bool := d.map (·.we)
def addrOf (d : List (WNext Bool 2)) : List (BitVec 2) := d.map (·.addr)
def dataOf (d : List (WNext Bool 2)) : List Bool := d.map (·.data)

/-- Split the next-state bus into the five streams the bank's blocks read. -/
@[drcomponents]
def unpackNext : StringModule (List (WNext Bool 2)) :=
  { inputs := [ (↑"d", ⟨List (WNext Bool 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"st", ⟨List (WSt 2), fun s v s' => s' = s ∧ v = stOf s⟩)
               , (↑"gnext", ⟨List (BitVec 3), fun s v s' => s' = s ∧ v = gnextOf s⟩)
               , (↑"we", ⟨List Bool, fun s v s' => s' = s ∧ v = weOf s⟩)
               , (↑"addr", ⟨List (BitVec 2), fun s v s' => s' = s ∧ v = addrOf s⟩)
               , (↑"data", ⟨List Bool, fun s v s' => s' = s ∧ v = dataOf s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The `full` flag is a bit of the state register. -/
@[drcomponents]
def fullOf : StringModule (List (WSt 2)) :=
  { inputs := [ (↑"q", ⟨List (WSt 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"full", ⟨List Bool, fun s v s' => s' = s ∧ v = s.map (·.full)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-! ### The netlist -/

def bankGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    st [type="io"];
    full [type="io"];
    gray [type="io"];
    mem [type="io"];

    unpN [type="unpackNext", typeImp=$(⟨_, unpackNext⟩)];
    clkF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    crF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    stR [type="streg", typeImp=$(⟨_, WriteState.stSpec⟩)];
    stF [type="forkSt", typeImp=$(⟨_, fork2 (WSt 2)⟩)];
    fullA [type="fullOf", typeImp=$(⟨_, fullOf⟩)];
    grR [type="busreg", typeImp=$(⟨_, BusReg.busSpec⟩)];
    memB [type="memory", typeImp=$(⟨_, RegFile.memSpec⟩)];

    clk -> clkF [to="in"];
    d -> unpN [to="d"];
    clrn -> crF [to="in"];

    clkF -> stR [from="out1", to="clk"];
    clkF -> grR [from="out2", to="clk"];
    clkF -> memB [from="out3", to="clk"];
    crF -> stR [from="out1", to="clrn"];
    crF -> grR [from="out2", to="clrn"];
    crF -> memB [from="out3", to="clrn"];
    unpN -> stR [from="st", to="d"];
    unpN -> grR [from="gnext", to="d"];
    unpN -> memB [from="we", to="we"];
    unpN -> memB [from="addr", to="addr"];
    unpN -> memB [from="data", to="data"];
    stR -> stF [from="q", to="in"];
    stF -> fullA [from="out2", to="q"];

    stF -> st [from="out1"];
    fullA -> full [from="full"];
    grR -> gray [from="q"];
    memB -> mem [from="mem"];
  ]

@[drunfold_defs]
def bankLowered := bankGraph.1.lower_TR |>.get rfl

/-- What each node of the graph is: the splitter and forks, and the state register, the Gray-pointer register and the register file
by their specifications. -/
def kenv := bankGraph.2

/-- **The write domain's register bank**: the graph, each child standing for its specification. -/
def bankImpl := [e| bankLowered, kenv.find? ]

section Spec
variable {n : Nat}
variable (α : Type) [Inhabited α]

/-- State of the register bank: the clock, the next-state bus, the clear, and the four emitted
outputs. -/
structure RegSt (α : Type) (n : Nat) where
  clk : List Bool
  d : List (WNext α n)
  crn : List Bool
  st_q : List (WSt n)
  full_q : List Bool
  gray_q : List (BitVec (n+1))
  mem_q : List (BitVec n → α)

/-- How far the bank's inputs are known: its clock, its bus and its clear. -/
def RegSt.horizon (s : RegSt α n) : Nat := min (min s.clk.length s.d.length) s.crn.length

/-- The register bank of the write domain, clocked by `clk`, loaded from the next-state bus
`d`, and cleared by `clrn`.  Each output has its own contract: the state (`RegOut`), the `full`
flag (a projection of the state register), the Gray pointer register that crosses into the
other domain (`BusRegOut`, glitch-free window) and the memory (`MemOut`, one window per written
entry).  Each binds only at the instants where the clock and the clear have behaved
(`GateOK P pw Rr Rc`), because that is all a netlist of gates can promise; the register level
gets the unguarded contracts back by taking the guard to be trivially true. -/
@[drcomponents]
def bankSpec (kq su P pw Rr Rc : Nat) : StringModule (RegSt α n) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.clk ⊏ v ∧ s' = { s with clk := v }⟩)
              , (↑"d", ⟨List (WNext α n), fun s v s' => s.d ⊏ v ∧ s' = { s with d := v }⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.crn ⊏ v ∧ s' = { s with crn := v }⟩)
              ].toAssocList
    outputs := [ (↑"st", ⟨List (WSt n), fun s v s' => s.st_q <+: v ∧
                    RegOutG kq su default (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).st) s.d.length s.horizon v ∧
                    s' = { s with st_q := v }⟩)
               , (↑"full", ⟨List Bool, fun s v s' => s.full_q <+: v ∧
                    (∃ q, RegOutG kq su default (GateOK P pw Rr Rc s.clk s.crn) s.clk
                            (fun u => (s.d.getD u default).st) s.d.length s.horizon q ∧
                          v = q.map (fun st => st.full)) ∧
                    s' = { s with full_q := v }⟩)
               , (↑"gray", ⟨List (BitVec (n+1)), fun s v s' => s.gray_q <+: v ∧
                    BusRegOutG kq su (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).gnext) s.d.length s.horizon v ∧
                    s' = { s with gray_q := v }⟩)
               , (↑"mem", ⟨List (BitVec n → α), fun s v s' => s.mem_q <+: v ∧
                    MemOutG kq su (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).we) (fun u => (s.d.getD u default).addr)
                      (fun u => (s.d.getD u default).data) s.d.length s.horizon v ∧
                    s' = { s with mem_q := v }⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], [], [], []⟩ }

end Spec

end Graphiti.AsyncFifo.WriteBank
