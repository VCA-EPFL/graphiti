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
# One cell of the register file: a flip-flop that holds

A memory cell captures its data when it is written to and keeps it otherwise, so its flip-flop
is fed by a multiplexer that reads the flip-flop's own output:

    nen = not en        t1 = en and data      t2 = nen and q
    m   = t1 or t2      (and the flip-flop of `Dff.lean` with `d := m`)

The flip-flop is a node of this graph --- `Dff.dffSpec`, the flip-flop's specification --- and
the loop closes through it.  A loop is no obstacle: the flip-flop, like a gate, emits one instant
past its shortest input, and that instant is what lets a stream go round a cycle at all.  Eleven
nodes and sixteen connections, against the twenty-one and thirty-five a flat netlist needs.

The clock gating that would avoid the loop -- `clk and en` into the flip-flop -- is not used
here.  It needs the enable to be stable over the whole high phase of the clock, and the write
side only promises a setup window (`CleanWrites`), so a late change of the enable could forge a
second edge.  That is a real hazard, which is why clock gaters are latch-based.

`EnReg.impl_refines : enImpl ⊑ enSpec`; how the cell's behaviour is computed across the loop
is in `ProofWriteOnly/EnReg.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.EnReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Dff

/-! ### The gates of the multiplexer -/

def or2 (a b : Bool) : Bool := a || b

/-! ### The netlist

The flip-flop is a *node*, not a copy of its gates.  The loop is no obstacle: `dffOut` is a
`timeline` of length `dffLen + 1`, so the flip-flop as a block emits one instant past its
shortest input exactly as a gate does, and that instant is what lets a stream go round a
cycle. -/

def enGraph := [graphEnv|
    clk [type="io"];
    en [type="io"];
    data [type="io"];
    clrn [type="io"];
    q [type="io"];

    clkf  [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    crf   [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    enf   [type="fork3", typeImp=$(⟨_, fork3⟩)];
    dataf [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    nen   [type="not1",  typeImp=$(⟨_, gate1 not⟩)];
    t1    [type="and2",  typeImp=$(⟨_, gate2 and2⟩)];
    t2    [type="and2",  typeImp=$(⟨_, gate2 and2⟩)];
    mx    [type="or2",   typeImp=$(⟨_, gate2 or2⟩)];
    ff    [type="dff",   typeImp=$(⟨_, dffSpec⟩)];
    qf    [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    cut   [type="cut4",  typeImp=$(⟨_, cut4⟩)];

    clk -> clkf [to="in"];
    en -> enf [to="in"];
    data -> dataf [to="in"];
    clrn -> crf [to="in"];

    enf -> nen [from="out1", to="a"];
    enf -> t1 [from="out2", to="a"];
    enf -> cut [from="out3", to="r2"];
    dataf -> t1 [from="out1", to="b"];
    dataf -> cut [from="out2", to="r3"];
    nen -> t2 [from="out", to="a"];
    qf -> t2 [from="out1", to="b"];
    t1 -> mx [from="out", to="a"];
    t2 -> mx [from="out", to="b"];
    mx -> ff [from="out", to="d"];
    clkf -> ff [from="out1", to="clk"];
    clkf -> cut [from="out2", to="r1"];
    crf -> ff [from="out1", to="clrn"];
    crf -> cut [from="out2", to="r4"];
    ff -> qf [from="q", to="in"];
    qf -> cut [from="out2", to="in"];

    cut -> q [from="out"];
  ]

@[drunfold_defs]
def enLowered := enGraph.1.lower_TR |>.get rfl

/-- What each node of the graph is: the gates and forks of the multiplexer, the cut, and for the flip-flop its specification
`Dff.dffSpec`. -/
def eenv := enGraph.2

/-- **The memory cell**: the graph, each child standing for its specification. -/
def enImpl := [e| enLowered, eenv.find? ]

/-! ### The wires as the run of an eleven-bit automaton -/

/-- The value of the eleven gate outputs at one instant: the flip-flop's six, the four of the
multiplexer, and the cell's output. -/
structure EnSt where
  n1 : Bool
  n2 : Bool
  n3 : Bool
  n4 : Bool
  n5 : Bool
  n6 : Bool
  nen : Bool
  t1 : Bool
  t2 : Bool
  m : Bool
  q : Bool
deriving DecidableEq, Repr

/-- Every gate recomputes from the values of the previous instant.  The flip-flop's `d` input is
the multiplexer's wire, and the multiplexer reads the cell's own output. -/
def enStep (s : EnSt) (i : Bool × Bool × Bool × Bool) : EnSt :=
  ⟨nand2 s.n4 s.n2, nand3 s.n1 i.1 i.2.2.2, nand3 s.n2 i.1 s.n4,
   nand3 s.n3 s.m i.2.2.2, nand2 s.n2 s.n6, nand3 s.n5 s.n3 i.2.2.2,
   not i.2.1, and2 i.2.1 i.2.2.1, and2 s.nen s.q, or2 s.t1 s.t2, and2 s.n5 i.2.2.2⟩

def EnSt.init : EnSt := ⟨false, false, false, false, false, false, false, false, false, false, false⟩

def enInp (clk en dat crn : List Bool) (t : Nat) : Bool × Bool × Bool × Bool :=
  (clk.getD t false, en.getD t false, dat.getD t false, crn.getD t false)

def enRun (clk en dat crn : List Bool) (t : Nat) : EnSt :=
  run enStep EnSt.init (enInp clk en dat crn) t

/-- How far the cell's inputs are known. -/
def enLen (clk en dat crn : List Bool) : Nat :=
  min (min clk.length en.length) (min dat.length crn.length)

/-- What the cell reports: its output wire, as far as its inputs are known plus the one instant
a Moore block may report. -/
def enOut (clk en dat crn : List Bool) : List Bool :=
  timeline (fun t => (enRun clk en dat crn t).q) (enLen clk en dat crn + 1)

/-! ### The specification -/

/-- The cell as a single block: it stores its four inputs, and its output is a prefix of the
stream the automaton gives. -/
@[drcomponents]
def enSpec : StringModule (List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"en", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"data", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.2 ⊏ v ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s' = s ∧ v <+: enOut s.1 s.2.1 s.2.2.1 s.2.2.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

end Graphiti.AsyncFifo.EnReg
