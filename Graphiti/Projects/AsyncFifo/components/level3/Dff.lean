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

/-!
# The edge-triggered D flip-flop, as gates

This is the first stateful block built from gates: the classic six-NAND positive-edge-triggered
flip-flop, with the asynchronous clear of the 7474 and one more gate on its output.  Its topology is
Kobler's (`CombinationalStream.lean`).

    n1 = nand n4 n2       n2 = nand3 n1 clk clrn    n3 = nand3 n2 clk n4
    n4 = nand3 n3 d clrn  n5 = nand n2 n6           n6 = nand3 n5 n3 clrn
                          q  = and n5 clrn

`clrn` is the active-low clear: while it is low it forces `n2`, `n4` and `n6` high, hence `n5`
low.  It is not decoration.  Every wire of a netlist of these gates is low at instant `0`,
because a gate that has not computed yet emits `false`; and from the all-low state with a low
clock this circuit *oscillates for ever* (`q` alternates), because the cross-coupled pair
`n5`/`n6` powers up in the state a latch may not be in.  So without a clear there is no instant
at which the flip-flop holds a defined value, and no netlist of gates can meet a contract that
pins its output before the first edge.  Cummings' FIFO has `wrst_n`/`rrst_n` for exactly this
reason; the register-level model hid it in `init_state`.

The clear also gates the output, `q = and n5 clrn`, which is why there are seven gates rather
than six.  Without it the output would still be wrong at instant `1`: at instant `0` every wire
is low, so at instant `1` the output NAND reads `nand false false = true`, whatever the circuit
and however long the clear is asserted.  `RegOut` pins the output before the first edge, so it
would be unsatisfiable by any netlist of these gates.  One AND gate per bit buys that away, at
the cost of one instant of clock-to-q.

The netlist ends in `Gates.cut3`, which reports the output only as far as the block's own
inputs are known, plus the one instant a Moore block is entitled to: what the block reports is
then a function of what it was given.

`dffImpl` is the netlist and `dffSpec` the flip-flop it behaves as: an edge-triggered register
with a clear, as a Moore machine.  `Dff.impl_refines : dffImpl ⊑ dffSpec` (`TopRefinement.lean`)
is this component's theorem; how the feedback loop is solved is in `ProofWriteOnly/Dff.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.Dff

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates

/-! ### The gates of the netlist -/

def nand2 (a b : Bool) : Bool := !(a && b)
def nand3 (a b c : Bool) : Bool := !(a && b && c)
def and2 (a b : Bool) : Bool := a && b

/-! ### The netlist -/

def dffGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    q [type="io"];

    clkf [type="fork3", typeImp=$(⟨_, fork3⟩)];
    df [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    crf [type="fork5", typeImp=$(⟨_, fork5⟩)];
    n1 [type="nand2", typeImp=$(⟨_, gate2 nand2⟩)];
    n2 [type="nand3", typeImp=$(⟨_, gate3 nand3⟩)];
    n2f [type="fork3", typeImp=$(⟨_, fork3⟩)];
    n3 [type="nand3", typeImp=$(⟨_, gate3 nand3⟩)];
    n3f [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    n4 [type="nand3", typeImp=$(⟨_, gate3 nand3⟩)];
    n4f [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    n5 [type="nand2", typeImp=$(⟨_, gate2 nand2⟩)];
    n5f [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    n6 [type="nand3", typeImp=$(⟨_, gate3 nand3⟩)];
    qf [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    cut [type="cut3", typeImp=$(⟨_, cut3⟩)];

    clk -> clkf [to="in"];
    d -> df [to="in"];
    clrn -> crf [to="in"];

    clkf -> n2 [from="out1", to="b"];
    clkf -> n3 [from="out2", to="b"];
    clkf -> cut [from="out3", to="r1"];
    df -> n4 [from="out1", to="b"];
    df -> cut [from="out2", to="r2"];
    crf -> n2 [from="out1", to="c"];
    crf -> n4 [from="out2", to="c"];
    crf -> n6 [from="out3", to="c"];
    crf -> qf [from="out4", to="b"];
    crf -> cut [from="out5", to="r3"];
    n4f -> n1 [from="out1", to="a"];
    n2f -> n1 [from="out1", to="b"];
    n1 -> n2 [from="out", to="a"];
    n2 -> n2f [from="out", to="in"];
    n2f -> n3 [from="out2", to="a"];
    n4f -> n3 [from="out2", to="c"];
    n3 -> n3f [from="out", to="in"];
    n3f -> n4 [from="out1", to="a"];
    n4 -> n4f [from="out", to="in"];
    n2f -> n5 [from="out3", to="a"];
    n6 -> n5 [from="out", to="b"];
    n5 -> n5f [from="out", to="in"];
    n5f -> n6 [from="out1", to="a"];
    n3f -> n6 [from="out2", to="b"];
    n5f -> qf [from="out2", to="a"];
    qf -> cut [from="out", to="in"];

    cut -> q [from="out"];
  ]

@[drunfold_defs]
def dffLowered := dffGraph.1.lower_TR |>.get rfl

def denv := dffGraph.2

/-- **The flip-flop, as gates.** -/
def dffImpl := [e| dffLowered, denv.find? ]

/-! ### The wires as the run of a six-bit automaton -/

/-- The value of the six gate outputs at one instant. -/
structure DffSt where
  n1 : Bool
  n2 : Bool
  n3 : Bool
  n4 : Bool
  n5 : Bool
  n6 : Bool
deriving DecidableEq, Repr

/-- Every gate recomputes from the values of the previous instant: one tick of delay each.
The input is `(clk, d, clrn)`. -/
def dffStep (s : DffSt) (i : Bool × Bool × Bool) : DffSt :=
  ⟨nand2 s.n4 s.n2, nand3 s.n1 i.1 i.2.2, nand3 s.n2 i.1 s.n4,
   nand3 s.n3 i.2.1 i.2.2, nand2 s.n2 s.n6, nand3 s.n5 s.n3 i.2.2⟩

/-- Every wire of a netlist of these gates is low before anything has propagated. -/
def DffSt.init : DffSt := ⟨false, false, false, false, false, false⟩

def dffInp (clk d crn : List Bool) (t : Nat) : Bool × Bool × Bool :=
  (clk.getD t false, d.getD t false, crn.getD t false)

def dffRun (clk d crn : List Bool) (t : Nat) : DffSt :=
  run dffStep DffSt.init (dffInp clk d crn) t

/-- How far the block's inputs are known. -/
def dffLen (clk d crn : List Bool) : Nat := min (min clk.length d.length) crn.length

/-- The flip-flop's output at one instant: the wire `n5` one instant earlier, gated by the
clear.  The gate costs one instant of clock-to-q and buys a defined output from instant `0`
(see the header). -/
def qAt (clk d crn : List Bool) (t : Nat) : Bool :=
  match t with
  | 0 => false
  | t + 1 => and2 (dffRun clk d crn t).n5 (crn.getD t false)

/-- What the block reports: the output wire, as far as its inputs are known plus the one
instant a Moore block may report. -/
def dffOut (clk d crn : List Bool) : List Bool :=
  timeline (qAt clk d crn) (dffLen clk d crn + 1)

/-! ### The specification -/

/-- The flip-flop as a single block: it stores its three inputs, and its output is a prefix of
the stream the automaton gives.  `DffTiming.lean` proves the register contract from this. -/
@[drcomponents]
def dffSpec : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s' = s ∧ v <+: dffOut s.1 s.2.1 s.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

end Graphiti.AsyncFifo.Dff
