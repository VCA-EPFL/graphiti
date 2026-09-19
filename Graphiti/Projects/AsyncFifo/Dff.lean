/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.Gates

/-!
# The edge-triggered D flip-flop as gates

This is the first stateful block built from gates: the classic six-NAND positive-edge-triggered
flip-flop, with the asynchronous clear of the 7474 and one more gate on its output.  Its
topology, the idea of describing it by a six-bit automaton, and the shape of the invariant are
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

Because the netlist has feedback, its wires are not functions of the inputs one gate at a time:
they are the fixpoint that the framework's connection rules compute incrementally, which is the
loop story of Kobler's report.  `dffRun` gives that fixpoint directly as the run of a six-bit
automaton, one step per instant.  Two things make that work, and both are hers:

* the gates of `Gates.lean` emit one instant past their inputs (`delay false`), without which
  no stream could ever enter a loop -- a gate whose output stopped at its shortest input would
  wait for the gate before it, for ever;
* the invariant `Wf` is *structural*: it says only that each node holds a prefix of what drives
  it.  No instant, no horizon, no automaton appears in it, so a growth of the block's inputs
  costs one `trans` per field.  The correspondence with the run (`wf_sim`) is derived from it
  by one induction on the instant, where it is needed: at the output.

What differs from her development is the boundary.  Her flip-flop reports every instant its
gates computed, which runs past the inputs that justify it, and her specification absorbs that
with a `future_sight` buffer of arbitrary values -- values a feedback loop could not consume.
Here the netlist ends in `Gates.cut3`, which reports the output only as far as the block's own
inputs are known, plus the one instant a Moore block is entitled to.  What the block reports is
then a function of what it was given, which is what the contracts of `Timed.lean` ask for.
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
    df [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    crf [type="fork5", typeImp=$(⟨_, fork5⟩)];
    n1 [type="nand2", typeImp=$(⟨_, gate2 nand2⟩)];
    n2 [type="nand3", typeImp=$(⟨_, gate3 nand3⟩)];
    n2f [type="fork3", typeImp=$(⟨_, fork3⟩)];
    n3 [type="nand3", typeImp=$(⟨_, gate3 nand3⟩)];
    n3f [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    n4 [type="nand3", typeImp=$(⟨_, gate3 nand3⟩)];
    n4f [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    n5 [type="nand2", typeImp=$(⟨_, gate2 nand2⟩)];
    n5f [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
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

@[drenv] theorem denv_fork2 : denv.find? "fork2" = .some ⟨_, Timed.fork2 Bool⟩ := rfl
@[drenv] theorem denv_fork3 : denv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem denv_fork5 : denv.find? "fork5" = .some ⟨_, fork5⟩ := rfl
@[drenv] theorem denv_and2 : denv.find? "and2" = .some ⟨_, gate2 and2⟩ := rfl
@[drenv] theorem denv_cut3 : denv.find? "cut3" = .some ⟨_, cut3⟩ := rfl
@[drenv] theorem denv_nand2 : denv.find? "nand2" = .some ⟨_, gate2 nand2⟩ := rfl
@[drenv] theorem denv_nand3 : denv.find? "nand3" = .some ⟨_, gate3 nand3⟩ := rfl

seal denv in
def_module dffT : Type :=
  [T| dffLowered, denv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal denv in
def_module dffNetlist : StringModule dffT :=
  [e| dffLowered, denv.find? ]

-- HEADER_END (everything below is generated by gen/gen_dff.py)

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

instance : Inhabited DffSt := ⟨⟨false, false, false, false, false, false⟩⟩

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

theorem dffLen_le_clk (clk d crn : List Bool) : dffLen clk d crn ≤ clk.length := by
  unfold dffLen; omega

theorem dffLen_le_d (clk d crn : List Bool) : dffLen clk d crn ≤ d.length := by
  unfold dffLen; omega

theorem dffLen_le_crn (clk d crn : List Bool) : dffLen clk d crn ≤ crn.length := by
  unfold dffLen; omega

theorem dffRun_congr {clk clk' d d' crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d')
    (hr : crn <+: crn') {t : Nat} (ht : t ≤ dffLen clk d crn) :
    dffRun clk d crn t = dffRun clk' d' crn' t := by
  refine run_congr _ _ (fun u hu => ?_) t ht
  unfold dffLen at hu
  unfold dffInp
  rw [hc.getD_eq_left (by omega), hd.getD_eq_left (by omega), hr.getD_eq_left (by omega)]

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

@[simp] theorem dffOut_length (clk d crn : List Bool) :
    (dffOut clk d crn).length = dffLen clk d crn + 1 := timeline_length _ _

theorem dffOut_getD (clk d crn : List Bool) {t : Nat} (ht : t < dffLen clk d crn + 1) :
    (dffOut clk d crn).getD t false = qAt clk d crn t := timeline_getD _ ht _

theorem dffOut_mono {clk clk' d d' crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d')
    (hr : crn <+: crn') : dffOut clk d crn <+: dffOut clk' d' crn' := by
  have := hc.length_le; have := hd.length_le; have := hr.length_le
  apply timeline_mono (by unfold dffLen; omega)
  intro t ht
  match t with
  | 0 => rfl
  | u + 1 =>
    simp only [dffLen] at ht
    show and2 _ _ = and2 _ _
    rw [dffRun_congr hc hd hr (by unfold dffLen; omega), hr.getD_eq_left (by omega)]

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

instance : MatchInterface dffNetlist dffSpec := by
  dsimp [dffNetlist, dffSpec]
  solve_match_interface

/-! ### The invariant

Every node holds a prefix of what drives it, and the three nodes fed by the block's inputs hold
exactly what the specification stores.  That is all: no instant, no horizon, no automaton -- so
a growth of the inputs costs one `trans` per field. -/

structure Wf (n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 : List Bool) (s : List Bool × List Bool × List Bool) : Prop where
  e_clk : clkf_in = s.1
  e_d : df_in = s.2.1
  e_crn : crf_in = s.2.2
  w_n2_a : n2_a <+: gateOut nand2 n1_a n1_b
  w_n2_b : n2_b <+: clkf_in
  w_n2_c : n2_c <+: crf_in
  w_n5f_in : n5f_in <+: gateOut nand2 n5_a n5_b
  w_qf_a : qf_a <+: n5f_in
  w_qf_b : qf_b <+: crf_in
  w_n6_a : n6_a <+: n5f_in
  w_n6_b : n6_b <+: n3f_in
  w_n6_c : n6_c <+: crf_in
  w_n5_a : n5_a <+: n2f_in
  w_n5_b : n5_b <+: gate3Out nand3 n6_a n6_b n6_c
  w_n4_a : n4_a <+: n3f_in
  w_n4_b : n4_b <+: df_in
  w_n4_c : n4_c <+: crf_in
  w_n4f_in : n4f_in <+: gate3Out nand3 n4_a n4_b n4_c
  w_n3_a : n3_a <+: n2f_in
  w_n3_b : n3_b <+: clkf_in
  w_n3_c : n3_c <+: n4f_in
  w_n1_a : n1_a <+: n4f_in
  w_n1_b : n1_b <+: n2f_in
  w_n3f_in : n3f_in <+: gate3Out nand3 n3_a n3_b n3_c
  w_n2f_in : n2f_in <+: gate3Out nand3 n2_a n2_b n2_c
  w_cut_in : cut_in <+: gateOut and2 qf_a qf_b
  w_cut_r1 : cut_r1 <+: clkf_in
  w_cut_r2 : cut_r2 <+: df_in
  w_cut_r3 : cut_r3 <+: crf_in

def ψ (i : dffT) (s : List Bool × List Bool × List Bool) : Prop :=
  Wf i.1.1 i.1.2.1 i.1.2.2 i.2.1 i.2.2.1 i.2.2.2.1.1 i.2.2.2.1.2 i.2.2.2.2.1 i.2.2.2.2.2.1.1 i.2.2.2.2.2.1.2.1 i.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 s

theorem Wf.init : Wf [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] ([], [], []) :=
  ⟨rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩

section SpecRules
variable (sp : List Bool × List Bool × List Bool)

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (dffSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List Bool) (h : sp.2.1 ⊏ v) :
    (dffSpec.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2 ⊏ v) :
    (dffSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List Bool) (h : v <+: dffOut sp.1 sp.2.1 sp.2.2) :
    (dffSpec.outputs.getIO ↑"q").2 sp v sp := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨rfl, h⟩
end SpecRules

section Cases
variable {n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 : List Bool} {sp : List Bool × List Bool × List Bool}
  (Hψ : Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp)
include Hψ

theorem in_clk (v : List Bool) (h : clkf_in ⊏ v) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in (v) n2f_in cut_in cut_r1 cut_r2 cut_r3 (v, sp.2) := by
  have hm : clkf_in <+: v := h.isPrefix
  exact { e_clk := rfl
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b.trans hm
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b.trans hm
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1.trans hm
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem in_d (v : List Bool) (h : df_in ⊏ v) :
    Wf n2_a n2_b n2_c n5f_in (v) qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 (sp.1, v, sp.2.2) := by
  have hm : df_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := rfl
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b.trans hm
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2.trans hm
          w_cut_r3 := Hψ.w_cut_r3 }

theorem in_clrn (v : List Bool) (h : crf_in ⊏ v) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b (v) n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 (sp.1, sp.2.1, v) := by
  have hm : crf_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := rfl
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c.trans hm
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b.trans hm
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c.trans hm
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c.trans hm
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3.trans hm }

theorem int_0 (_h : n2_b ⊏ clkf_in) :
    Wf n2_a (clkf_in) n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := List.prefix_rfl
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in.trans (gate3Out_mono _ List.prefix_rfl Hψ.w_n2_b List.prefix_rfl)
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_1 (_h : n3_b ⊏ clkf_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a (clkf_in) n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := List.prefix_rfl
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in.trans (gate3Out_mono _ List.prefix_rfl Hψ.w_n3_b List.prefix_rfl)
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_2 (_h : cut_r1 ⊏ clkf_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in (clkf_in) cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := List.prefix_rfl
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_3 (_h : n4_b ⊏ df_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a (df_in) n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := List.prefix_rfl
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in.trans (gate3Out_mono _ List.prefix_rfl Hψ.w_n4_b List.prefix_rfl)
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_4 (_h : cut_r2 ⊏ df_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 (df_in) cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := List.prefix_rfl
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_5 (_h : n2_c ⊏ crf_in) :
    Wf n2_a n2_b (crf_in) n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := List.prefix_rfl
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in.trans (gate3Out_mono _ List.prefix_rfl List.prefix_rfl Hψ.w_n2_c)
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_6 (_h : n4_c ⊏ crf_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b (crf_in) n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := List.prefix_rfl
          w_n4f_in := Hψ.w_n4f_in.trans (gate3Out_mono _ List.prefix_rfl List.prefix_rfl Hψ.w_n4_c)
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_7 (_h : n6_c ⊏ crf_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b (crf_in) n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := List.prefix_rfl
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b.trans (gate3Out_mono _ List.prefix_rfl List.prefix_rfl Hψ.w_n6_c)
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_8 (_h : qf_b ⊏ crf_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a (crf_in) crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := List.prefix_rfl
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in.trans (gateOut_mono _ List.prefix_rfl Hψ.w_qf_b)
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_9 (_h : cut_r3 ⊏ crf_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 (crf_in) sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := List.prefix_rfl }

theorem int_10 (_h : n1_a ⊏ n4f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c (n4f_in) n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a.trans (gateOut_mono _ Hψ.w_n1_a List.prefix_rfl)
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := List.prefix_rfl
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_11 (_h : n1_b ⊏ n2f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a (n2f_in) n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_n1_b)
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := List.prefix_rfl
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_12 (_h : n2_a ⊏ gateOut nand2 n1_a n1_b) :
    Wf (gateOut nand2 n1_a n1_b) n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := List.prefix_rfl
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in.trans (gate3Out_mono _ Hψ.w_n2_a List.prefix_rfl List.prefix_rfl)
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_13 (_h : n2f_in ⊏ gate3Out nand3 n2_a n2_b n2_c) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in (gate3Out nand3 n2_a n2_b n2_c) cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a.trans Hψ.w_n2f_in
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a.trans Hψ.w_n2f_in
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b.trans Hψ.w_n2f_in
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := List.prefix_rfl
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_14 (_h : n3_a ⊏ n2f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in (n2f_in) n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := List.prefix_rfl
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in.trans (gate3Out_mono _ Hψ.w_n3_a List.prefix_rfl List.prefix_rfl)
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_15 (_h : n3_c ⊏ n4f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b (n4f_in) n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := List.prefix_rfl
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in.trans (gate3Out_mono _ List.prefix_rfl List.prefix_rfl Hψ.w_n3_c)
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_16 (_h : n3f_in ⊏ gate3Out nand3 n3_a n3_b n3_c) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b (gate3Out nand3 n3_a n3_b n3_c) clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b.trans Hψ.w_n3f_in
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a.trans Hψ.w_n3f_in
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := List.prefix_rfl
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_17 (_h : n4_a ⊏ n3f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b (n3f_in) n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := List.prefix_rfl
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in.trans (gate3Out_mono _ Hψ.w_n4_a List.prefix_rfl List.prefix_rfl)
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_18 (_h : n4f_in ⊏ gate3Out nand3 n4_a n4_b n4_c) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c (gate3Out nand3 n4_a n4_b n4_c) n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := List.prefix_rfl
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c.trans Hψ.w_n4f_in
          w_n1_a := Hψ.w_n1_a.trans Hψ.w_n4f_in
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_19 (_h : n5_a ⊏ n2f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c (n2f_in) n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in.trans (gateOut_mono _ Hψ.w_n5_a List.prefix_rfl)
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := List.prefix_rfl
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_20 (_h : n5_b ⊏ gate3Out nand3 n6_a n6_b n6_c) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a (gate3Out nand3 n6_a n6_b n6_c) n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in.trans (gateOut_mono _ List.prefix_rfl Hψ.w_n5_b)
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := List.prefix_rfl
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_21 (_h : n5f_in ⊏ gateOut nand2 n5_a n5_b) :
    Wf n2_a n2_b n2_c (gateOut nand2 n5_a n5_b) df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := List.prefix_rfl
          w_qf_a := Hψ.w_qf_a.trans Hψ.w_n5f_in
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a.trans Hψ.w_n5f_in
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_22 (_h : n6_a ⊏ n5f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in (n5f_in) n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := List.prefix_rfl
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b.trans (gate3Out_mono _ Hψ.w_n6_a List.prefix_rfl List.prefix_rfl)
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_23 (_h : n6_b ⊏ n3f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a (n3f_in) n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := List.prefix_rfl
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b.trans (gate3Out_mono _ List.prefix_rfl Hψ.w_n6_b List.prefix_rfl)
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_24 (_h : qf_a ⊏ n5f_in) :
    Wf n2_a n2_b n2_c n5f_in df_in (n5f_in) qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := List.prefix_rfl
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in.trans (gateOut_mono _ Hψ.w_qf_a List.prefix_rfl)
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

theorem int_25 (_h : cut_in ⊏ gateOut and2 qf_a qf_b) :
    Wf n2_a n2_b n2_c n5f_in df_in qf_a qf_b crf_in n6_a n6_b n6_c n5_a n5_b n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in clkf_in n2f_in (gateOut and2 qf_a qf_b) cut_r1 cut_r2 cut_r3 sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qf_a := Hψ.w_qf_a
          w_qf_b := Hψ.w_qf_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := List.prefix_rfl
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3 }

/-- **The nodes agree with the automaton.**  This is where the netlist's feedback is
resolved: the structural invariant says only that each node holds a prefix of what drives it,
and one induction on the instant turns that into the values of the run.  Nothing here needs a
horizon -- a node only ever holds values its own inputs justify. -/
theorem wf_sim : ∀ t,
    (t < n2_a.length → n2_a.getD t false = (dffRun sp.1 sp.2.1 sp.2.2 t).n1) ∧
    (t < n2f_in.length → n2f_in.getD t false = (dffRun sp.1 sp.2.1 sp.2.2 t).n2) ∧
    (t < n3f_in.length → n3f_in.getD t false = (dffRun sp.1 sp.2.1 sp.2.2 t).n3) ∧
    (t < n4f_in.length → n4f_in.getD t false = (dffRun sp.1 sp.2.1 sp.2.2 t).n4) ∧
    (t < n5f_in.length → n5f_in.getD t false = (dffRun sp.1 sp.2.1 sp.2.2 t).n5) ∧
    (t < n5_b.length → n5_b.getD t false = (dffRun sp.1 sp.2.1 sp.2.2 t).n6) ∧
    (t < cut_in.length → cut_in.getD t false = qAt sp.1 sp.2.1 sp.2.2 t) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
    · rw [Hψ.w_n2_a.getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [Hψ.w_n2f_in.getD_eq_left hl, gate3Out_getD_zero]
      rfl
    · rw [Hψ.w_n3f_in.getD_eq_left hl, gate3Out_getD_zero]
      rfl
    · rw [Hψ.w_n4f_in.getD_eq_left hl, gate3Out_getD_zero]
      rfl
    · rw [Hψ.w_n5f_in.getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [Hψ.w_n5_b.getD_eq_left hl, gate3Out_getD_zero]
      rfl
    · rw [Hψ.w_cut_in.getD_eq_left hl, gateOut_getD_zero]
      rfl
  | succ t ih =>
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
    · have l0 := Hψ.w_n2_a.length_le
      simp only [gateOut_length] at l0
      have l_n1_a := Hψ.w_n1_a.length_le
      have l_n1_b := Hψ.w_n1_b.length_le
      rw [Hψ.w_n2_a.getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_n1_a.getD_eq_left (by omega), ih.2.2.2.1 (by omega), Hψ.w_n1_b.getD_eq_left (by omega), ih.2.1 (by omega)]
      rfl
    · have l0 := Hψ.w_n2f_in.length_le
      simp only [gate3Out_length] at l0
      have l_n2_b := Hψ.w_n2_b.length_le
      have l_n2_c := Hψ.w_n2_c.length_le
      rw [Hψ.w_n2f_in.getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, ih.1 (by omega), Hψ.w_n2_b.getD_eq_left (by omega), Hψ.e_clk, Hψ.w_n2_c.getD_eq_left (by omega), Hψ.e_crn]
      rfl
    · have l0 := Hψ.w_n3f_in.length_le
      simp only [gate3Out_length] at l0
      have l_n3_a := Hψ.w_n3_a.length_le
      have l_n3_b := Hψ.w_n3_b.length_le
      have l_n3_c := Hψ.w_n3_c.length_le
      rw [Hψ.w_n3f_in.getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_n3_a.getD_eq_left (by omega), ih.2.1 (by omega), Hψ.w_n3_b.getD_eq_left (by omega), Hψ.e_clk, Hψ.w_n3_c.getD_eq_left (by omega), ih.2.2.2.1 (by omega)]
      rfl
    · have l0 := Hψ.w_n4f_in.length_le
      simp only [gate3Out_length] at l0
      have l_n4_a := Hψ.w_n4_a.length_le
      have l_n4_b := Hψ.w_n4_b.length_le
      have l_n4_c := Hψ.w_n4_c.length_le
      rw [Hψ.w_n4f_in.getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_n4_a.getD_eq_left (by omega), ih.2.2.1 (by omega), Hψ.w_n4_b.getD_eq_left (by omega), Hψ.e_d, Hψ.w_n4_c.getD_eq_left (by omega), Hψ.e_crn]
      rfl
    · have l0 := Hψ.w_n5f_in.length_le
      simp only [gateOut_length] at l0
      have l_n5_a := Hψ.w_n5_a.length_le
      rw [Hψ.w_n5f_in.getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_n5_a.getD_eq_left (by omega), ih.2.1 (by omega), ih.2.2.2.2.2.1 (by omega)]
      rfl
    · have l0 := Hψ.w_n5_b.length_le
      simp only [gate3Out_length] at l0
      have l_n6_a := Hψ.w_n6_a.length_le
      have l_n6_b := Hψ.w_n6_b.length_le
      have l_n6_c := Hψ.w_n6_c.length_le
      rw [Hψ.w_n5_b.getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_n6_a.getD_eq_left (by omega), ih.2.2.2.2.1 (by omega), Hψ.w_n6_b.getD_eq_left (by omega), ih.2.2.1 (by omega), Hψ.w_n6_c.getD_eq_left (by omega), Hψ.e_crn]
      rfl
    · have l0 := Hψ.w_cut_in.length_le
      simp only [gateOut_length] at l0
      have l_qf_a := Hψ.w_qf_a.length_le
      have l_qf_b := Hψ.w_qf_b.length_le
      rw [Hψ.w_cut_in.getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_qf_a.getD_eq_left (by omega), ih.2.2.2.2.1 (by omega), Hψ.w_qf_b.getD_eq_left (by omega), Hψ.e_crn]
      rfl

/-- What the block reports is a prefix of what the specification says: the values agree
by `wf_sim`, and the length is what `cut3` allows. -/
theorem out_q :
    cut_in.take (min (min cut_r1.length cut_r2.length) cut_r3.length + 1) <+:
      dffOut sp.1 sp.2.1 sp.2.2 := by
  have h1 := Hψ.w_cut_r1.length_le
  have h2 := Hψ.w_cut_r2.length_le
  have h3 := Hψ.w_cut_r3.length_le
  rw [Hψ.e_clk] at h1
  rw [Hψ.e_d] at h2
  rw [Hψ.e_crn] at h3
  rw [prefix_iff_length_getD false]
  refine ⟨by simp only [List.length_take, dffOut_length]; unfold dffLen; omega, fun t ht => ?_⟩
  simp only [List.length_take] at ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
    ← List.getD_eq_getElem?_getD, dffOut_getD _ _ _ (by unfold dffLen; omega)]
  exact (wf_sim Hψ t).2.2.2.2.2.2 (by omega)

end Cases

/-! ### The refinement

One lemma per internal rule: a single tactic block over all of them would have to carry the
whole state through `subst`, which is what made the write domain's netlist blow up. -/

theorem int_case_0 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_0 Hψ ‹_›⟩

theorem int_case_1 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_1 Hψ ‹_›⟩

theorem int_case_2 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_2 Hψ ‹_›⟩

theorem int_case_3 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_3 Hψ ‹_›⟩

theorem int_case_4 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_4 Hψ ‹_›⟩

theorem int_case_5 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_5 Hψ ‹_›⟩

theorem int_case_6 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_6 Hψ ‹_›⟩

theorem int_case_7 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_7 Hψ ‹_›⟩

theorem int_case_8 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_8 Hψ ‹_›⟩

theorem int_case_9 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_9 Hψ ‹_›⟩

theorem int_case_10 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_10 Hψ ‹_›⟩

theorem int_case_11 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_11 Hψ ‹_›⟩

theorem int_case_12 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_12 Hψ ‹_›⟩

theorem int_case_13 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_13 Hψ ‹_›⟩

theorem int_case_14 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_14 Hψ ‹_›⟩

theorem int_case_15 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_15 Hψ ‹_›⟩

theorem int_case_16 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_16 Hψ ‹_›⟩

theorem int_case_17 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_17 Hψ ‹_›⟩

theorem int_case_18 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_18 Hψ ‹_›⟩

theorem int_case_19 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_19 Hψ ‹_›⟩

theorem int_case_20 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_20 Hψ ‹_›⟩

theorem int_case_21 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_21 Hψ ‹_›⟩

theorem int_case_22 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_22 Hψ ‹_›⟩

theorem int_case_23 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_23 Hψ ‹_›⟩

theorem int_case_24 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_24 Hψ ‹_›⟩

theorem int_case_25 (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)
    (Hrule : (dffNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_n5f_in, c_df_in, ⟨c_qf_a, c_qf_b⟩, c_crf_in, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n5_a, c_n5_b⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_25 Hψ ‹_›⟩

theorem dffNetlist_internals_eq : dffNetlist.internals = [dffNetlist.internals.getD 0 (fun _ _ => False), dffNetlist.internals.getD 1 (fun _ _ => False), dffNetlist.internals.getD 2 (fun _ _ => False), dffNetlist.internals.getD 3 (fun _ _ => False), dffNetlist.internals.getD 4 (fun _ _ => False), dffNetlist.internals.getD 5 (fun _ _ => False), dffNetlist.internals.getD 6 (fun _ _ => False), dffNetlist.internals.getD 7 (fun _ _ => False), dffNetlist.internals.getD 8 (fun _ _ => False), dffNetlist.internals.getD 9 (fun _ _ => False), dffNetlist.internals.getD 10 (fun _ _ => False), dffNetlist.internals.getD 11 (fun _ _ => False), dffNetlist.internals.getD 12 (fun _ _ => False), dffNetlist.internals.getD 13 (fun _ _ => False), dffNetlist.internals.getD 14 (fun _ _ => False), dffNetlist.internals.getD 15 (fun _ _ => False), dffNetlist.internals.getD 16 (fun _ _ => False), dffNetlist.internals.getD 17 (fun _ _ => False), dffNetlist.internals.getD 18 (fun _ _ => False), dffNetlist.internals.getD 19 (fun _ _ => False), dffNetlist.internals.getD 20 (fun _ _ => False), dffNetlist.internals.getD 21 (fun _ _ => False), dffNetlist.internals.getD 22 (fun _ _ => False), dffNetlist.internals.getD 23 (fun _ _ => False), dffNetlist.internals.getD 24 (fun _ _ => False), dffNetlist.internals.getD 25 (fun _ _ => False)] := rfl

theorem refines_ψ : dffNetlist ⊑_{ψ} dffSpec := by
  intro i s Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs dffNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [dffNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← Hψ.e_clk]; assumption), existSR_reflexive, in_clk Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← Hψ.e_d]; assumption), existSR_reflexive, in_d Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← Hψ.e_crn]; assumption), existSR_reflexive, in_clrn Hψ _ ‹_›⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_n5f_in, m_df_in, ⟨m_qf_a, m_qf_b⟩, m_crf_in, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n5_a, m_n5_b⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs dffNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [dffNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ (out_q Hψ), Hψ⟩
  · intro rule mid_i Hin Hrule
    rw [dffNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact int_case_0 s i mid_i Hψ Hrule
    · subst h; exact int_case_1 s i mid_i Hψ Hrule
    · subst h; exact int_case_2 s i mid_i Hψ Hrule
    · subst h; exact int_case_3 s i mid_i Hψ Hrule
    · subst h; exact int_case_4 s i mid_i Hψ Hrule
    · subst h; exact int_case_5 s i mid_i Hψ Hrule
    · subst h; exact int_case_6 s i mid_i Hψ Hrule
    · subst h; exact int_case_7 s i mid_i Hψ Hrule
    · subst h; exact int_case_8 s i mid_i Hψ Hrule
    · subst h; exact int_case_9 s i mid_i Hψ Hrule
    · subst h; exact int_case_10 s i mid_i Hψ Hrule
    · subst h; exact int_case_11 s i mid_i Hψ Hrule
    · subst h; exact int_case_12 s i mid_i Hψ Hrule
    · subst h; exact int_case_13 s i mid_i Hψ Hrule
    · subst h; exact int_case_14 s i mid_i Hψ Hrule
    · subst h; exact int_case_15 s i mid_i Hψ Hrule
    · subst h; exact int_case_16 s i mid_i Hψ Hrule
    · subst h; exact int_case_17 s i mid_i Hψ Hrule
    · subst h; exact int_case_18 s i mid_i Hψ Hrule
    · subst h; exact int_case_19 s i mid_i Hψ Hrule
    · subst h; exact int_case_20 s i mid_i Hψ Hrule
    · subst h; exact int_case_21 s i mid_i Hψ Hrule
    · subst h; exact int_case_22 s i mid_i Hψ Hrule
    · subst h; exact int_case_23 s i mid_i Hψ Hrule
    · subst h; exact int_case_24 s i mid_i Hψ Hrule
    · subst h; exact int_case_25 s i mid_i Hψ Hrule

theorem refines_initial : Module.refines_initial dffNetlist dffSpec ψ := by
  intro i hi
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  dsimp only [dffNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨([], [], []), rfl, Wf.init⟩

/-- **The netlist refines the flip-flop block.** -/
theorem dff_refines : dffNetlist ⊑ dffSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.Dff
