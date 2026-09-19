/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.Dff

/-!
# One cell of the register file: a flip-flop that holds

A memory cell captures its data when it is written to and keeps it otherwise, so its flip-flop
is fed by a multiplexer that reads the flip-flop's own output:

    nen = not en        t1 = en and data      t2 = nen and q
    m   = t1 or t2      (and the flip-flop of `Dff.lean` with `d := m`)

That loop is why this is a netlist of gates rather than a graph of blocks.  A block's output is
a function of the streams it was *given*, and here the flip-flop is given a stream that depends
on what it produces; the fixpoint of the two is not a composition of the two functions.  So the
cell's eleven gates get one automaton, `enRun`, exactly as the flip-flop's seven did.

Nothing is lost by inlining: `EnRegTiming.lean` shows that the six flip-flop wires of `enRun`
are `Dff.dffRun` driven by the multiplexer's stream, so every timing theorem about the
flip-flop applies to the cell, and the only new work is what the multiplexer does around an
edge.

The clock gating that would avoid the loop -- `clk and en` into the flip-flop -- is not used
here.  It needs the enable to be stable over the whole high phase of the clock, and the write
side only promises a setup window (`CleanWrites`), so a late change of the enable could forge a
second edge.  That is a real hazard, which is why clock gaters are latch-based.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.EnReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Dff

/-! ### The gates of the multiplexer -/

def or2 (a b : Bool) : Bool := a || b

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

instance : Inhabited EnSt := ⟨⟨false, false, false, false, false, false, false, false, false,
  false, false⟩⟩

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

theorem enRun_congr {clk clk' en en' dat dat' crn crn' : List Bool} (hc : clk <+: clk')
    (he : en <+: en') (hd : dat <+: dat') (hr : crn <+: crn') {t : Nat}
    (ht : t ≤ enLen clk en dat crn) : enRun clk en dat crn t = enRun clk' en' dat' crn' t := by
  refine run_congr _ _ (fun u hu => ?_) t ht
  unfold enLen at hu
  unfold enInp
  rw [hc.getD_eq_left (by omega), he.getD_eq_left (by omega), hd.getD_eq_left (by omega),
    hr.getD_eq_left (by omega)]

/-- What the cell reports: its output wire, as far as its inputs are known plus the one instant
a Moore block may report. -/
def enOut (clk en dat crn : List Bool) : List Bool :=
  timeline (fun t => (enRun clk en dat crn t).q) (enLen clk en dat crn + 1)

@[simp] theorem enOut_length (clk en dat crn : List Bool) :
    (enOut clk en dat crn).length = enLen clk en dat crn + 1 := timeline_length _ _

theorem enOut_getD (clk en dat crn : List Bool) {t : Nat} (ht : t < enLen clk en dat crn + 1) :
    (enOut clk en dat crn).getD t false = (enRun clk en dat crn t).q := timeline_getD _ ht _

theorem enOut_mono {clk clk' en en' dat dat' crn crn' : List Bool} (hc : clk <+: clk')
    (he : en <+: en') (hd : dat <+: dat') (hr : crn <+: crn') :
    enOut clk en dat crn <+: enOut clk' en' dat' crn' := by
  have := hc.length_le; have := he.length_le; have := hd.length_le; have := hr.length_le
  apply timeline_mono (by unfold enLen; omega)
  intro t ht
  rw [enRun_congr hc he hd hr (by unfold enLen at *; omega)]

/-! ### The netlist -/

def enGraph := [graphEnv|
    clk [type="io"];
    en [type="io"];
    data [type="io"];
    clrn [type="io"];
    q [type="io"];

    clkf [type="fork3", typeImp=$(⟨_, fork3⟩)];
    crf [type="fork5", typeImp=$(⟨_, fork5⟩)];
    enf [type="fork3", typeImp=$(⟨_, fork3⟩)];
    dataf [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    nen [type="not1", typeImp=$(⟨_, gate1 not⟩)];
    t1 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    t2 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    mx [type="or2", typeImp=$(⟨_, gate2 or2⟩)];
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
    qg [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    qf [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    cut [type="cut4", typeImp=$(⟨_, cut4⟩)];

    clk -> clkf [to="in"];
    en -> enf [to="in"];
    data -> dataf [to="in"];
    clrn -> crf [to="in"];

    clkf -> n2 [from="out1", to="b"];
    clkf -> n3 [from="out2", to="b"];
    clkf -> cut [from="out3", to="r1"];
    crf -> n2 [from="out1", to="c"];
    crf -> n4 [from="out2", to="c"];
    crf -> n6 [from="out3", to="c"];
    crf -> qg [from="out4", to="b"];
    crf -> cut [from="out5", to="r4"];
    enf -> nen [from="out1", to="a"];
    enf -> t1 [from="out2", to="a"];
    enf -> cut [from="out3", to="r2"];
    dataf -> t1 [from="out1", to="b"];
    dataf -> cut [from="out2", to="r3"];
    nen -> t2 [from="out", to="a"];
    qf -> t2 [from="out1", to="b"];
    qf -> cut [from="out2", to="in"];
    t1 -> mx [from="out", to="a"];
    t2 -> mx [from="out", to="b"];
    mx -> n4 [from="out", to="b"];
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
    n5f -> qg [from="out2", to="a"];
    qg -> qf [from="out", to="in"];

    cut -> q [from="out"];
  ]

@[drunfold_defs]
def enLowered := enGraph.1.lower_TR |>.get rfl

def eenv := enGraph.2

@[drenv] theorem eenv_fork2 : eenv.find? "fork2" = .some ⟨_, Timed.fork2 Bool⟩ := rfl
@[drenv] theorem eenv_fork3 : eenv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem eenv_fork5 : eenv.find? "fork5" = .some ⟨_, fork5⟩ := rfl
@[drenv] theorem eenv_not1 : eenv.find? "not1" = .some ⟨_, gate1 not⟩ := rfl
@[drenv] theorem eenv_and2 : eenv.find? "and2" = .some ⟨_, gate2 and2⟩ := rfl
@[drenv] theorem eenv_or2 : eenv.find? "or2" = .some ⟨_, gate2 or2⟩ := rfl
@[drenv] theorem eenv_nand2 : eenv.find? "nand2" = .some ⟨_, gate2 nand2⟩ := rfl
@[drenv] theorem eenv_nand3 : eenv.find? "nand3" = .some ⟨_, gate3 nand3⟩ := rfl
@[drenv] theorem eenv_cut4 : eenv.find? "cut4" = .some ⟨_, cut4⟩ := rfl

seal eenv in
def_module enT : Type :=
  [T| enLowered, eenv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal eenv in
def_module enNetlist : StringModule enT :=
  [e| enLowered, eenv.find? ]

-- HEADER_END (everything below is generated by gen/gen_enreg.py)

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

instance : MatchInterface enNetlist enSpec := by
  dsimp [enNetlist, enSpec]
  solve_match_interface

/-! ### The invariant -/

structure Wf (n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a : List Bool) (s : List Bool × List Bool × List Bool × List Bool) : Prop where
  e_clk : clkf_in = s.1
  e_en : enf_in = s.2.1
  e_data : dataf_in = s.2.2.1
  e_crn : crf_in = s.2.2.2
  w_n2_a : n2_a <+: gateOut nand2 n1_a n1_b
  w_n2_b : n2_b <+: clkf_in
  w_n2_c : n2_c <+: crf_in
  w_n5f_in : n5f_in <+: gateOut nand2 n5_a n5_b
  w_qg_a : qg_a <+: n5f_in
  w_qg_b : qg_b <+: crf_in
  w_qf_in : qf_in <+: gateOut and2 qg_a qg_b
  w_t1_a : t1_a <+: enf_in
  w_t1_b : t1_b <+: dataf_in
  w_n5_a : n5_a <+: n2f_in
  w_n5_b : n5_b <+: gate3Out nand3 n6_a n6_b n6_c
  w_n6_a : n6_a <+: n5f_in
  w_n6_b : n6_b <+: n3f_in
  w_n6_c : n6_c <+: crf_in
  w_n4_a : n4_a <+: n3f_in
  w_n4_b : n4_b <+: gateOut or2 mx_a mx_b
  w_n4_c : n4_c <+: crf_in
  w_n4f_in : n4f_in <+: gate3Out nand3 n4_a n4_b n4_c
  w_n3_a : n3_a <+: n2f_in
  w_n3_b : n3_b <+: clkf_in
  w_n3_c : n3_c <+: n4f_in
  w_n1_a : n1_a <+: n4f_in
  w_n1_b : n1_b <+: n2f_in
  w_n3f_in : n3f_in <+: gate3Out nand3 n3_a n3_b n3_c
  w_t2_a : t2_a <+: gate1Out not nen_a
  w_t2_b : t2_b <+: qf_in
  w_n2f_in : n2f_in <+: gate3Out nand3 n2_a n2_b n2_c
  w_cut_in : cut_in <+: qf_in
  w_cut_r1 : cut_r1 <+: clkf_in
  w_cut_r2 : cut_r2 <+: enf_in
  w_cut_r3 : cut_r3 <+: dataf_in
  w_cut_r4 : cut_r4 <+: crf_in
  w_mx_a : mx_a <+: gateOut and2 t1_a t1_b
  w_mx_b : mx_b <+: gateOut and2 t2_a t2_b
  w_nen_a : nen_a <+: enf_in

def ψ (i : enT) (s : List Bool × List Bool × List Bool × List Bool) : Prop :=
  Wf i.1.1 i.1.2.1 i.1.2.2 i.2.1 i.2.2.1 i.2.2.2.1.1 i.2.2.2.1.2 i.2.2.2.2.1 i.2.2.2.2.2.1.1 i.2.2.2.2.2.1.2 i.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 s

theorem Wf.init : Wf [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] ([], [], [], []) :=
  ⟨rfl, rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩

section SpecRules
variable (sp : List Bool × List Bool × List Bool × List Bool)

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (enSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_en (v : List Bool) (h : sp.2.1 ⊏ v) :
    (enSpec.inputs.getIO ↑"en").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_data (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (enSpec.inputs.getIO ↑"data").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.2 ⊏ v) :
    (enSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List Bool) (h : v <+: enOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2) :
    (enSpec.outputs.getIO ↑"q").2 sp v sp := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨rfl, h⟩
end SpecRules

section Cases
variable {n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a : List Bool} {sp : List Bool × List Bool × List Bool × List Bool}
  (Hψ : Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp)
include Hψ

theorem in_clk (v : List Bool) (h : clkf_in ⊏ v) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b (v) n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a (v, sp.2) := by
  have hm : clkf_in <+: v := h.isPrefix
  exact { e_clk := rfl
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b.trans hm
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1.trans hm
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem in_en (v : List Bool) (h : enf_in ⊏ v) :
    Wf n2_a n2_b n2_c (v) n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a (sp.1, v, sp.2.2) := by
  have hm : enf_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_en := rfl
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a.trans hm
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2.trans hm
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a.trans hm }

theorem in_data (v : List Bool) (h : dataf_in ⊏ v) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in (v) t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a (sp.1, sp.2.1, v, sp.2.2.2) := by
  have hm : dataf_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := rfl
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b.trans hm
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3.trans hm
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem in_clrn (v : List Bool) (h : crf_in ⊏ v) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b (v) n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a (sp.1, sp.2.1, sp.2.2.1, v) := by
  have hm : crf_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := rfl
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c.trans hm
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b.trans hm
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c.trans hm
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4.trans hm
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_0 (_h : n2_b ⊏ clkf_in) :
    Wf n2_a (clkf_in) n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := List.prefix_rfl
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in.trans (gate3Out_mono _ List.prefix_rfl Hψ.w_n2_b List.prefix_rfl)
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_1 (_h : n3_b ⊏ clkf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a (clkf_in) n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_2 (_h : cut_r1 ⊏ clkf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in (clkf_in) cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := List.prefix_rfl
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_3 (_h : n2_c ⊏ crf_in) :
    Wf n2_a n2_b (crf_in) enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := List.prefix_rfl
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in.trans (gate3Out_mono _ List.prefix_rfl List.prefix_rfl Hψ.w_n2_c)
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_4 (_h : n4_c ⊏ crf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b (crf_in) n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_5 (_h : n6_c ⊏ crf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b (crf_in) n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b.trans (gate3Out_mono _ List.prefix_rfl List.prefix_rfl Hψ.w_n6_c)
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := List.prefix_rfl
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_6 (_h : qg_b ⊏ crf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a (crf_in) qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := List.prefix_rfl
          w_qf_in := Hψ.w_qf_in.trans (gateOut_mono _ List.prefix_rfl Hψ.w_qg_b)
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_7 (_h : cut_r4 ⊏ crf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 (crf_in) mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := List.prefix_rfl
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_8 (_h : nen_a ⊏ enf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b (enf_in) sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a.trans (gate1Out_mono _ Hψ.w_nen_a)
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := List.prefix_rfl }

theorem int_9 (_h : t1_a ⊏ enf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in (enf_in) t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := List.prefix_rfl
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a.trans (gateOut_mono _ Hψ.w_t1_a List.prefix_rfl)
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_10 (_h : cut_r2 ⊏ enf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 (enf_in) cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := List.prefix_rfl
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_11 (_h : t1_b ⊏ dataf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a (dataf_in) crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := List.prefix_rfl
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_t1_b)
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_12 (_h : cut_r3 ⊏ dataf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 (dataf_in) cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := List.prefix_rfl
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_13 (_h : t2_a ⊏ gate1Out not nen_a) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in (gate1Out not nen_a) t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := List.prefix_rfl
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b.trans (gateOut_mono _ Hψ.w_t2_a List.prefix_rfl)
          w_nen_a := Hψ.w_nen_a }

theorem int_14 (_h : t2_b ⊏ qf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a (qf_in) clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := List.prefix_rfl
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_t2_b)
          w_nen_a := Hψ.w_nen_a }

theorem int_15 (_h : cut_in ⊏ qf_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in (qf_in) cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := List.prefix_rfl
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_16 (_h : mx_a ⊏ gateOut and2 t1_a t1_b) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 (gateOut and2 t1_a t1_b) mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b.trans (gateOut_mono _ Hψ.w_mx_a List.prefix_rfl)
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := List.prefix_rfl
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_17 (_h : mx_b ⊏ gateOut and2 t2_a t2_b) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a (gateOut and2 t2_a t2_b) nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
          w_n4_a := Hψ.w_n4_a
          w_n4_b := Hψ.w_n4_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_mx_b)
          w_n4_c := Hψ.w_n4_c
          w_n4f_in := Hψ.w_n4f_in
          w_n3_a := Hψ.w_n3_a
          w_n3_b := Hψ.w_n3_b
          w_n3_c := Hψ.w_n3_c
          w_n1_a := Hψ.w_n1_a
          w_n1_b := Hψ.w_n1_b
          w_n3f_in := Hψ.w_n3f_in
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := List.prefix_rfl
          w_nen_a := Hψ.w_nen_a }

theorem int_18 (_h : n4_b ⊏ gateOut or2 mx_a mx_b) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a (gateOut or2 mx_a mx_b) n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_19 (_h : n1_a ⊏ n4f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c (n4f_in) n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a.trans (gateOut_mono _ Hψ.w_n1_a List.prefix_rfl)
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_20 (_h : n1_b ⊏ n2f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a (n2f_in) n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_n1_b)
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_21 (_h : n2_a ⊏ gateOut nand2 n1_a n1_b) :
    Wf (gateOut nand2 n1_a n1_b) n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := List.prefix_rfl
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in.trans (gate3Out_mono _ Hψ.w_n2_a List.prefix_rfl List.prefix_rfl)
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_22 (_h : n2f_in ⊏ gate3Out nand3 n2_a n2_b n2_c) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in (gate3Out nand3 n2_a n2_b n2_c) cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a.trans Hψ.w_n2f_in
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := List.prefix_rfl
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_23 (_h : n3_a ⊏ n2f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in (n2f_in) n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_24 (_h : n3_c ⊏ n4f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b (n4f_in) n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_25 (_h : n3f_in ⊏ gate3Out nand3 n3_a n3_b n3_c) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b (gate3Out nand3 n3_a n3_b n3_c) dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b.trans Hψ.w_n3f_in
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_26 (_h : n4_a ⊏ n3f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c (n3f_in) n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_27 (_h : n4f_in ⊏ gate3Out nand3 n4_a n4_b n4_c) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c (gate3Out nand3 n4_a n4_b n4_c) n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_28 (_h : n5_a ⊏ n2f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in (n2f_in) n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in.trans (gateOut_mono _ Hψ.w_n5_a List.prefix_rfl)
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := List.prefix_rfl
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_29 (_h : n5_b ⊏ gate3Out nand3 n6_a n6_b n6_c) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a (gate3Out nand3 n6_a n6_b n6_c) n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in.trans (gateOut_mono _ List.prefix_rfl Hψ.w_n5_b)
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := List.prefix_rfl
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_30 (_h : n5f_in ⊏ gateOut nand2 n5_a n5_b) :
    Wf n2_a n2_b n2_c enf_in (gateOut nand2 n5_a n5_b) qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := List.prefix_rfl
          w_qg_a := Hψ.w_qg_a.trans Hψ.w_n5f_in
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a.trans Hψ.w_n5f_in
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_31 (_h : n6_a ⊏ n5f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b (n5f_in) n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b.trans (gate3Out_mono _ Hψ.w_n6_a List.prefix_rfl List.prefix_rfl)
          w_n6_a := List.prefix_rfl
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_32 (_h : n6_b ⊏ n3f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a (n3f_in) n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b.trans (gate3Out_mono _ List.prefix_rfl Hψ.w_n6_b List.prefix_rfl)
          w_n6_a := Hψ.w_n6_a
          w_n6_b := List.prefix_rfl
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_33 (_h : qg_a ⊏ n5f_in) :
    Wf n2_a n2_b n2_c enf_in n5f_in (n5f_in) qg_b qf_in t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := List.prefix_rfl
          w_qg_b := Hψ.w_qg_b
          w_qf_in := Hψ.w_qf_in.trans (gateOut_mono _ Hψ.w_qg_a List.prefix_rfl)
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

theorem int_34 (_h : qf_in ⊏ gateOut and2 qg_a qg_b) :
    Wf n2_a n2_b n2_c enf_in n5f_in qg_a qg_b (gateOut and2 qg_a qg_b) t1_a t1_b crf_in n5_a n5_b n6_a n6_b n6_c n4_a n4_b n4_c n4f_in n3_a n3_b n3_c n1_a n1_b n3f_in dataf_in t2_a t2_b clkf_in n2f_in cut_in cut_r1 cut_r2 cut_r3 cut_r4 mx_a mx_b nen_a sp := by
  exact { e_clk := Hψ.e_clk
          e_en := Hψ.e_en
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_n2_a := Hψ.w_n2_a
          w_n2_b := Hψ.w_n2_b
          w_n2_c := Hψ.w_n2_c
          w_n5f_in := Hψ.w_n5f_in
          w_qg_a := Hψ.w_qg_a
          w_qg_b := Hψ.w_qg_b
          w_qf_in := List.prefix_rfl
          w_t1_a := Hψ.w_t1_a
          w_t1_b := Hψ.w_t1_b
          w_n5_a := Hψ.w_n5_a
          w_n5_b := Hψ.w_n5_b
          w_n6_a := Hψ.w_n6_a
          w_n6_b := Hψ.w_n6_b
          w_n6_c := Hψ.w_n6_c
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
          w_t2_a := Hψ.w_t2_a
          w_t2_b := Hψ.w_t2_b.trans Hψ.w_qf_in
          w_n2f_in := Hψ.w_n2f_in
          w_cut_in := Hψ.w_cut_in.trans Hψ.w_qf_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_cut_r3 := Hψ.w_cut_r3
          w_cut_r4 := Hψ.w_cut_r4
          w_mx_a := Hψ.w_mx_a
          w_mx_b := Hψ.w_mx_b
          w_nen_a := Hψ.w_nen_a }

/-- **The nodes agree with the automaton.**  The cell's loop -- the multiplexer reading the
flip-flop it feeds -- is resolved here, by the same induction on the instant as the flip-flop's
own loops: the structural invariant says each node holds a prefix of what drives it, and that
is enough. -/
theorem wf_sim : ∀ t,
    (t < n2_a.length → n2_a.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).n1) ∧
    (t < n2f_in.length → n2f_in.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).n2) ∧
    (t < n3f_in.length → n3f_in.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).n3) ∧
    (t < n4f_in.length → n4f_in.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).n4) ∧
    (t < n5f_in.length → n5f_in.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).n5) ∧
    (t < n5_b.length → n5_b.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).n6) ∧
    (t < qf_in.length → qf_in.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).q) ∧
    (t < t2_a.length → t2_a.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).nen) ∧
    (t < mx_a.length → mx_a.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).t1) ∧
    (t < mx_b.length → mx_b.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).t2) ∧
    (t < n4_b.length → n4_b.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).m) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
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
    · rw [Hψ.w_qf_in.getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [Hψ.w_t2_a.getD_eq_left hl, gate1Out_getD_zero]
      rfl
    · rw [Hψ.w_mx_a.getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [Hψ.w_mx_b.getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [Hψ.w_n4_b.getD_eq_left hl, gateOut_getD_zero]
      rfl
  | succ t ih =>
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
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
      have l_n4_c := Hψ.w_n4_c.length_le
      rw [Hψ.w_n4f_in.getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_n4_a.getD_eq_left (by omega), ih.2.2.1 (by omega), ih.2.2.2.2.2.2.2.2.2.2 (by omega), Hψ.w_n4_c.getD_eq_left (by omega), Hψ.e_crn]
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
    · have l0 := Hψ.w_qf_in.length_le
      simp only [gateOut_length] at l0
      have l_qg_a := Hψ.w_qg_a.length_le
      have l_qg_b := Hψ.w_qg_b.length_le
      rw [Hψ.w_qf_in.getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_qg_a.getD_eq_left (by omega), ih.2.2.2.2.1 (by omega), Hψ.w_qg_b.getD_eq_left (by omega), Hψ.e_crn]
      rfl
    · have l0 := Hψ.w_t2_a.length_le
      simp only [gate1Out_length] at l0
      have l_nen_a := Hψ.w_nen_a.length_le
      rw [Hψ.w_t2_a.getD_eq_left hl, gate1Out_getD _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_nen_a.getD_eq_left (by omega), Hψ.e_en]
      rfl
    · have l0 := Hψ.w_mx_a.length_le
      simp only [gateOut_length] at l0
      have l_t1_a := Hψ.w_t1_a.length_le
      have l_t1_b := Hψ.w_t1_b.length_le
      rw [Hψ.w_mx_a.getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, Hψ.w_t1_a.getD_eq_left (by omega), Hψ.e_en, Hψ.w_t1_b.getD_eq_left (by omega), Hψ.e_data]
      rfl
    · have l0 := Hψ.w_mx_b.length_le
      simp only [gateOut_length] at l0
      have l_t2_b := Hψ.w_t2_b.length_le
      rw [Hψ.w_mx_b.getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, ih.2.2.2.2.2.2.2.1 (by omega), Hψ.w_t2_b.getD_eq_left (by omega), ih.2.2.2.2.2.2.1 (by omega)]
      rfl
    · have l0 := Hψ.w_n4_b.length_le
      simp only [gateOut_length] at l0
      rw [Hψ.w_n4_b.getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, ih.2.2.2.2.2.2.2.2.1 (by omega), ih.2.2.2.2.2.2.2.2.2.1 (by omega)]
      rfl

/-- What the block reports is a prefix of the specification's stream. -/
theorem out_q :
    cut_in.take (min (min cut_r1.length cut_r2.length) (min cut_r3.length cut_r4.length) + 1)
      <+: enOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 := by
  have h1 := Hψ.w_cut_r1.length_le
  have h2 := Hψ.w_cut_r2.length_le
  have h3 := Hψ.w_cut_r3.length_le
  have h4 := Hψ.w_cut_r4.length_le
  rw [Hψ.e_clk] at h1
  rw [Hψ.e_en] at h2
  rw [Hψ.e_data] at h3
  rw [Hψ.e_crn] at h4
  have h5 := Hψ.w_cut_in.length_le
  rw [prefix_iff_length_getD false]
  refine ⟨by simp only [List.length_take, enOut_length]; unfold enLen; omega, fun t ht => ?_⟩
  simp only [List.length_take] at ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
    ← List.getD_eq_getElem?_getD, enOut_getD _ _ _ _ (by unfold enLen; omega)]
  rw [Hψ.w_cut_in.getD_eq_left (by omega)]
  exact (wf_sim Hψ t).2.2.2.2.2.2.1 (by omega)

end Cases

/-! ### The refinement -/

theorem int_case_0 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_0 Hψ ‹_›⟩

theorem int_case_1 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_1 Hψ ‹_›⟩

theorem int_case_2 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_2 Hψ ‹_›⟩

theorem int_case_3 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_3 Hψ ‹_›⟩

theorem int_case_4 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_4 Hψ ‹_›⟩

theorem int_case_5 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_5 Hψ ‹_›⟩

theorem int_case_6 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_6 Hψ ‹_›⟩

theorem int_case_7 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_7 Hψ ‹_›⟩

theorem int_case_8 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_8 Hψ ‹_›⟩

theorem int_case_9 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_9 Hψ ‹_›⟩

theorem int_case_10 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_10 Hψ ‹_›⟩

theorem int_case_11 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_11 Hψ ‹_›⟩

theorem int_case_12 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_12 Hψ ‹_›⟩

theorem int_case_13 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_13 Hψ ‹_›⟩

theorem int_case_14 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_14 Hψ ‹_›⟩

theorem int_case_15 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_15 Hψ ‹_›⟩

theorem int_case_16 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_16 Hψ ‹_›⟩

theorem int_case_17 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_17 Hψ ‹_›⟩

theorem int_case_18 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_18 Hψ ‹_›⟩

theorem int_case_19 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_19 Hψ ‹_›⟩

theorem int_case_20 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_20 Hψ ‹_›⟩

theorem int_case_21 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_21 Hψ ‹_›⟩

theorem int_case_22 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_22 Hψ ‹_›⟩

theorem int_case_23 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_23 Hψ ‹_›⟩

theorem int_case_24 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_24 Hψ ‹_›⟩

theorem int_case_25 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_25 Hψ ‹_›⟩

theorem int_case_26 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_26 Hψ ‹_›⟩

theorem int_case_27 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_27 Hψ ‹_›⟩

theorem int_case_28 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 28 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_28 Hψ ‹_›⟩

theorem int_case_29 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 29 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_29 Hψ ‹_›⟩

theorem int_case_30 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 30 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_30 Hψ ‹_›⟩

theorem int_case_31 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 31 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_31 Hψ ‹_›⟩

theorem int_case_32 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 32 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_32 Hψ ‹_›⟩

theorem int_case_33 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 33 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_33 Hψ ‹_›⟩

theorem int_case_34 (s : List Bool × List Bool × List Bool × List Bool) (i mid : enT) (Hψ : ψ i s)
    (Hrule : (enNetlist.internals.getD 34 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_n2_a, c_n2_b, c_n2_c⟩, c_enf_in, c_n5f_in, ⟨c_qg_a, c_qg_b⟩, c_qf_in, ⟨c_t1_a, c_t1_b⟩, c_crf_in, ⟨c_n5_a, c_n5_b⟩, ⟨c_n6_a, c_n6_b, c_n6_c⟩, ⟨c_n4_a, c_n4_b, c_n4_c⟩, c_n4f_in, ⟨c_n3_a, c_n3_b, c_n3_c⟩, ⟨c_n1_a, c_n1_b⟩, c_n3f_in, c_dataf_in, ⟨c_t2_a, c_t2_b⟩, c_clkf_in, c_n2f_in, ⟨c_cut_in, c_cut_r1, c_cut_r2, c_cut_r3, c_cut_r4⟩, ⟨c_mx_a, c_mx_b⟩, c_nen_a⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_34 Hψ ‹_›⟩

theorem enNetlist_internals_eq : enNetlist.internals = [enNetlist.internals.getD 0 (fun _ _ => False), enNetlist.internals.getD 1 (fun _ _ => False), enNetlist.internals.getD 2 (fun _ _ => False), enNetlist.internals.getD 3 (fun _ _ => False), enNetlist.internals.getD 4 (fun _ _ => False), enNetlist.internals.getD 5 (fun _ _ => False), enNetlist.internals.getD 6 (fun _ _ => False), enNetlist.internals.getD 7 (fun _ _ => False), enNetlist.internals.getD 8 (fun _ _ => False), enNetlist.internals.getD 9 (fun _ _ => False), enNetlist.internals.getD 10 (fun _ _ => False), enNetlist.internals.getD 11 (fun _ _ => False), enNetlist.internals.getD 12 (fun _ _ => False), enNetlist.internals.getD 13 (fun _ _ => False), enNetlist.internals.getD 14 (fun _ _ => False), enNetlist.internals.getD 15 (fun _ _ => False), enNetlist.internals.getD 16 (fun _ _ => False), enNetlist.internals.getD 17 (fun _ _ => False), enNetlist.internals.getD 18 (fun _ _ => False), enNetlist.internals.getD 19 (fun _ _ => False), enNetlist.internals.getD 20 (fun _ _ => False), enNetlist.internals.getD 21 (fun _ _ => False), enNetlist.internals.getD 22 (fun _ _ => False), enNetlist.internals.getD 23 (fun _ _ => False), enNetlist.internals.getD 24 (fun _ _ => False), enNetlist.internals.getD 25 (fun _ _ => False), enNetlist.internals.getD 26 (fun _ _ => False), enNetlist.internals.getD 27 (fun _ _ => False), enNetlist.internals.getD 28 (fun _ _ => False), enNetlist.internals.getD 29 (fun _ _ => False), enNetlist.internals.getD 30 (fun _ _ => False), enNetlist.internals.getD 31 (fun _ _ => False), enNetlist.internals.getD 32 (fun _ _ => False), enNetlist.internals.getD 33 (fun _ _ => False), enNetlist.internals.getD 34 (fun _ _ => False)] := rfl

theorem refines_ψ : enNetlist ⊑_{ψ} enSpec := by
  intro i s Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid_i
    case_transition Hcontains : Module.inputs enNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [enNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← Hψ.e_clk]; assumption), existSR_reflexive, in_clk Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_en s _ (by rw [← Hψ.e_en]; assumption), existSR_reflexive, in_en Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_data s _ (by rw [← Hψ.e_data]; assumption), existSR_reflexive, in_data Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← Hψ.e_crn]; assumption), existSR_reflexive, in_clrn Hψ _ ‹_›⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_n2_a, m_n2_b, m_n2_c⟩, m_enf_in, m_n5f_in, ⟨m_qg_a, m_qg_b⟩, m_qf_in, ⟨m_t1_a, m_t1_b⟩, m_crf_in, ⟨m_n5_a, m_n5_b⟩, ⟨m_n6_a, m_n6_b, m_n6_c⟩, ⟨m_n4_a, m_n4_b, m_n4_c⟩, m_n4f_in, ⟨m_n3_a, m_n3_b, m_n3_c⟩, ⟨m_n1_a, m_n1_b⟩, m_n3f_in, m_dataf_in, ⟨m_t2_a, m_t2_b⟩, m_clkf_in, m_n2f_in, ⟨m_cut_in, m_cut_r1, m_cut_r2, m_cut_r3, m_cut_r4⟩, ⟨m_mx_a, m_mx_b⟩, m_nen_a⟩ := mid_i
    case_transition Hcontains : Module.outputs enNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [enNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ (out_q Hψ), Hψ⟩
  · intro rule mid_i Hin Hrule
    rw [enNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · subst h; exact int_case_26 s i mid_i Hψ Hrule
    · subst h; exact int_case_27 s i mid_i Hψ Hrule
    · subst h; exact int_case_28 s i mid_i Hψ Hrule
    · subst h; exact int_case_29 s i mid_i Hψ Hrule
    · subst h; exact int_case_30 s i mid_i Hψ Hrule
    · subst h; exact int_case_31 s i mid_i Hψ Hrule
    · subst h; exact int_case_32 s i mid_i Hψ Hrule
    · subst h; exact int_case_33 s i mid_i Hψ Hrule
    · subst h; exact int_case_34 s i mid_i Hψ Hrule

theorem refines_initial : Module.refines_initial enNetlist enSpec ψ := by
  intro i hi
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  dsimp only [enNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨([], [], [], []), rfl, Wf.init⟩

/-- **The cell's netlist refines the cell.** -/
theorem en_refines : enNetlist ⊑ enSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.EnReg
