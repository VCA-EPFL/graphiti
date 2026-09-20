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

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Over an index rather than a record with one field
per wire, the per-rule lemmas collapse into `Netlist.Wf_step_of` and `Netlist.Wf_drv`, so what
is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The 35 driven wires. -/
inductive W
  | n2_a
  | n2_b
  | n2_c
  | n5f_in
  | qg_a
  | qg_b
  | qf_in
  | t1_a
  | t1_b
  | n5_a
  | n5_b
  | n6_a
  | n6_b
  | n6_c
  | n4_a
  | n4_b
  | n4_c
  | n4f_in
  | n3_a
  | n3_b
  | n3_c
  | n1_a
  | n1_b
  | n3f_in
  | t2_a
  | t2_b
  | n2f_in
  | cut_in
  | cut_r1
  | cut_r2
  | cut_r3
  | cut_r4
  | mx_a
  | mx_b
  | nen_a
  deriving DecidableEq

/-- What drives each wire: one line per wire, and the only place the shape of this netlist is
written down.  The loop through `n1`..`n6` and back through `qg` is the cell's latch; `drv` is
the one-step driver, so a cycle in the circuit is no cycle here. -/
def drv (clk en dat crn : List Bool) : Drv W
  | w, .n2_a => gateOut nand2 (w .n1_a) (w .n1_b)
  | _, .n2_b => clk
  | _, .n2_c => crn
  | w, .n5f_in => gateOut nand2 (w .n5_a) (w .n5_b)
  | w, .qg_a => (w .n5f_in)
  | _, .qg_b => crn
  | w, .qf_in => gateOut and2 (w .qg_a) (w .qg_b)
  | _, .t1_a => en
  | _, .t1_b => dat
  | w, .n5_a => (w .n2f_in)
  | w, .n5_b => gate3Out nand3 (w .n6_a) (w .n6_b) (w .n6_c)
  | w, .n6_a => (w .n5f_in)
  | w, .n6_b => (w .n3f_in)
  | _, .n6_c => crn
  | w, .n4_a => (w .n3f_in)
  | w, .n4_b => gateOut or2 (w .mx_a) (w .mx_b)
  | _, .n4_c => crn
  | w, .n4f_in => gate3Out nand3 (w .n4_a) (w .n4_b) (w .n4_c)
  | w, .n3_a => (w .n2f_in)
  | _, .n3_b => clk
  | w, .n3_c => (w .n4f_in)
  | w, .n1_a => (w .n4f_in)
  | w, .n1_b => (w .n2f_in)
  | w, .n3f_in => gate3Out nand3 (w .n3_a) (w .n3_b) (w .n3_c)
  | w, .t2_a => gate1Out not (w .nen_a)
  | w, .t2_b => (w .qf_in)
  | w, .n2f_in => gate3Out nand3 (w .n2_a) (w .n2_b) (w .n2_c)
  | w, .cut_in => (w .qf_in)
  | _, .cut_r1 => clk
  | _, .cut_r2 => en
  | _, .cut_r3 => dat
  | _, .cut_r4 => crn
  | w, .mx_a => gateOut and2 (w .t1_a) (w .t1_b)
  | w, .mx_b => gateOut and2 (w .t2_a) (w .t2_b)
  | _, .nen_a => en

theorem drv_mono {clk en dat crn} : Mono (drv clk en dat crn) := by
  intro a b h k
  cases k <;> simp only [drv]
  case n2_a => exact gateOut_mono _ (h .n1_a) (h .n1_b)
  case n2_b => exact List.prefix_rfl
  case n2_c => exact List.prefix_rfl
  case n5f_in => exact gateOut_mono _ (h .n5_a) (h .n5_b)
  case qg_a => exact h .n5f_in
  case qg_b => exact List.prefix_rfl
  case qf_in => exact gateOut_mono _ (h .qg_a) (h .qg_b)
  case t1_a => exact List.prefix_rfl
  case t1_b => exact List.prefix_rfl
  case n5_a => exact h .n2f_in
  case n5_b => exact gate3Out_mono _ (h .n6_a) (h .n6_b) (h .n6_c)
  case n6_a => exact h .n5f_in
  case n6_b => exact h .n3f_in
  case n6_c => exact List.prefix_rfl
  case n4_a => exact h .n3f_in
  case n4_b => exact gateOut_mono _ (h .mx_a) (h .mx_b)
  case n4_c => exact List.prefix_rfl
  case n4f_in => exact gate3Out_mono _ (h .n4_a) (h .n4_b) (h .n4_c)
  case n3_a => exact h .n2f_in
  case n3_b => exact List.prefix_rfl
  case n3_c => exact h .n4f_in
  case n1_a => exact h .n4f_in
  case n1_b => exact h .n2f_in
  case n3f_in => exact gate3Out_mono _ (h .n3_a) (h .n3_b) (h .n3_c)
  case t2_a => exact gate1Out_mono _ (h .nen_a)
  case t2_b => exact h .qf_in
  case n2f_in => exact gate3Out_mono _ (h .n2_a) (h .n2_b) (h .n2_c)
  case cut_in => exact h .qf_in
  case cut_r1 => exact List.prefix_rfl
  case cut_r2 => exact List.prefix_rfl
  case cut_r3 => exact List.prefix_rfl
  case cut_r4 => exact List.prefix_rfl
  case mx_a => exact gateOut_mono _ (h .t1_a) (h .t1_b)
  case mx_b => exact gateOut_mono _ (h .t2_a) (h .t2_b)
  case nen_a => exact List.prefix_rfl

/-- Growing the block's own inputs grows every driver. -/
theorem drv_env {clk clk' en en' dat dat' crn crn' : List Bool}
    (hclk : clk <+: clk') (hen : en <+: en') (hdat : dat <+: dat') (hcrn : crn <+: crn')
    (w : Wires W) (k : W) : drv clk en dat crn w k <+: drv clk' en' dat' crn' w k := by
  cases k <;> simp only [drv]
  case n2_a => exact gateOut_mono _ List.prefix_rfl List.prefix_rfl
  case n2_b => exact hclk
  case n2_c => exact hcrn
  case n5f_in => exact gateOut_mono _ List.prefix_rfl List.prefix_rfl
  case qg_a => exact List.prefix_rfl
  case qg_b => exact hcrn
  case qf_in => exact gateOut_mono _ List.prefix_rfl List.prefix_rfl
  case t1_a => exact hen
  case t1_b => exact hdat
  case n5_a => exact List.prefix_rfl
  case n5_b => exact gate3Out_mono _ List.prefix_rfl List.prefix_rfl List.prefix_rfl
  case n6_a => exact List.prefix_rfl
  case n6_b => exact List.prefix_rfl
  case n6_c => exact hcrn
  case n4_a => exact List.prefix_rfl
  case n4_b => exact gateOut_mono _ List.prefix_rfl List.prefix_rfl
  case n4_c => exact hcrn
  case n4f_in => exact gate3Out_mono _ List.prefix_rfl List.prefix_rfl List.prefix_rfl
  case n3_a => exact List.prefix_rfl
  case n3_b => exact hclk
  case n3_c => exact List.prefix_rfl
  case n1_a => exact List.prefix_rfl
  case n1_b => exact List.prefix_rfl
  case n3f_in => exact gate3Out_mono _ List.prefix_rfl List.prefix_rfl List.prefix_rfl
  case t2_a => exact gate1Out_mono _ List.prefix_rfl
  case t2_b => exact List.prefix_rfl
  case n2f_in => exact gate3Out_mono _ List.prefix_rfl List.prefix_rfl List.prefix_rfl
  case cut_in => exact List.prefix_rfl
  case cut_r1 => exact hclk
  case cut_r2 => exact hen
  case cut_r3 => exact hdat
  case cut_r4 => exact hcrn
  case mx_a => exact gateOut_mono _ List.prefix_rfl List.prefix_rfl
  case mx_b => exact gateOut_mono _ List.prefix_rfl List.prefix_rfl
  case nen_a => exact hen

/-- The reduced state is a nested product; `wires` reads it as an assignment. -/
def wires (i : enT) : Wires W
  | .n2_a => i.1.1
  | .n2_b => i.1.2.1
  | .n2_c => i.1.2.2
  | .n5f_in => i.2.2.1
  | .qg_a => i.2.2.2.1.1
  | .qg_b => i.2.2.2.1.2
  | .qf_in => i.2.2.2.2.1
  | .t1_a => i.2.2.2.2.2.1.1
  | .t1_b => i.2.2.2.2.2.1.2
  | .n5_a => i.2.2.2.2.2.2.2.1.1
  | .n5_b => i.2.2.2.2.2.2.2.1.2
  | .n6_a => i.2.2.2.2.2.2.2.2.1.1
  | .n6_b => i.2.2.2.2.2.2.2.2.1.2.1
  | .n6_c => i.2.2.2.2.2.2.2.2.1.2.2
  | .n4_a => i.2.2.2.2.2.2.2.2.2.1.1
  | .n4_b => i.2.2.2.2.2.2.2.2.2.1.2.1
  | .n4_c => i.2.2.2.2.2.2.2.2.2.1.2.2
  | .n4f_in => i.2.2.2.2.2.2.2.2.2.2.1
  | .n3_a => i.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .n3_b => i.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  | .n3_c => i.2.2.2.2.2.2.2.2.2.2.2.1.2.2
  | .n1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .n1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .n3f_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .t2_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .t2_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .n2f_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .cut_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .cut_r1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  | .cut_r2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  | .cut_r3 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1
  | .cut_r4 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2
  | .mx_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .mx_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .nen_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

def ψ (i : enT) (s : List Bool × List Bool × List Bool × List Bool) : Prop :=
  Wf (drv s.1 s.2.1 s.2.2.1 s.2.2.2) (wires i)
    ∧ i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = s.1
    ∧ i.2.1 = s.2.1
    ∧ i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = s.2.2.1
    ∧ i.2.2.2.2.2.2.1 = s.2.2.2

/-! ### The invariant, clause by clause

`hw .k` already says this, but with `drv` unapplied; spelling each driver out lets the
simulation proof below rewrite with it exactly as it did against the old record. -/

section Clauses
variable {clk en dat crn : List Bool} {w : Wires W} (hw : Wf (drv clk en dat crn) w)
include hw

theorem wf_n2_a : w .n2_a <+: gateOut nand2 (w .n1_a) (w .n1_b) := hw .n2_a
theorem wf_n2_b : w .n2_b <+: clk := hw .n2_b
theorem wf_n2_c : w .n2_c <+: crn := hw .n2_c
theorem wf_n5f_in : w .n5f_in <+: gateOut nand2 (w .n5_a) (w .n5_b) := hw .n5f_in
theorem wf_qg_a : w .qg_a <+: (w .n5f_in) := hw .qg_a
theorem wf_qg_b : w .qg_b <+: crn := hw .qg_b
theorem wf_qf_in : w .qf_in <+: gateOut and2 (w .qg_a) (w .qg_b) := hw .qf_in
theorem wf_t1_a : w .t1_a <+: en := hw .t1_a
theorem wf_t1_b : w .t1_b <+: dat := hw .t1_b
theorem wf_n5_a : w .n5_a <+: (w .n2f_in) := hw .n5_a
theorem wf_n5_b : w .n5_b <+: gate3Out nand3 (w .n6_a) (w .n6_b) (w .n6_c) := hw .n5_b
theorem wf_n6_a : w .n6_a <+: (w .n5f_in) := hw .n6_a
theorem wf_n6_b : w .n6_b <+: (w .n3f_in) := hw .n6_b
theorem wf_n6_c : w .n6_c <+: crn := hw .n6_c
theorem wf_n4_a : w .n4_a <+: (w .n3f_in) := hw .n4_a
theorem wf_n4_b : w .n4_b <+: gateOut or2 (w .mx_a) (w .mx_b) := hw .n4_b
theorem wf_n4_c : w .n4_c <+: crn := hw .n4_c
theorem wf_n4f_in : w .n4f_in <+: gate3Out nand3 (w .n4_a) (w .n4_b) (w .n4_c) := hw .n4f_in
theorem wf_n3_a : w .n3_a <+: (w .n2f_in) := hw .n3_a
theorem wf_n3_b : w .n3_b <+: clk := hw .n3_b
theorem wf_n3_c : w .n3_c <+: (w .n4f_in) := hw .n3_c
theorem wf_n1_a : w .n1_a <+: (w .n4f_in) := hw .n1_a
theorem wf_n1_b : w .n1_b <+: (w .n2f_in) := hw .n1_b
theorem wf_n3f_in : w .n3f_in <+: gate3Out nand3 (w .n3_a) (w .n3_b) (w .n3_c) := hw .n3f_in
theorem wf_t2_a : w .t2_a <+: gate1Out not (w .nen_a) := hw .t2_a
theorem wf_t2_b : w .t2_b <+: (w .qf_in) := hw .t2_b
theorem wf_n2f_in : w .n2f_in <+: gate3Out nand3 (w .n2_a) (w .n2_b) (w .n2_c) := hw .n2f_in
theorem wf_cut_in : w .cut_in <+: (w .qf_in) := hw .cut_in
theorem wf_cut_r1 : w .cut_r1 <+: clk := hw .cut_r1
theorem wf_cut_r2 : w .cut_r2 <+: en := hw .cut_r2
theorem wf_cut_r3 : w .cut_r3 <+: dat := hw .cut_r3
theorem wf_cut_r4 : w .cut_r4 <+: crn := hw .cut_r4
theorem wf_mx_a : w .mx_a <+: gateOut and2 (w .t1_a) (w .t1_b) := hw .mx_a
theorem wf_mx_b : w .mx_b <+: gateOut and2 (w .t2_a) (w .t2_b) := hw .mx_b
theorem wf_nen_a : w .nen_a <+: en := hw .nen_a

end Clauses

/-! ### What the netlist computes

`wf_sim` is the simulation -- the wires follow the automaton of `enRun` -- and `out_q` reads
the cell's output off it.  This is the block's actual content, and it does not collapse; only
the per-rule bookkeeping around it did. -/

theorem wf_sim {clk en dat crn : List Bool} {w : Wires W} (hw : Wf (drv clk en dat crn) w) :
    ∀ t,
    (t < (w .n2_a).length → (w .n2_a).getD t false = (enRun clk en dat crn t).n1) ∧
    (t < (w .n2f_in).length → (w .n2f_in).getD t false = (enRun clk en dat crn t).n2) ∧
    (t < (w .n3f_in).length → (w .n3f_in).getD t false = (enRun clk en dat crn t).n3) ∧
    (t < (w .n4f_in).length → (w .n4f_in).getD t false = (enRun clk en dat crn t).n4) ∧
    (t < (w .n5f_in).length → (w .n5f_in).getD t false = (enRun clk en dat crn t).n5) ∧
    (t < (w .n5_b).length → (w .n5_b).getD t false = (enRun clk en dat crn t).n6) ∧
    (t < (w .qf_in).length → (w .qf_in).getD t false = (enRun clk en dat crn t).q) ∧
    (t < (w .t2_a).length → (w .t2_a).getD t false = (enRun clk en dat crn t).nen) ∧
    (t < (w .mx_a).length → (w .mx_a).getD t false = (enRun clk en dat crn t).t1) ∧
    (t < (w .mx_b).length → (w .mx_b).getD t false = (enRun clk en dat crn t).t2) ∧
    (t < (w .n4_b).length → (w .n4_b).getD t false = (enRun clk en dat crn t).m) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
    · rw [(wf_n2_a hw).getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [(wf_n2f_in hw).getD_eq_left hl, gate3Out_getD_zero]
      rfl
    · rw [(wf_n3f_in hw).getD_eq_left hl, gate3Out_getD_zero]
      rfl
    · rw [(wf_n4f_in hw).getD_eq_left hl, gate3Out_getD_zero]
      rfl
    · rw [(wf_n5f_in hw).getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [(wf_n5_b hw).getD_eq_left hl, gate3Out_getD_zero]
      rfl
    · rw [(wf_qf_in hw).getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [(wf_t2_a hw).getD_eq_left hl, gate1Out_getD_zero]
      rfl
    · rw [(wf_mx_a hw).getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [(wf_mx_b hw).getD_eq_left hl, gateOut_getD_zero]
      rfl
    · rw [(wf_n4_b hw).getD_eq_left hl, gateOut_getD_zero]
      rfl
  | succ t ih =>
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
    · have l0 := (wf_n2_a hw).length_le
      simp only [gateOut_length] at l0
      have l_n1_a := (wf_n1_a hw).length_le
      have l_n1_b := (wf_n1_b hw).length_le
      rw [(wf_n2_a hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_n1_a hw).getD_eq_left (by omega), ih.2.2.2.1 (by omega), (wf_n1_b hw).getD_eq_left (by omega), ih.2.1 (by omega)]
      rfl
    · have l0 := (wf_n2f_in hw).length_le
      simp only [gate3Out_length] at l0
      have l_n2_b := (wf_n2_b hw).length_le
      have l_n2_c := (wf_n2_c hw).length_le
      rw [(wf_n2f_in hw).getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, ih.1 (by omega), (wf_n2_b hw).getD_eq_left (by omega), (wf_n2_c hw).getD_eq_left (by omega)]
      rfl
    · have l0 := (wf_n3f_in hw).length_le
      simp only [gate3Out_length] at l0
      have l_n3_a := (wf_n3_a hw).length_le
      have l_n3_b := (wf_n3_b hw).length_le
      have l_n3_c := (wf_n3_c hw).length_le
      rw [(wf_n3f_in hw).getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_n3_a hw).getD_eq_left (by omega), ih.2.1 (by omega), (wf_n3_b hw).getD_eq_left (by omega), (wf_n3_c hw).getD_eq_left (by omega), ih.2.2.2.1 (by omega)]
      rfl
    · have l0 := (wf_n4f_in hw).length_le
      simp only [gate3Out_length] at l0
      have l_n4_a := (wf_n4_a hw).length_le
      have l_n4_c := (wf_n4_c hw).length_le
      rw [(wf_n4f_in hw).getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_n4_a hw).getD_eq_left (by omega), ih.2.2.1 (by omega), ih.2.2.2.2.2.2.2.2.2.2 (by omega), (wf_n4_c hw).getD_eq_left (by omega)]
      rfl
    · have l0 := (wf_n5f_in hw).length_le
      simp only [gateOut_length] at l0
      have l_n5_a := (wf_n5_a hw).length_le
      rw [(wf_n5f_in hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_n5_a hw).getD_eq_left (by omega), ih.2.1 (by omega), ih.2.2.2.2.2.1 (by omega)]
      rfl
    · have l0 := (wf_n5_b hw).length_le
      simp only [gate3Out_length] at l0
      have l_n6_a := (wf_n6_a hw).length_le
      have l_n6_b := (wf_n6_b hw).length_le
      have l_n6_c := (wf_n6_c hw).length_le
      rw [(wf_n5_b hw).getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_n6_a hw).getD_eq_left (by omega), ih.2.2.2.2.1 (by omega), (wf_n6_b hw).getD_eq_left (by omega), ih.2.2.1 (by omega), (wf_n6_c hw).getD_eq_left (by omega)]
      rfl
    · have l0 := (wf_qf_in hw).length_le
      simp only [gateOut_length] at l0
      have l_qg_a := (wf_qg_a hw).length_le
      have l_qg_b := (wf_qg_b hw).length_le
      rw [(wf_qf_in hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_qg_a hw).getD_eq_left (by omega), ih.2.2.2.2.1 (by omega), (wf_qg_b hw).getD_eq_left (by omega)]
      rfl
    · have l0 := (wf_t2_a hw).length_le
      simp only [gate1Out_length] at l0
      have l_nen_a := (wf_nen_a hw).length_le
      rw [(wf_t2_a hw).getD_eq_left hl, gate1Out_getD _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_nen_a hw).getD_eq_left (by omega)]
      rfl
    · have l0 := (wf_mx_a hw).length_le
      simp only [gateOut_length] at l0
      have l_t1_a := (wf_t1_a hw).length_le
      have l_t1_b := (wf_t1_b hw).length_le
      rw [(wf_mx_a hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_t1_a hw).getD_eq_left (by omega), (wf_t1_b hw).getD_eq_left (by omega)]
      rfl
    · have l0 := (wf_mx_b hw).length_le
      simp only [gateOut_length] at l0
      have l_t2_b := (wf_t2_b hw).length_le
      rw [(wf_mx_b hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, ih.2.2.2.2.2.2.2.1 (by omega), (wf_t2_b hw).getD_eq_left (by omega), ih.2.2.2.2.2.2.1 (by omega)]
      rfl
    · have l0 := (wf_n4_b hw).length_le
      simp only [gateOut_length] at l0
      rw [(wf_n4_b hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, ih.2.2.2.2.2.2.2.2.1 (by omega), ih.2.2.2.2.2.2.2.2.2.1 (by omega)]
      rfl

/-- What the block reports is a prefix of the specification's stream. -/
theorem out_q {clk en dat crn : List Bool} {w : Wires W} (hw : Wf (drv clk en dat crn) w) :
    (w .cut_in).take (min (min (w .cut_r1).length (w .cut_r2).length) (min (w .cut_r3).length (w .cut_r4).length) + 1)
      <+: enOut clk en dat crn := by
  have h1 := (wf_cut_r1 hw).length_le
  have h2 := (wf_cut_r2 hw).length_le
  have h3 := (wf_cut_r3 hw).length_le
  have h4 := (wf_cut_r4 hw).length_le
  have h5 := (wf_cut_in hw).length_le
  rw [prefix_iff_length_getD false]
  refine ⟨by simp only [List.length_take, enOut_length]; unfold enLen; omega, fun t ht => ?_⟩
  simp only [List.length_take] at ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
    ← List.getD_eq_getElem?_getD, enOut_getD _ _ _ _ (by unfold enLen; omega)]
  rw [(wf_cut_in hw).getD_eq_left (by omega)]
  exact (wf_sim hw t).2.2.2.2.2.2.1 (by omega)


/-! ### One tactic for every connection -/

syntax "en_case" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| en_case) => `(tactic| (
      obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
      obtain ⟨⟨_, _, _⟩, _, _, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _, _, _, _⟩, ⟨_, _⟩, _⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _, _⟩, _, _, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _, _, _, _⟩, ⟨_, _⟩, _⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e0, e1, e2, e3⟩ := H
      refine ⟨s, existSR_reflexive, Wf_step_of hw drv_mono ?_ ?_, e0, e1, e2, e3⟩
      · intro j
        cases j <;> dsimp only [wires] <;>
          first | exact List.prefix_rfl | exact (‹_ ⊏ _›).isPrefix
      · intro j
        have hj := hw j
        cases j <;> (try dsimp only [wires, drv] at hj) <;> dsimp only [wires, drv] <;>
          first
            | exact hj
            | exact List.prefix_rfl
            | exact e0 ▸ List.prefix_rfl
            | exact e1 ▸ List.prefix_rfl
            | exact e2 ▸ List.prefix_rfl
            | exact e3 ▸ List.prefix_rfl
            | assumption))

/-- Every wire of `mid` is the wire of `i`: what an input rule changes is an input. -/
syntax "en_same" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| en_same) => `(tactic|
      (intro j; cases j <;> dsimp only [wires] <;> exact List.prefix_rfl))

theorem enNetlist_internals_eq : enNetlist.internals =
    [enNetlist.internals.getD 0 (fun _ _ => False), enNetlist.internals.getD 1 (fun _ _ => False), enNetlist.internals.getD 2 (fun _ _ => False),
     enNetlist.internals.getD 3 (fun _ _ => False), enNetlist.internals.getD 4 (fun _ _ => False), enNetlist.internals.getD 5 (fun _ _ => False),
     enNetlist.internals.getD 6 (fun _ _ => False), enNetlist.internals.getD 7 (fun _ _ => False), enNetlist.internals.getD 8 (fun _ _ => False),
     enNetlist.internals.getD 9 (fun _ _ => False), enNetlist.internals.getD 10 (fun _ _ => False), enNetlist.internals.getD 11 (fun _ _ => False),
     enNetlist.internals.getD 12 (fun _ _ => False), enNetlist.internals.getD 13 (fun _ _ => False), enNetlist.internals.getD 14 (fun _ _ => False),
     enNetlist.internals.getD 15 (fun _ _ => False), enNetlist.internals.getD 16 (fun _ _ => False), enNetlist.internals.getD 17 (fun _ _ => False),
     enNetlist.internals.getD 18 (fun _ _ => False), enNetlist.internals.getD 19 (fun _ _ => False), enNetlist.internals.getD 20 (fun _ _ => False),
     enNetlist.internals.getD 21 (fun _ _ => False), enNetlist.internals.getD 22 (fun _ _ => False), enNetlist.internals.getD 23 (fun _ _ => False),
     enNetlist.internals.getD 24 (fun _ _ => False), enNetlist.internals.getD 25 (fun _ _ => False), enNetlist.internals.getD 26 (fun _ _ => False),
     enNetlist.internals.getD 27 (fun _ _ => False), enNetlist.internals.getD 28 (fun _ _ => False), enNetlist.internals.getD 29 (fun _ _ => False),
     enNetlist.internals.getD 30 (fun _ _ => False), enNetlist.internals.getD 31 (fun _ _ => False), enNetlist.internals.getD 32 (fun _ _ => False),
     enNetlist.internals.getD 33 (fun _ _ => False), enNetlist.internals.getD 34 (fun _ _ => False)] := rfl

/-! All 35 connections, one line each. -/

theorem case_0 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n2_b

theorem case_1 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n3_b

theorem case_2 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- cut_r1

theorem case_3 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n2_c

theorem case_4 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n4_c

theorem case_5 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n6_c

theorem case_6 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- qg_b

theorem case_7 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- cut_r4

theorem case_8 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- nen_a

theorem case_9 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- t1_a

theorem case_10 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- cut_r2

theorem case_11 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- t1_b

theorem case_12 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- cut_r3

theorem case_13 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- t2_a

theorem case_14 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- t2_b

theorem case_15 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- cut_in

theorem case_16 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- mx_a

theorem case_17 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- mx_b

theorem case_18 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n4_b

theorem case_19 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n1_a

theorem case_20 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n1_b

theorem case_21 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n2_a

theorem case_22 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n2f_in

theorem case_23 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n3_a

theorem case_24 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n3_c

theorem case_25 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n3f_in

theorem case_26 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n4_a

theorem case_27 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n4f_in

theorem case_28 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 28 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n5_a

theorem case_29 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 29 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n5_b

theorem case_30 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 30 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n5f_in

theorem case_31 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 31 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n6_a

theorem case_32 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 32 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- n6_b

theorem case_33 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 33 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- qg_a

theorem case_34 (s) (i mid : enT) (H : ψ i s)
    (Hrule : (enNetlist.internals.getD 34 (fun _ _ => False)) i mid) :
    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by en_case   -- qf_in

/-! ### The specification's own rules -/

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

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : enNetlist ⊑_{ψ} enSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
    obtain ⟨⟨_, _, _⟩, _, _, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _, _, _, _⟩, ⟨_, _⟩, _⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, e3⟩ := H
    case_transition Hcontains : Module.inputs enNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [enNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    -- The port's identity is decided by `hpre`'s type; the four proofs are one shape.
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← e0]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env (e0 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl
            List.prefix_rfl _)) (by en_same) (by en_same), rfl, e1, e2, e3⟩
      | exact ⟨_, _, spec_in_en s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl (e1 ▸ hpre.isPrefix) List.prefix_rfl
            List.prefix_rfl _)) (by en_same) (by en_same), e0, rfl, e2, e3⟩
      | exact ⟨_, _, spec_in_data s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix)
            List.prefix_rfl _)) (by en_same) (by en_same), e0, e1, rfl, e3⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl List.prefix_rfl
            (e3 ▸ hpre.isPrefix) _)) (by en_same) (by en_same), e0, e1, e2, rfl⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
    obtain ⟨⟨_, _, _⟩, _, _, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _, _, _, _⟩, ⟨_, _⟩, _⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, e3⟩ := H
    have ho := out_q hw
    dsimp only [wires] at ho
    case_transition Hcontains : Module.outputs enNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [enNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ ho, hw, e0, e1, e2, e3⟩
  · intro rule mid_i Hin Hrule
    rw [enNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact case_0 s i mid_i H Hrule
    · subst h; exact case_1 s i mid_i H Hrule
    · subst h; exact case_2 s i mid_i H Hrule
    · subst h; exact case_3 s i mid_i H Hrule
    · subst h; exact case_4 s i mid_i H Hrule
    · subst h; exact case_5 s i mid_i H Hrule
    · subst h; exact case_6 s i mid_i H Hrule
    · subst h; exact case_7 s i mid_i H Hrule
    · subst h; exact case_8 s i mid_i H Hrule
    · subst h; exact case_9 s i mid_i H Hrule
    · subst h; exact case_10 s i mid_i H Hrule
    · subst h; exact case_11 s i mid_i H Hrule
    · subst h; exact case_12 s i mid_i H Hrule
    · subst h; exact case_13 s i mid_i H Hrule
    · subst h; exact case_14 s i mid_i H Hrule
    · subst h; exact case_15 s i mid_i H Hrule
    · subst h; exact case_16 s i mid_i H Hrule
    · subst h; exact case_17 s i mid_i H Hrule
    · subst h; exact case_18 s i mid_i H Hrule
    · subst h; exact case_19 s i mid_i H Hrule
    · subst h; exact case_20 s i mid_i H Hrule
    · subst h; exact case_21 s i mid_i H Hrule
    · subst h; exact case_22 s i mid_i H Hrule
    · subst h; exact case_23 s i mid_i H Hrule
    · subst h; exact case_24 s i mid_i H Hrule
    · subst h; exact case_25 s i mid_i H Hrule
    · subst h; exact case_26 s i mid_i H Hrule
    · subst h; exact case_27 s i mid_i H Hrule
    · subst h; exact case_28 s i mid_i H Hrule
    · subst h; exact case_29 s i mid_i H Hrule
    · subst h; exact case_30 s i mid_i H Hrule
    · subst h; exact case_31 s i mid_i H Hrule
    · subst h; exact case_32 s i mid_i H Hrule
    · subst h; exact case_33 s i mid_i H Hrule
    · subst h; exact case_34 s i mid_i H Hrule

theorem refines_initial : Module.refines_initial enNetlist enSpec ψ := by
  intro i hi
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, enf_in, n5f_in, ⟨qg_a, qg_b⟩, qf_in, ⟨t1_a, t1_b⟩, crf_in, ⟨n5_a, n5_b⟩, ⟨n6_a, n6_b, n6_c⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, dataf_in, ⟨t2_a, t2_b⟩, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨mx_a, mx_b⟩, nen_a⟩ := i
  dsimp only [enNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨([], [], [], []), rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The cell's netlist refines the cell.** -/
theorem en_refines : enNetlist ⊑ enSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.EnReg
