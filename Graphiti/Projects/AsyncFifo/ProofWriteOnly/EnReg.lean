/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Dff
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.EnRegLemmas

/-!
# The memory cell: its behaviour, and the proof

The circuit is `components/level4/EnReg.lean`.  For the proof its flip-flop stands for its
contract `Dff.dffSpec` (`EnRegLemmas.eenv`).  That is sound across the loop because `dffOut` is
a `timeline` of length `dffLen + 1`: the flip-flop as a block emits one instant past its
shortest input exactly as a gate does, while `Netlist.Wf` never mentions the topology.

What the loop *does* force is the cell's **behaviour**, which is a fixpoint and not a
composition: the flip-flop is given a stream that depends on what it produces, so the cell is a
sequential circuit whose state includes the flip-flop's, and `enRun` is that combined automaton.
Those are two different claims, and an earlier version of this comment ran them together and
concluded, wrongly, that the netlist had to be flat.

The two meet in `enOut_eq`: the cell's output is the flip-flop's output over the multiplexer's
stream.  So `wf_sim` below induces over the multiplexer only --- four wires --- and the
flip-flop's six come from `dffRun`, which is what `enRun_ff` says.  `EnRegTiming.lean` then
inherits the whole timing analysis of `DffTiming.lean` with `d := mStream`, and the only new
work is what the multiplexer does around an edge.
-/


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.EnReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Dff

/-! ### The netlist, as an index type

Sixteen wires, against the thirty-five the flat version needed: the flip-flop's six NANDs and
their forks are behind `Dff.dffSpec` now, and only the multiplexer is gates. -/

open Graphiti.AsyncFifo.Netlist

/-- The sixteen driven wires. -/
inductive W
  | nen_a | t1_a | t1_b | t2_a | t2_b | mx_a | mx_b
  | ff_clk | ff_d | ff_crn | qf_in
  | cut_in | cut_r1 | cut_r2 | cut_r3 | cut_r4
  deriving DecidableEq

/-- What drives each wire.  `qf_in` is driven by the *flip-flop*, `dffOut`, and `t2_b` reads it
back: that is the loop, and it is a loop through a block. -/
def drv (clk en dat crn : List Bool) : Drv W
  | _, .nen_a => en
  | _, .t1_a => en
  | _, .t1_b => dat
  | w, .t2_a => gate1Out not (w .nen_a)
  | w, .t2_b => w .qf_in
  | w, .mx_a => gateOut and2 (w .t1_a) (w .t1_b)
  | w, .mx_b => gateOut and2 (w .t2_a) (w .t2_b)
  | _, .ff_clk => clk
  | w, .ff_d => gateOut or2 (w .mx_a) (w .mx_b)
  | _, .ff_crn => crn
  | w, .qf_in => dffOut (w .ff_clk) (w .ff_d) (w .ff_crn)
  | w, .cut_in => w .qf_in
  | _, .cut_r1 => clk
  | _, .cut_r2 => en
  | _, .cut_r3 => dat
  | _, .cut_r4 => crn

/-- The cases are named rather than left to a search: `dffOut_mono`'s conclusion is a deep
definition, and offering it to a goal it does not fit makes the unifier unfold it. -/
theorem drv_mono {clk en dat crn} : Mono (drv clk en dat crn) := by
  intro a b h k
  cases k <;> simp only [drv]
  case t2_a => exact gate1Out_mono _ (h .nen_a)
  case t2_b => exact h .qf_in
  case mx_a => exact gateOut_mono _ (h .t1_a) (h .t1_b)
  case mx_b => exact gateOut_mono _ (h .t2_a) (h .t2_b)
  case ff_d => exact gateOut_mono _ (h .mx_a) (h .mx_b)
  case qf_in => exact dffOut_mono (h .ff_clk) (h .ff_d) (h .ff_crn)
  case cut_in => exact h .qf_in
  all_goals exact List.prefix_rfl

/-- Growing the cell's own inputs grows every driver. -/
theorem drv_env {clk clk' en en' dat dat' crn crn' : List Bool}
    (hclk : clk <+: clk') (hen : en <+: en') (hdat : dat <+: dat') (hcrn : crn <+: crn')
    (w : Wires W) (k : W) : drv clk en dat crn w k <+: drv clk' en' dat' crn' w k := by
  cases k <;> simp only [drv]
  case nen_a => exact hen
  case t1_a => exact hen
  case t1_b => exact hdat
  case ff_clk => exact hclk
  case ff_crn => exact hcrn
  case cut_r1 => exact hclk
  case cut_r2 => exact hen
  case cut_r3 => exact hdat
  case cut_r4 => exact hcrn
  all_goals exact List.prefix_rfl

/-- The reduced state is a nested product; `wires` reads it as an assignment. -/
def wires (i : enT) : Wires W
  | .t1_a => i.1.1 | .t1_b => i.1.2
  | .t2_a => i.2.2.2.2.2.1.1 | .t2_b => i.2.2.2.2.2.1.2
  | .cut_in => i.2.2.2.2.2.2.1.1
  | .cut_r1 => i.2.2.2.2.2.2.1.2.1 | .cut_r2 => i.2.2.2.2.2.2.1.2.2.1
  | .cut_r3 => i.2.2.2.2.2.2.1.2.2.2.1 | .cut_r4 => i.2.2.2.2.2.2.1.2.2.2.2
  | .ff_clk => i.2.2.2.2.2.2.2.1.1 | .ff_d => i.2.2.2.2.2.2.2.1.2.1
  | .ff_crn => i.2.2.2.2.2.2.2.1.2.2
  | .qf_in => i.2.2.2.2.2.2.2.2.1
  | .nen_a => i.2.2.2.2.2.2.2.2.2.1
  | .mx_a => i.2.2.2.2.2.2.2.2.2.2.1 | .mx_b => i.2.2.2.2.2.2.2.2.2.2.2

def ψ (i : enT) (s : List Bool × List Bool × List Bool × List Bool) : Prop :=
  Wf (drv s.1 s.2.1 s.2.2.1 s.2.2.2) (wires i)
    ∧ i.2.2.2.2.1 = s.1 ∧ i.2.2.1 = s.2.1 ∧ i.2.2.2.1 = s.2.2.1 ∧ i.2.1 = s.2.2.2

/-! ### The invariant, clause by clause -/

section Clauses
variable {clk en dat crn : List Bool} {w : Wires W} (hw : Wf (drv clk en dat crn) w)
include hw

theorem wf_nen_a : w .nen_a <+: en := hw .nen_a
theorem wf_t1_a : w .t1_a <+: en := hw .t1_a
theorem wf_t1_b : w .t1_b <+: dat := hw .t1_b
theorem wf_t2_a : w .t2_a <+: gate1Out not (w .nen_a) := hw .t2_a
theorem wf_t2_b : w .t2_b <+: (w .qf_in) := hw .t2_b
theorem wf_mx_a : w .mx_a <+: gateOut and2 (w .t1_a) (w .t1_b) := hw .mx_a
theorem wf_mx_b : w .mx_b <+: gateOut and2 (w .t2_a) (w .t2_b) := hw .mx_b
theorem wf_ff_clk : w .ff_clk <+: clk := hw .ff_clk
theorem wf_ff_d : w .ff_d <+: gateOut or2 (w .mx_a) (w .mx_b) := hw .ff_d
theorem wf_ff_crn : w .ff_crn <+: crn := hw .ff_crn
theorem wf_qf_in : w .qf_in <+: dffOut (w .ff_clk) (w .ff_d) (w .ff_crn) := hw .qf_in
theorem wf_cut_in : w .cut_in <+: (w .qf_in) := hw .cut_in
theorem wf_cut_r1 : w .cut_r1 <+: clk := hw .cut_r1
theorem wf_cut_r2 : w .cut_r2 <+: en := hw .cut_r2
theorem wf_cut_r3 : w .cut_r3 <+: dat := hw .cut_r3
theorem wf_cut_r4 : w .cut_r4 <+: crn := hw .cut_r4

end Clauses

/-! ### What the netlist computes

The flip-flop's own six wires are gone from this induction: they are `dffRun`, and the first
clause below says so.  What is left is the multiplexer, four wires of it, and the one step that
reads the flip-flop's output back. -/

theorem wf_sim {clk en dat crn : List Bool} {w : Wires W} (hw : Wf (drv clk en dat crn) w) :
    ∀ t,
    (t ≤ dffLen (w .ff_clk) (w .ff_d) (w .ff_crn) →
      dffRun (w .ff_clk) (w .ff_d) (w .ff_crn) t = ffOf (enRun clk en dat crn t)) ∧
    (t < (w .t2_a).length → (w .t2_a).getD t false = (enRun clk en dat crn t).nen) ∧
    (t < (w .mx_a).length → (w .mx_a).getD t false = (enRun clk en dat crn t).t1) ∧
    (t < (w .mx_b).length → (w .mx_b).getD t false = (enRun clk en dat crn t).t2) ∧
    (t < (w .ff_d).length → (w .ff_d).getD t false = (enRun clk en dat crn t).m) ∧
    (t < (w .qf_in).length → (w .qf_in).getD t false = (enRun clk en dat crn t).q) ∧
    (t < (w .t2_b).length → (w .t2_b).getD t false = (enRun clk en dat crn t).q) := by
  have lnen := (wf_nen_a hw).length_le
  have lt1a := (wf_t1_a hw).length_le
  have lt1b := (wf_t1_b hw).length_le
  have lt2a := (wf_t2_a hw).length_le
  have lt2b := (wf_t2_b hw).length_le
  have lmxa := (wf_mx_a hw).length_le
  have lmxb := (wf_mx_b hw).length_le
  have lffd := (wf_ff_d hw).length_le
  have lffc := (wf_ff_clk hw).length_le
  have lffr := (wf_ff_crn hw).length_le
  have lqf := (wf_qf_in hw).length_le
  simp only [gate1Out_length, gateOut_length, dffOut_length, dffLen] at lt2a lmxa lmxb lffd lqf
  -- one bound per wire, with the `min`s taken apart: `omega` is never handed a nested one
  have bmxa1 : (w .mx_a).length ≤ (w .t1_a).length + 1 := by omega
  have bmxa2 : (w .mx_a).length ≤ (w .t1_b).length + 1 := by omega
  have bmxb1 : (w .mx_b).length ≤ (w .t2_a).length + 1 := by omega
  have bmxb2 : (w .mx_b).length ≤ (w .t2_b).length + 1 := by omega
  have bffd1 : (w .ff_d).length ≤ (w .mx_a).length + 1 := by omega
  have bffd2 : (w .ff_d).length ≤ (w .mx_b).length + 1 := by omega
  have bqf1 : (w .qf_in).length ≤ (w .ff_clk).length + 1 := by omega
  have bqf2 : (w .qf_in).length ≤ (w .ff_d).length + 1 := by omega
  have bqf3 : (w .qf_in).length ≤ (w .ff_crn).length + 1 := by omega
  clear lmxa lmxb lffd lqf
  intro t
  induction t with
  | zero =>
    have hq : 0 < (w .qf_in).length → (w .qf_in).getD 0 false = (enRun clk en dat crn 0).q := by
      intro hl
      rw [(wf_qf_in hw).getD_eq_left hl, dffOut_getD _ _ _ (by omega)]
      rfl
    refine ⟨fun _ => rfl, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, hq, fun hl => ?_⟩
    · rw [(wf_t2_a hw).getD_eq_left hl, gate1Out_getD_zero]; rfl
    · rw [(wf_mx_a hw).getD_eq_left hl, gateOut_getD_zero]; rfl
    · rw [(wf_mx_b hw).getD_eq_left hl, gateOut_getD_zero]; rfl
    · rw [(wf_ff_d hw).getD_eq_left hl, gateOut_getD_zero]; rfl
    · rw [(wf_t2_b hw).getD_eq_left hl]; exact hq (by omega)
  | succ t ih =>
    obtain ⟨iff', it2a, imxa, imxb, iffd, iqf, it2b⟩ := ih
    -- the flip-flop's own state, one `dffStep` against one `enStep`
    have hff : t + 1 ≤ dffLen (w .ff_clk) (w .ff_d) (w .ff_crn) →
        dffRun (w .ff_clk) (w .ff_d) (w .ff_crn) (t + 1) = ffOf (enRun clk en dat crn (t + 1)) := by
      intro hl
      simp only [dffLen] at hl
      have e1 : dffRun (w .ff_clk) (w .ff_d) (w .ff_crn) (t + 1) =
          dffStep (dffRun (w .ff_clk) (w .ff_d) (w .ff_crn) t)
            (dffInp (w .ff_clk) (w .ff_d) (w .ff_crn) t) := rfl
      have e2 : enRun clk en dat crn (t + 1) =
          enStep (enRun clk en dat crn t) (enInp clk en dat crn t) := rfl
      rw [e1, iff' (by simp only [dffLen]; omega), e2]
      unfold dffInp enInp ffOf dffStep enStep
      rw [(wf_ff_clk hw).getD_eq_left (by omega), (wf_ff_crn hw).getD_eq_left (by omega),
        iffd (by omega)]
    have hq : t + 1 < (w .qf_in).length →
        (w .qf_in).getD (t + 1) false = (enRun clk en dat crn (t + 1)).q := by
      intro hl
      rw [(wf_qf_in hw).getD_eq_left hl, dffOut_getD _ _ _ (by simp only [dffLen]; omega)]
      show and2 (dffRun (w .ff_clk) (w .ff_d) (w .ff_crn) t).n5 ((w .ff_crn).getD t false) = _
      rw [iff' (by simp only [dffLen]; omega), (wf_ff_crn hw).getD_eq_left (by omega)]
      rfl
    refine ⟨hff, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, hq, fun hl => ?_⟩
    · rw [(wf_t2_a hw).getD_eq_left hl, gate1Out_getD _ _ (by omega) (by omega),
        Nat.add_sub_cancel, (wf_nen_a hw).getD_eq_left (by omega)]
      rfl
    · rw [(wf_mx_a hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega),
        Nat.add_sub_cancel, (wf_t1_a hw).getD_eq_left (by omega),
        (wf_t1_b hw).getD_eq_left (by omega)]
      rfl
    · rw [(wf_mx_b hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega),
        Nat.add_sub_cancel, it2a (by omega), it2b (by omega)]
      rfl
    · rw [(wf_ff_d hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega),
        Nat.add_sub_cancel, imxa (by omega), imxb (by omega)]
      rfl
    · rw [(wf_t2_b hw).getD_eq_left hl]; exact hq (by omega)

/-- What the cell reports is a prefix of what the specification says. -/
theorem out_q {clk en dat crn : List Bool} {w : Wires W} (hw : Wf (drv clk en dat crn) w) :
    (w .cut_in).take (min (min (w .cut_r1).length (w .cut_r2).length)
        (min (w .cut_r3).length (w .cut_r4).length) + 1) <+: enOut clk en dat crn := by
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
  exact (wf_sim hw t).2.2.2.2.2.1 (by omega)

/-! ### One tactic for every connection -/

syntax "en_case" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| en_case) => `(tactic| (
      obtain ⟨⟨t1_a, t1_b⟩, crf_in, enf_in, dataf_in, clkf_in, ⟨t2_a, t2_b⟩,
        ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨ff_clk, ff_d, ff_crn⟩, qf_in, nen_a,
        ⟨mx_a, mx_b⟩⟩ := i
      obtain ⟨⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _⟩, _, _, ⟨_, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _⟩, _, _, ⟨_, _⟩⟩, out, Hr⟩ := Hr
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
            | assumption
            | exact List.prefix_rfl
            | exact e0 ▸ List.prefix_rfl
            | exact e1 ▸ List.prefix_rfl
            | exact e2 ▸ List.prefix_rfl
            | exact e3 ▸ List.prefix_rfl))

theorem enNetlist_internals_eq : enNetlist.internals =
    [enNetlist.internals.getD 0 (fun _ _ => False), enNetlist.internals.getD 1 (fun _ _ => False),
     enNetlist.internals.getD 2 (fun _ _ => False), enNetlist.internals.getD 3 (fun _ _ => False),
     enNetlist.internals.getD 4 (fun _ _ => False), enNetlist.internals.getD 5 (fun _ _ => False),
     enNetlist.internals.getD 6 (fun _ _ => False), enNetlist.internals.getD 7 (fun _ _ => False),
     enNetlist.internals.getD 8 (fun _ _ => False), enNetlist.internals.getD 9 (fun _ _ => False),
     enNetlist.internals.getD 10 (fun _ _ => False), enNetlist.internals.getD 11 (fun _ _ => False),
     enNetlist.internals.getD 12 (fun _ _ => False), enNetlist.internals.getD 13 (fun _ _ => False),
     enNetlist.internals.getD 14 (fun _ _ => False), enNetlist.internals.getD 15 (fun _ _ => False)]
    := rfl


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
    obtain ⟨⟨t1_a, t1_b⟩, crf_in, enf_in, dataf_in, clkf_in, ⟨t2_a, t2_b⟩,
      ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨ff_clk, ff_d, ff_crn⟩, qf_in, nen_a,
      ⟨mx_a, mx_b⟩⟩ := i
    obtain ⟨⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _⟩, _, _, ⟨_, _⟩⟩ := mid_i
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
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← e0]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env (e0 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl
            List.prefix_rfl _), rfl, e1, e2, e3⟩
      | exact ⟨_, _, spec_in_en s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl (e1 ▸ hpre.isPrefix) List.prefix_rfl
            List.prefix_rfl _), e0, rfl, e2, e3⟩
      | exact ⟨_, _, spec_in_data s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix)
            List.prefix_rfl _), e0, e1, rfl, e3⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl List.prefix_rfl
            (e3 ▸ hpre.isPrefix) _), e0, e1, e2, rfl⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨t1_a, t1_b⟩, crf_in, enf_in, dataf_in, clkf_in, ⟨t2_a, t2_b⟩,
      ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨ff_clk, ff_d, ff_crn⟩, qf_in, nen_a,
      ⟨mx_a, mx_b⟩⟩ := i
    obtain ⟨⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _⟩, _, _, ⟨_, _⟩⟩ := mid_i
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
  · intro rule mid Hin Hrule
    rw [enNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals (subst h; en_case)

theorem refines_initial : Module.refines_initial enNetlist enSpec ψ := by
  intro i hi
  obtain ⟨⟨t1_a, t1_b⟩, crf_in, enf_in, dataf_in, clkf_in, ⟨t2_a, t2_b⟩,
    ⟨cut_in, cut_r1, cut_r2, cut_r3, cut_r4⟩, ⟨ff_clk, ff_d, ff_crn⟩, qf_in, nen_a,
    ⟨mx_a, mx_b⟩⟩ := i
  dsimp only [enNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨([], [], [], []), rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The cell's netlist refines the cell** --- and the flip-flop in it is `Dff`'s, as a block. -/
theorem en_refines : enNetlist ⊑ enSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩


end Graphiti.AsyncFifo.EnReg
