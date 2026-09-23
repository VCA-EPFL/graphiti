/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.DffLemmas

/-!
# The flip-flop: solving its feedback loop, and the proof

The circuit is `components/level3/Dff.lean`; this file proves it refines its contract
`dffSpec` (`DffLemmas.lean`).  The idea of describing the netlist by a six-bit automaton, and
the shape of the invariant, are Kobler's (`CombinationalStream.lean`).

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
then a function of what it was given, which is what the contracts of `Contracts.lean` ask for.
-/


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.Dff

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Over an index rather than a record with one
field per wire, the per-rule lemmas collapse into `Netlist.Wf_set` and `Netlist.Wf_drv`, so
what is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The 26 driven wires. -/
inductive W
  | n2_a
  | n2_b
  | n2_c
  | n5f_in
  | qf_a
  | qf_b
  | n6_a
  | n6_b
  | n6_c
  | n5_a
  | n5_b
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
  | n2f_in
  | cut_in
  | cut_r1
  | cut_r2
  | cut_r3
  deriving DecidableEq

/-- What drives each wire: one line per wire, and the only place the shape of this netlist
is written down. -/
def drv (clk : List Bool) (d : List Bool) (crn : List Bool) : Drv W
  | w, .n2_a => gateOut nand2 (w .n1_a) (w .n1_b)
  | w, .n2_b => clk
  | w, .n2_c => crn
  | w, .n5f_in => gateOut nand2 (w .n5_a) (w .n5_b)
  | w, .qf_a => (w .n5f_in)
  | w, .qf_b => crn
  | w, .n6_a => (w .n5f_in)
  | w, .n6_b => (w .n3f_in)
  | w, .n6_c => crn
  | w, .n5_a => (w .n2f_in)
  | w, .n5_b => gate3Out nand3 (w .n6_a) (w .n6_b) (w .n6_c)
  | w, .n4_a => (w .n3f_in)
  | w, .n4_b => d
  | w, .n4_c => crn
  | w, .n4f_in => gate3Out nand3 (w .n4_a) (w .n4_b) (w .n4_c)
  | w, .n3_a => (w .n2f_in)
  | w, .n3_b => clk
  | w, .n3_c => (w .n4f_in)
  | w, .n1_a => (w .n4f_in)
  | w, .n1_b => (w .n2f_in)
  | w, .n3f_in => gate3Out nand3 (w .n3_a) (w .n3_b) (w .n3_c)
  | w, .n2f_in => gate3Out nand3 (w .n2_a) (w .n2_b) (w .n2_c)
  | w, .cut_in => gateOut and2 (w .qf_a) (w .qf_b)
  | w, .cut_r1 => clk
  | w, .cut_r2 => d
  | w, .cut_r3 => crn

theorem drv_mono {clk d crn} :
    Mono (drv clk d crn) := by
  intro a b h k
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, h, gate3Out_mono, gateOut_mono]
theorem drv_env {clk clk' : List Bool} {d d' : List Bool} {crn crn' : List Bool}
    (hclk : clk <+: clk') (hd : d <+: d') (hcrn : crn <+: crn') (w : Wires W) (k : W) :
    drv clk d crn w k <+:
      drv clk' d' crn' w k := by
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, hclk, hcrn, hd, gate3Out_mono, gateOut_mono]
def wires (i : dffT) : Wires W
  | .n2_a => i.1.1
  | .n2_b => i.1.2.1
  | .n2_c => i.1.2.2
  | .n5f_in => i.2.1
  | .qf_a => i.2.2.2.1.1
  | .qf_b => i.2.2.2.1.2
  | .n6_a => i.2.2.2.2.2.1.1
  | .n6_b => i.2.2.2.2.2.1.2.1
  | .n6_c => i.2.2.2.2.2.1.2.2
  | .n5_a => i.2.2.2.2.2.2.1.1
  | .n5_b => i.2.2.2.2.2.2.1.2
  | .n4_a => i.2.2.2.2.2.2.2.1.1
  | .n4_b => i.2.2.2.2.2.2.2.1.2.1
  | .n4_c => i.2.2.2.2.2.2.2.1.2.2
  | .n4f_in => i.2.2.2.2.2.2.2.2.1
  | .n3_a => i.2.2.2.2.2.2.2.2.2.1.1
  | .n3_b => i.2.2.2.2.2.2.2.2.2.1.2.1
  | .n3_c => i.2.2.2.2.2.2.2.2.2.1.2.2
  | .n1_a => i.2.2.2.2.2.2.2.2.2.2.1.1
  | .n1_b => i.2.2.2.2.2.2.2.2.2.2.1.2
  | .n3f_in => i.2.2.2.2.2.2.2.2.2.2.2.1
  | .n2f_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .cut_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .cut_r1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .cut_r2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .cut_r3 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

def ψ (i : dffT) (s : List Bool × List Bool × List Bool) : Prop :=
  Wf (drv s.1 s.2.1 s.2.2) (wires i)
    ∧ i.2.2.2.2.2.2.2.2.2.2.2.2.1 = s.1
    ∧ i.2.2.1 = s.2.1
    ∧ i.2.2.2.2.1 = s.2.2

/-! ### The invariant, clause by clause

`hw .k` already says this, but with `drv` unapplied; spelling each driver out lets the
simulation proof below rewrite with it exactly as it did against the old record. -/

section Clauses
variable {clk d crn : List Bool} {w : Wires W} (hw : Wf (drv clk d crn) w)
include hw

theorem wf_n2_a : w .n2_a <+: gateOut nand2 (w .n1_a) (w .n1_b) := hw .n2_a
theorem wf_n2_b : w .n2_b <+: clk := hw .n2_b
theorem wf_n2_c : w .n2_c <+: crn := hw .n2_c
theorem wf_n5f_in : w .n5f_in <+: gateOut nand2 (w .n5_a) (w .n5_b) := hw .n5f_in
theorem wf_qf_a : w .qf_a <+: (w .n5f_in) := hw .qf_a
theorem wf_qf_b : w .qf_b <+: crn := hw .qf_b
theorem wf_n6_a : w .n6_a <+: (w .n5f_in) := hw .n6_a
theorem wf_n6_b : w .n6_b <+: (w .n3f_in) := hw .n6_b
theorem wf_n6_c : w .n6_c <+: crn := hw .n6_c
theorem wf_n5_a : w .n5_a <+: (w .n2f_in) := hw .n5_a
theorem wf_n5_b : w .n5_b <+: gate3Out nand3 (w .n6_a) (w .n6_b) (w .n6_c) := hw .n5_b
theorem wf_n4_a : w .n4_a <+: (w .n3f_in) := hw .n4_a
theorem wf_n4_b : w .n4_b <+: d := hw .n4_b
theorem wf_n4_c : w .n4_c <+: crn := hw .n4_c
theorem wf_n4f_in : w .n4f_in <+: gate3Out nand3 (w .n4_a) (w .n4_b) (w .n4_c) := hw .n4f_in
theorem wf_n3_a : w .n3_a <+: (w .n2f_in) := hw .n3_a
theorem wf_n3_b : w .n3_b <+: clk := hw .n3_b
theorem wf_n3_c : w .n3_c <+: (w .n4f_in) := hw .n3_c
theorem wf_n1_a : w .n1_a <+: (w .n4f_in) := hw .n1_a
theorem wf_n1_b : w .n1_b <+: (w .n2f_in) := hw .n1_b
theorem wf_n3f_in : w .n3f_in <+: gate3Out nand3 (w .n3_a) (w .n3_b) (w .n3_c) := hw .n3f_in
theorem wf_n2f_in : w .n2f_in <+: gate3Out nand3 (w .n2_a) (w .n2_b) (w .n2_c) := hw .n2f_in
theorem wf_cut_in : w .cut_in <+: gateOut and2 (w .qf_a) (w .qf_b) := hw .cut_in
theorem wf_cut_r1 : w .cut_r1 <+: clk := hw .cut_r1
theorem wf_cut_r2 : w .cut_r2 <+: d := hw .cut_r2
theorem wf_cut_r3 : w .cut_r3 <+: crn := hw .cut_r3

end Clauses

/-! ### What the netlist computes

`wf_sim` is the simulation -- the wires follow the six-bit automaton of `dffRun` -- and
`out_q` reads the flip-flop's output off it.  This is the block's actual content, and it does
not collapse; only the per-rule bookkeeping around it did. -/

theorem wf_sim {clk d crn : List Bool} {w : Wires W} (hw : Wf (drv clk d crn) w) : ∀ t,
    (t < (w .n2_a).length → (w .n2_a).getD t false = (dffRun clk d crn t).n1) ∧
    (t < (w .n2f_in).length → (w .n2f_in).getD t false = (dffRun clk d crn t).n2) ∧
    (t < (w .n3f_in).length → (w .n3f_in).getD t false = (dffRun clk d crn t).n3) ∧
    (t < (w .n4f_in).length → (w .n4f_in).getD t false = (dffRun clk d crn t).n4) ∧
    (t < (w .n5f_in).length → (w .n5f_in).getD t false = (dffRun clk d crn t).n5) ∧
    (t < (w .n5_b).length → (w .n5_b).getD t false = (dffRun clk d crn t).n6) ∧
    (t < (w .cut_in).length → (w .cut_in).getD t false = qAt clk d crn t) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
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
    · rw [(wf_cut_in hw).getD_eq_left hl, gateOut_getD_zero]
      rfl
  | succ t ih =>
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
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
      have l_n4_b := (wf_n4_b hw).length_le
      have l_n4_c := (wf_n4_c hw).length_le
      rw [(wf_n4f_in hw).getD_eq_left hl, gate3Out_getD _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_n4_a hw).getD_eq_left (by omega), ih.2.2.1 (by omega), (wf_n4_b hw).getD_eq_left (by omega), (wf_n4_c hw).getD_eq_left (by omega)]
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
    · have l0 := (wf_cut_in hw).length_le
      simp only [gateOut_length] at l0
      have l_qf_a := (wf_qf_a hw).length_le
      have l_qf_b := (wf_qf_b hw).length_le
      rw [(wf_cut_in hw).getD_eq_left hl, gateOut_getD _ _ _ (by omega) (by omega), Nat.add_sub_cancel, (wf_qf_a hw).getD_eq_left (by omega), ih.2.2.2.2.1 (by omega), (wf_qf_b hw).getD_eq_left (by omega)]
      rfl

/-- What the block reports is a prefix of what the specification says: the values agree
by `wf_sim`, and the length is what `cut3` allows. -/
theorem out_q {clk d crn : List Bool} {w : Wires W} (hw : Wf (drv clk d crn) w) :
    (w .cut_in).take (min (min (w .cut_r1).length (w .cut_r2).length) (w .cut_r3).length + 1) <+:
      dffOut clk d crn := by
  have h1 := (wf_cut_r1 hw).length_le
  have h2 := (wf_cut_r2 hw).length_le
  have h3 := (wf_cut_r3 hw).length_le
  rw [prefix_iff_length_getD false]
  refine ⟨by simp only [List.length_take, dffOut_length]; unfold dffLen; omega, fun t ht => ?_⟩
  simp only [List.length_take] at ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
    ← List.getD_eq_getElem?_getD, dffOut_getD _ _ _ (by unfold dffLen; omega)]
  exact (wf_sim hw t).2.2.2.2.2.2 (by omega)

/-! ### One tactic for every connection -/

syntax "dff_case " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| dff_case $w:term) => `(tactic| (
      obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
      obtain ⟨⟨_, _, _⟩, _, _, ⟨_, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _, _⟩, _, _, ⟨_, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e0, e1, e2⟩ := H
      refine ⟨s, existSR_reflexive, Wf_step_of hw drv_mono ?_ ?_, e0, e1, e2⟩
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
            | exact e2 ▸ List.prefix_rfl))

theorem dffNetlist_internals_eq : dffNetlist.internals =
    [dffNetlist.internals.getD 0 (fun _ _ => False), dffNetlist.internals.getD 1 (fun _ _ => False), dffNetlist.internals.getD 2 (fun _ _ => False),
     dffNetlist.internals.getD 3 (fun _ _ => False), dffNetlist.internals.getD 4 (fun _ _ => False), dffNetlist.internals.getD 5 (fun _ _ => False),
     dffNetlist.internals.getD 6 (fun _ _ => False), dffNetlist.internals.getD 7 (fun _ _ => False), dffNetlist.internals.getD 8 (fun _ _ => False),
     dffNetlist.internals.getD 9 (fun _ _ => False), dffNetlist.internals.getD 10 (fun _ _ => False), dffNetlist.internals.getD 11 (fun _ _ => False),
     dffNetlist.internals.getD 12 (fun _ _ => False), dffNetlist.internals.getD 13 (fun _ _ => False), dffNetlist.internals.getD 14 (fun _ _ => False),
     dffNetlist.internals.getD 15 (fun _ _ => False), dffNetlist.internals.getD 16 (fun _ _ => False), dffNetlist.internals.getD 17 (fun _ _ => False),
     dffNetlist.internals.getD 18 (fun _ _ => False), dffNetlist.internals.getD 19 (fun _ _ => False), dffNetlist.internals.getD 20 (fun _ _ => False),
     dffNetlist.internals.getD 21 (fun _ _ => False), dffNetlist.internals.getD 22 (fun _ _ => False), dffNetlist.internals.getD 23 (fun _ _ => False),
     dffNetlist.internals.getD 24 (fun _ _ => False), dffNetlist.internals.getD 25 (fun _ _ => False)] := rfl

/-! All 26 connections, one line each. -/

theorem case_0 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n2_b

theorem case_1 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n3_b

theorem case_2 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.cut_r1

theorem case_3 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n4_b

theorem case_4 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.cut_r2

theorem case_5 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n2_c

theorem case_6 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n4_c

theorem case_7 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n6_c

theorem case_8 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.qf_b

theorem case_9 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.cut_r3

theorem case_10 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n1_a

theorem case_11 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n1_b

theorem case_12 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n2_a

theorem case_13 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n2f_in

theorem case_14 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n3_a

theorem case_15 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n3_c

theorem case_16 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n3f_in

theorem case_17 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n4_a

theorem case_18 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n4f_in

theorem case_19 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n5_a

theorem case_20 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n5_b

theorem case_21 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n5f_in

theorem case_22 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n6_a

theorem case_23 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.n6_b

theorem case_24 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.qf_a

theorem case_25 (s) (i mid : dffT) (H : ψ i s)
    (Hrule : (dffNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by dff_case W.cut_in

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

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : dffNetlist ⊑_{ψ} dffSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
    obtain ⟨⟨_, _, _⟩, _, _, ⟨_, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2⟩ := H
    case_transition Hcontains : Module.inputs dffNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [dffNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    -- The port's identity is decided by `hpre`'s type; the proofs are one shape.
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← e0]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env (e0 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl _), rfl, e1, e2⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl (e1 ▸ hpre.isPrefix) List.prefix_rfl _), e0, rfl, e2⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix) _), e0, e1, rfl⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
    obtain ⟨⟨_, _, _⟩, _, _, ⟨_, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2⟩ := H
    case_transition Hcontains : Module.outputs dffNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [dffNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    simp only [eq_mp_eq_cast, cast_self]
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ (out_q hw), hw, e0, e1, e2⟩
  · intro rule mid_i Hin Hrule
    rw [dffNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
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

theorem refines_initial : Module.refines_initial dffNetlist dffSpec ψ := by
  intro i hi
  obtain ⟨⟨n2_a, n2_b, n2_c⟩, n5f_in, df_in, ⟨qf_a, qf_b⟩, crf_in, ⟨n6_a, n6_b, n6_c⟩, ⟨n5_a, n5_b⟩, ⟨n4_a, n4_b, n4_c⟩, n4f_in, ⟨n3_a, n3_b, n3_c⟩, ⟨n1_a, n1_b⟩, n3f_in, clkf_in, n2f_in, ⟨cut_in, cut_r1, cut_r2, cut_r3⟩⟩ := i
  dsimp only [dffNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  repeat' (obtain ⟨rfl, hi⟩ := hi)
  refine ⟨([], [], []), rfl, ?_, rfl, rfl, rfl⟩
  intro k; cases k <;> exact List.nil_prefix

theorem dff_refines : dffNetlist ⊑ dffSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩


/-- **The flip-flop as gates refines its contract.** -/
theorem dffImpl_refines : dffImpl ⊑ dffSpec :=
  Module.refines_transitive _ (Module.refines_eq' dffNetlist_sigma.symm) dff_refines

end Graphiti.AsyncFifo.Dff
