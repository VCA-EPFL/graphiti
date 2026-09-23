/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Dff
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Timed
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteStateLemmas

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.WriteState

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Dff

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Stated over an index rather than as a record
with one field per wire, the per-rule lemmas collapse into `Netlist.Wf_set` and
`Netlist.Wf_drv`, so what is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The 28 driven wires. -/
inductive W | pk0 | pk1 | pk2 | pk3 | pk4 | pk5 | pk6
            | f0clk | f0d | f0crn
            | f1clk | f1d | f1crn
            | f2clk | f2d | f2crn
            | f3clk | f3d | f3crn
            | f4clk | f4d | f4crn
            | f5clk | f5d | f5crn
            | f6clk | f6d | f6crn
  deriving DecidableEq

/-- What drives each wire: one line per wire, and the only place the shape of this netlist
is written down. -/
def drv (clk crn : List Bool) (d : List (WSt 2)) : Drv W
  | w, .pk0 => dffOut (w .f0clk) (w .f0d) (w .f0crn)
  | w, .pk1 => dffOut (w .f1clk) (w .f1d) (w .f1crn)
  | w, .pk2 => dffOut (w .f2clk) (w .f2d) (w .f2crn)
  | w, .pk3 => dffOut (w .f3clk) (w .f3d) (w .f3crn)
  | w, .pk4 => dffOut (w .f4clk) (w .f4d) (w .f4crn)
  | w, .pk5 => dffOut (w .f5clk) (w .f5d) (w .f5crn)
  | w, .pk6 => dffOut (w .f6clk) (w .f6d) (w .f6crn)
  | _, .f0clk | _, .f1clk | _, .f2clk | _, .f3clk | _, .f4clk | _, .f5clk | _, .f6clk => clk
  | _, .f0crn | _, .f1crn | _, .f2crn | _, .f3crn | _, .f4crn | _, .f5crn | _, .f6crn => crn
  | _, .f0d => bitsOf 0 d
  | _, .f1d => bitsOf 1 d
  | _, .f2d => bitsOf 2 d
  | _, .f3d => bitsOf 3 d
  | _, .f4d => bitsOf 4 d
  | _, .f5d => bitsOf 5 d
  | _, .f6d => bitsOf 6 d

theorem drv_mono {clk crn d} : Mono (drv clk crn d) := by
  intro a b h k
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, h, dffOut_mono]
theorem drv_env {clk clk' crn crn' : List Bool} {d d' : List (WSt 2)}
    (hc : clk <+: clk') (hr : crn <+: crn') (hd : d <+: d') (w : Wires W) (k : W) :
    drv clk crn d w k <+: drv clk' crn' d' w k := by
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, hc, hd, hr, bitsOf_mono]
def wires (i : stT) : Wires W
  | .pk0 => i.1.1
  | .pk1 => i.1.2.1
  | .pk2 => i.1.2.2.1
  | .pk3 => i.1.2.2.2.1
  | .pk4 => i.1.2.2.2.2.1
  | .pk5 => i.1.2.2.2.2.2.1
  | .pk6 => i.1.2.2.2.2.2.2
  | .f0clk => i.2.2.2.2.2.2.2.2.1.1 | .f0d => i.2.2.2.2.2.2.2.2.1.2.1 | .f0crn => i.2.2.2.2.2.2.2.2.1.2.2
  | .f1clk => i.2.2.2.2.2.2.2.2.2.1.1 | .f1d => i.2.2.2.2.2.2.2.2.2.1.2.1 | .f1crn => i.2.2.2.2.2.2.2.2.2.1.2.2
  | .f2clk => i.2.2.2.2.2.2.2.2.2.2.1 | .f2d => i.2.2.2.2.2.2.2.2.2.2.2.1 | .f2crn => i.2.2.2.2.2.2.2.2.2.2.2.2
  | .f3clk => i.2.2.2.2.2.2.1.1 | .f3d => i.2.2.2.2.2.2.1.2.1 | .f3crn => i.2.2.2.2.2.2.1.2.2
  | .f4clk => i.2.2.2.2.2.2.2.1.1 | .f4d => i.2.2.2.2.2.2.2.1.2.1 | .f4crn => i.2.2.2.2.2.2.2.1.2.2
  | .f5clk => i.2.2.2.2.1.1 | .f5d => i.2.2.2.2.1.2.1 | .f5crn => i.2.2.2.2.1.2.2
  | .f6clk => i.2.1.1 | .f6d => i.2.1.2.1 | .f6crn => i.2.1.2.2

def ψ (i : stT) (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) : Prop :=
  Wf (drv s.1 s.2.2.1 s.2.1) (wires i) ∧ i.2.2.2.2.2.1 = s.1 ∧ i.2.2.1 = s.2.1
    ∧ i.2.2.2.1 = s.2.2.1 ∧ s.2.2.2 <+: packStOut (wires i .pk0) (wires i .pk1) (wires i .pk2) (wires i .pk3) (wires i .pk4) (wires i .pk5) (wires i .pk6)

/-- What the block reports is a prefix of what the specification says. -/
theorem out_q {clk crn d} {w : Wires W} (hw : Wf (drv clk crn d) w) :
    packStOut (w .pk0) (w .pk1) (w .pk2) (w .pk3) (w .pk4) (w .pk5) (w .pk6) <+: stOut clk d crn := by
  refine packStOut_mono ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (hw .pk0).trans (dffOut_mono (hw .f0clk) (hw .f0d) (hw .f0crn))
  · exact (hw .pk1).trans (dffOut_mono (hw .f1clk) (hw .f1d) (hw .f1crn))
  · exact (hw .pk2).trans (dffOut_mono (hw .f2clk) (hw .f2d) (hw .f2crn))
  · exact (hw .pk3).trans (dffOut_mono (hw .f3clk) (hw .f3d) (hw .f3crn))
  · exact (hw .pk4).trans (dffOut_mono (hw .f4clk) (hw .f4d) (hw .f4crn))
  · exact (hw .pk5).trans (dffOut_mono (hw .f5clk) (hw .f5d) (hw .f5crn))
  · exact (hw .pk6).trans (dffOut_mono (hw .f6clk) (hw .f6d) (hw .f6crn))

/-! ### One tactic for every connection -/

syntax "st_case " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| st_case $w:term) => `(tactic| (
      obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6⟩, ⟨x6,y6,z6⟩, ud, cr, ⟨x5,y5,z5⟩, ck, ⟨x3,y3,z3⟩, ⟨x4,y4,z4⟩, ⟨x0,y0,z0⟩, ⟨x1,y1,z1⟩, ⟨x2,y2,z2⟩⟩ := i
      obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_,_,_⟩, _, _, ⟨_,_,_⟩, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _, _, _, _, _, _⟩, ⟨_,_,_⟩, _, _, ⟨_,_,_⟩, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e1, e2, e3, hq⟩ := H
      refine ⟨s, existSR_reflexive, ?_, e1, e2, e3, ?_⟩
      · have key := Wf_set drv_mono hw $w _ (‹_ ⊏ _›).isPrefix (by
          simp only [drv, wires]
          first
            | exact e1 ▸ List.prefix_rfl
            | exact e3 ▸ List.prefix_rfl
            | exact e2 ▸ List.prefix_rfl
            | assumption)
        intro j; have hj := key j; revert hj; cases j <;> simp [wires, upd, drv]
      · have key := hq.trans (packStOut_mono
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          )
        revert key; simp [wires, upd]))

theorem stNetlist_internals_eq : stNetlist.internals =
    [stNetlist.internals.getD 0 (fun _ _ => False), stNetlist.internals.getD 1 (fun _ _ => False), stNetlist.internals.getD 2 (fun _ _ => False),
     stNetlist.internals.getD 3 (fun _ _ => False), stNetlist.internals.getD 4 (fun _ _ => False), stNetlist.internals.getD 5 (fun _ _ => False),
     stNetlist.internals.getD 6 (fun _ _ => False), stNetlist.internals.getD 7 (fun _ _ => False), stNetlist.internals.getD 8 (fun _ _ => False),
     stNetlist.internals.getD 9 (fun _ _ => False), stNetlist.internals.getD 10 (fun _ _ => False), stNetlist.internals.getD 11 (fun _ _ => False),
     stNetlist.internals.getD 12 (fun _ _ => False), stNetlist.internals.getD 13 (fun _ _ => False), stNetlist.internals.getD 14 (fun _ _ => False),
     stNetlist.internals.getD 15 (fun _ _ => False), stNetlist.internals.getD 16 (fun _ _ => False), stNetlist.internals.getD 17 (fun _ _ => False),
     stNetlist.internals.getD 18 (fun _ _ => False), stNetlist.internals.getD 19 (fun _ _ => False), stNetlist.internals.getD 20 (fun _ _ => False),
     stNetlist.internals.getD 21 (fun _ _ => False), stNetlist.internals.getD 22 (fun _ _ => False), stNetlist.internals.getD 23 (fun _ _ => False),
     stNetlist.internals.getD 24 (fun _ _ => False), stNetlist.internals.getD 25 (fun _ _ => False), stNetlist.internals.getD 26 (fun _ _ => False),
     stNetlist.internals.getD 27 (fun _ _ => False)] := rfl

/-! All 28 connections, one line each. -/

theorem case_0 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f0clk

theorem case_1 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f1clk

theorem case_2 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f2clk

theorem case_3 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f3clk

theorem case_4 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f4clk

theorem case_5 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f5clk

theorem case_6 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f6clk

theorem case_7 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f0crn

theorem case_8 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f1crn

theorem case_9 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f2crn

theorem case_10 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f3crn

theorem case_11 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f4crn

theorem case_12 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f5crn

theorem case_13 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f6crn

theorem case_14 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f0d

theorem case_15 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f1d

theorem case_16 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f2d

theorem case_17 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f3d

theorem case_18 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f4d

theorem case_19 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f5d

theorem case_20 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f6d

theorem case_21 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk0

theorem case_22 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk1

theorem case_23 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk2

theorem case_24 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk3

theorem case_25 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk4

theorem case_26 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk5

theorem case_27 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk6
/-! ### The specification's own rules -/

section SpecRules
variable (sp : List Bool × List (WSt 2) × List Bool × List (WSt 2))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (stSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (WSt 2)) (h : sp.2.1 ⊏ v) :
    (stSpec.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (stSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List (WSt 2)) (h1 : sp.2.2.2 <+: v)
    (h2 : v <+: stOut sp.1 sp.2.1 sp.2.2.1) :
    (stSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : stNetlist ⊑_{ψ} stSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6⟩, ⟨x6,y6,z6⟩, ud, cr, ⟨x5,y5,z5⟩, ck, ⟨x3,y3,z3⟩, ⟨x4,y4,z4⟩, ⟨x0,y0,z0⟩, ⟨x1,y1,z1⟩, ⟨x2,y2,z2⟩⟩ := i
    obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_,_,_⟩, _, _, ⟨_,_,_⟩, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, hq⟩ := H
    case_transition Hcontains : Module.inputs stNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [stNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    -- The port's identity is decided by `hpre`'s type; the three proofs are one shape.
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env (e1 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl _),
          rfl, e2, e3, hq⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix) _),
          e1, rfl, e3, hq⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl (e3 ▸ hpre.isPrefix) List.prefix_rfl _),
          e1, e2, rfl, hq⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6⟩, ⟨x6,y6,z6⟩, ud, cr, ⟨x5,y5,z5⟩, ck, ⟨x3,y3,z3⟩, ⟨x4,y4,z4⟩, ⟨x0,y0,z0⟩, ⟨x1,y1,z1⟩, ⟨x2,y2,z2⟩⟩ := i
    obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_,_,_⟩, _, _, ⟨_,_,_⟩, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, hq⟩ := H
    case_transition Hcontains : Module.outputs stNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [stNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    simp only [eq_mp_eq_cast, cast_self]
    dsimp only [wires] at hq
    have ho := out_q hw
    dsimp only [wires] at ho
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ hq ho, hw, e1, e2, e3, List.prefix_rfl⟩
  · intro rule mid_i Hin Hrule
    rw [stNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
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

theorem refines_initial : Module.refines_initial stNetlist stSpec ψ := by
  intro i hi
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6⟩, ⟨x6,y6,z6⟩, ud, cr, ⟨x5,y5,z5⟩, ck, ⟨x3,y3,z3⟩, ⟨x4,y4,z4⟩, ⟨x0,y0,z0⟩, ⟨x1,y1,z1⟩, ⟨x2,y2,z2⟩⟩ := i
  dsimp only [stNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  repeat' (obtain ⟨rfl, hi⟩ := hi)
  refine ⟨([], [], [], []), rfl, ?_, rfl, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The seven flip-flops refine the state register.** -/
theorem reg_refines : stNetlist ⊑ stSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.WriteState
