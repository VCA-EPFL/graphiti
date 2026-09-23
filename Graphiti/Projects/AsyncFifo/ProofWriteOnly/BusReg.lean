/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Dff
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusRegLemmas

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.BusReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Dff

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Stated over an index rather than as a record with
one field per wire, the per-rule lemmas collapse into `Netlist.Wf_set` and `Netlist.Wf_drv`, so
what is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The twelve driven wires. -/
inductive W | pk0 | pk1 | pk2
            | f0clk | f0d | f0crn | f1clk | f1d | f1crn | f2clk | f2d | f2crn
  deriving DecidableEq

/-- What drives each wire: one line per wire, and the only place the shape of this netlist is
written down. -/
def drv (clk crn : List Bool) (d : List (BitVec 3)) : Drv W
  | w, .pk0 => dffOut (w .f0clk) (w .f0d) (w .f0crn)
  | w, .pk1 => dffOut (w .f1clk) (w .f1d) (w .f1crn)
  | w, .pk2 => dffOut (w .f2clk) (w .f2d) (w .f2crn)
  | _, .f0clk | _, .f1clk | _, .f2clk => clk
  | _, .f0crn | _, .f1crn | _, .f2crn => crn
  | _, .f0d => bitsOf 0 d
  | _, .f1d => bitsOf 1 d
  | _, .f2d => bitsOf 2 d

theorem drv_mono {clk crn d} : Mono (drv clk crn d) := by
  intro a b h k
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, h, dffOut_mono]
theorem drv_env {clk clk' crn crn' : List Bool} {d d' : List (BitVec 3)}
    (hc : clk <+: clk') (hr : crn <+: crn') (hd : d <+: d') (w : Wires W) (k : W) :
    drv clk crn d w k <+: drv clk' crn' d' w k := by
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, hc, hd, hr, bitsOf_mono]
def wires (i : busT) : Wires W
  | .pk0 => i.1.1 | .pk1 => i.1.2.1 | .pk2 => i.1.2.2
  | .f0clk => i.2.2.2.2.1.1 | .f0d => i.2.2.2.2.1.2.1 | .f0crn => i.2.2.2.2.1.2.2
  | .f1clk => i.2.2.2.2.2.1.1 | .f1d => i.2.2.2.2.2.1.2.1 | .f1crn => i.2.2.2.2.2.1.2.2
  | .f2clk => i.2.2.2.2.2.2.1 | .f2d => i.2.2.2.2.2.2.2.1 | .f2crn => i.2.2.2.2.2.2.2.2

def ψ (i : busT) (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) : Prop :=
  Wf (drv s.1 s.2.2.1 s.2.1) (wires i) ∧ i.2.2.2.1 = s.1 ∧ i.2.1 = s.2.1 ∧ i.2.2.1 = s.2.2.1
    ∧ s.2.2.2 <+: pack3Out (wires i .pk0) (wires i .pk1) (wires i .pk2)

/-- What the block reports is a prefix of what the specification says. -/
theorem out_q {clk crn d} {w : Wires W} (hw : Wf (drv clk crn d) w) :
    pack3Out (w .pk0) (w .pk1) (w .pk2) <+: busOut clk d crn := by
  refine pack3Out_mono ?_ ?_ ?_
  · exact (hw .pk0).trans (dffOut_mono (hw .f0clk) (hw .f0d) (hw .f0crn))
  · exact (hw .pk1).trans (dffOut_mono (hw .f1clk) (hw .f1d) (hw .f1crn))
  · exact (hw .pk2).trans (dffOut_mono (hw .f2clk) (hw .f2d) (hw .f2crn))

/-! ### One tactic for every connection -/

syntax "bus_case " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| bus_case $w:term) => `(tactic| (
      obtain ⟨⟨pk0, pk1, pk2⟩, ud, cr, ck, ⟨a0,a1,a2⟩, ⟨b0,b1,b2⟩, ⟨c0,c1,c2⟩⟩ := i
      obtain ⟨⟨_,_,_⟩, _, _, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_,_,_⟩,_,_,_,⟨_,_,_⟩,⟨_,_,_⟩,⟨_,_,_⟩⟩, out, Hr⟩ := Hr
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
      · have key := hq.trans (pack3Out_mono (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _) (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _))
        revert key; simp [wires, upd]))

theorem busNetlist_internals_eq : busNetlist.internals =
    [busNetlist.internals.getD 0 (fun _ _ => False), busNetlist.internals.getD 1 (fun _ _ => False), busNetlist.internals.getD 2 (fun _ _ => False),
     busNetlist.internals.getD 3 (fun _ _ => False), busNetlist.internals.getD 4 (fun _ _ => False), busNetlist.internals.getD 5 (fun _ _ => False),
     busNetlist.internals.getD 6 (fun _ _ => False), busNetlist.internals.getD 7 (fun _ _ => False), busNetlist.internals.getD 8 (fun _ _ => False),
     busNetlist.internals.getD 9 (fun _ _ => False), busNetlist.internals.getD 10 (fun _ _ => False), busNetlist.internals.getD 11 (fun _ _ => False)] := rfl

/-! All twelve connections, one line each. -/

theorem case_0 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f0clk

theorem case_1 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f1clk

theorem case_2 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f2clk

theorem case_3 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f0crn

theorem case_4 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f1crn

theorem case_5 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f2crn

theorem case_6 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f0d

theorem case_7 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f1d

theorem case_8 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.f2d

theorem case_9 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.pk0

theorem case_10 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.pk1

theorem case_11 (s) (i mid : busT) (H : ψ i s)
    (Hrule : (busNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by bus_case W.pk2

/-! ### The specification's own rules -/

section SpecRules
variable (sp : List Bool × List (BitVec 3) × List Bool × List (BitVec 3))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (busSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (BitVec 3)) (h : sp.2.1 ⊏ v) :
    (busSpec.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (busSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List (BitVec 3)) (h1 : sp.2.2.2 <+: v)
    (h2 : v <+: busOut sp.1 sp.2.1 sp.2.2.1) :
    (busSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : busNetlist ⊑_{ψ} busSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨pk0, pk1, pk2⟩, ud, cr, ck, ⟨a0,a1,a2⟩, ⟨b0,b1,b2⟩, ⟨c0,c1,c2⟩⟩ := i
    obtain ⟨⟨_,_,_⟩, _, _, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, hq⟩ := H
    case_transition Hcontains : Module.inputs busNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [busNetlist] at Hcontains
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
    obtain ⟨⟨pk0, pk1, pk2⟩, ud, cr, ck, ⟨a0,a1,a2⟩, ⟨b0,b1,b2⟩, ⟨c0,c1,c2⟩⟩ := i
    obtain ⟨⟨_,_,_⟩, _, _, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, hq⟩ := H
    case_transition Hcontains : Module.outputs busNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [busNetlist] at Hcontains
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
    rw [busNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h|h|h|h|h
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

theorem refines_initial : Module.refines_initial busNetlist busSpec ψ := by
  intro i hi
  obtain ⟨⟨pk0, pk1, pk2⟩, ud, cr, ck, ⟨a0,a1,a2⟩, ⟨b0,b1,b2⟩, ⟨c0,c1,c2⟩⟩ := i
  dsimp only [busNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨([], [], [], []), rfl, ?_, rfl, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The three flip-flops refine the three-bit register.** -/
theorem reg_refines : busNetlist ⊑ busSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.BusReg
