/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import Graphiti.Simp
import Graphiti.AssocList.Lemmas
import Graphiti.Module
import Graphiti.ExprLow
import Graphiti.Component
import Graphiti.Reduce
import Graphiti.List
import Graphiti.ExprHighLemmas
import Graphiti.Tactic

namespace Graphiti.BagQueue

open NatModule

variable {T₁ : Type}

instance : MatchInterface (queue T₁) (bag T₁) where
  input_types := by intro ident; rfl
  output_types := by
    intro ident; dsimp [drcomponents]
    by_cases H: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [H, drunfold, drnat]
  inputs_present := by intros; rfl
  outputs_present := by
    intros ident; dsimp [drcomponents]
    by_cases H: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [H, drnat]

def φ (I S : List T₁) : Prop := I = S

theorem φ_initial : Module.refines_initial (queue T₁) (bag T₁) φ := by
  intros i _; exists i

theorem queue_refine_ϕ_bag: queue T₁ ⊑_{φ} bag T₁ := by
  intros i s H
  constructor
  <;> intros ident mid_i v Hrule
  · case_transition Hcontains : Module.inputs (queue T₁), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp [queue] at Hrule Hcontains;
    subst ident
    exists mid_i, mid_i;
    subst mid_i; unfold bag
    and_intros
    · rw [PortMap.rw_rule_execution]; subst i; simpa [queue]
    · constructor
    · rfl
  · case_transition Hcontains : Module.outputs (queue T₁), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp [queue] at Hrule Hcontains;
    subst ident
    exists s, mid_i
    and_intros
    · constructor
    · dsimp [drcomponents]
      rw [PortMap.rw_rule_execution (h := by apply PortMap.getIO_cons)]
      subst i s; exists ⟨0, by simpa⟩
    · rfl
  · exists mid_i

theorem ϕ_indistinguishable:
  ∀ x y, φ x y → Module.indistinguishable (queue T₁) (bag T₁) x y := by
    intros x y Hϕ
    constructor
    <;> intros ident new_i v H
    <;> exists new_i
    <;> dsimp [drcomponents] at *
    · by_cases Hident: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
      · rw [PortMap.rw_rule_execution] at H
        subst ident
        rw [PortMap.rw_rule_execution]
        rw [Hϕ] at H
        exact H
      · exfalso
        apply (PortMap.getIO_cons_nil_false _ _ ident _ _ _ Hident H)
    · by_cases Hident: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
      · rw [PortMap.rw_rule_execution] at H
        subst ident
        rw [PortMap.rw_rule_execution (h := by apply PortMap.getIO_cons)]
        rw [Hϕ] at H
        rw [←H]
        exists ⟨0, by simpa⟩
      · exfalso
        exact (PortMap.getIO_cons_nil_false _ _ ident _ _ _ Hident H)

theorem queue_refine_bag: queue T₁ ⊑ bag T₁ := by
  apply (Module.refines_φ_refines ϕ_indistinguishable φ_initial queue_refine_ϕ_bag)

end Graphiti.BagQueue
