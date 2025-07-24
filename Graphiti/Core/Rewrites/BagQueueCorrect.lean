/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import Graphiti.Core.Simp
import Graphiti.Core.AssocList.Lemmas
import Graphiti.Core.Module
import Graphiti.Core.ExprLow
import Graphiti.Core.Component
import Graphiti.Core.Reduce
import Graphiti.Core.List
import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Tactic
import Graphiti.Core.ModuleReduction

namespace Graphiti.BagQueue

open NatModule

variable {T₁ : Type}

instance : MatchInterface (queue T₁) (bag T₁) := by
  dsimp [queue, bag]
  solve_match_interface

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

theorem queue_refine_bag: queue T₁ ⊑ bag T₁ := by
  exists inferInstance, φ; solve_by_elim [queue_refine_ϕ_bag, φ_initial]

end Graphiti.BagQueue
