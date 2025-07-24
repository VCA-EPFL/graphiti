/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Mathlib.Tactic

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas

namespace Graphiti

variable {Ident S₁ S₂ : Type _}
variable [DecidableEq Ident]
variable (ψ : S₁ → S₂ → Prop)
variable (mod₁ : Module Ident S₁) (mod₂ : Module Ident S₂)
variable [mm: MatchInterface mod₁ mod₂]

class SimulationRelation :=
  inputs_preserved: ∀ ident i₁ i₂ v s₁ s₂,
    ψ i₁ s₁ →
    (mod₁.inputs.getIO ident).snd i₁ v i₂ →
    (mod₂.inputs.getIO ident).snd s₁ ((mm.input_types ident).mp v) s₂ →
    ψ i₂ s₂
  internals_preserved: ∀ i i' s s',
    ψ i s →
    existSR mod₁.internals i i' →
    existSR mod₂.internals s s' →
    ψ i' s'
  outputs_preserved: ∀ ident i₁ i₂ v s₁ s₂,
    ψ i₁ s₁ →
    (mod₁.outputs.getIO ident).snd i₁ v i₂ →
    (mod₂.outputs.getIO ident).snd s₁ ((mm.output_types ident).mp v) s₂ →
    ψ i₂ s₂
  initial_state_preserves: ∀ i s,
    mod₁.init_state i →
    mod₂.init_state s →
    ψ i s

class WeakSimulationRelation :=
  inputs_preserved: ∀ ident i₁ i₂ v s₁ s₂, ∃ i₃ s₃,
    ψ i₁ s₁ →
    (mod₁.inputs.getIO ident).snd i₁ v i₂ ∧ existSR mod₁.internals i₂ i₃ →
    (mod₂.inputs.getIO ident).snd s₁ ((mm.input_types ident).mp v) s₂ ∧ existSR mod₂.internals s₂ s₃ →
    ψ i₃ s₃
  internals_preserved: ∀ i₁ s₁, ∃ i₂ s₂,
    ψ i₁ s₁ →
    existSR mod₁.internals i₁ i₂ →
    existSR mod₂.internals s₁ s₂ →
    ψ i₂ s₂
  outputs_preserved: ∀ ident i₁ i₂ v s₁ s₂, ∃ i₃ s₃,
    ψ i₁ s₁ →
    (mod₁.outputs.getIO ident).snd i₁ v i₂ ∧ existSR mod₁.internals i₂ i₃ →
    (mod₂.outputs.getIO ident).snd s₁ ((mm.output_types ident).mp v) s₂ ∧ existSR mod₂.internals s₂ s₃ →
    ψ i₃ s₃
  initial_state_preserves: ∀ i s,
    mod₁.init_state i →
    mod₂.init_state s →
    ψ i s

-- TODO: Define a `LeftWeakSimulationRelation` and a `RightWeakSimulationRelation`?
instance [ws: SimulationRelation ψ mod₁ mod₂]: WeakSimulationRelation ψ mod₁ mod₂ := {
  inputs_preserved := by
    intros ident i₁ i₂ v s₁ s₂
    use i₂, s₂
    intro h₁ ⟨h₂, h₃⟩ ⟨h₄, h₅⟩
    apply ws.inputs_preserved ident i₁ i₂ v s₁ s₂ <;> assumption
  internals_preserved := by
    intros i₁ s₁
    use i₁, s₁
    intros
    assumption
  outputs_preserved := by
    intros ident i₁ i₂ v s₁ s₂
    use i₂, s₂
    intro h₁ ⟨h₂, h₃⟩ ⟨h₄, h₅⟩
    apply ws.outputs_preserved ident i₁ i₂ v s₁ s₂ <;> assumption
  initial_state_preserves := ws.initial_state_preserves
}

-- True is a simulation relation (the weakest possible simulation relation, it doesn't give any information)
-- It doesn't help at all when proving inputability or outputability
def TTrue: S₁ → S₂ → Prop := λ _ _ => True
instance: SimulationRelation TTrue mod₁ mod₂ := {
  inputs_preserved := by
    intros <;> trivial
  internals_preserved := by
    intros <;> trivial
  outputs_preserved := by
    intros <;> trivial
  initial_state_preserves := by
    intros <;> trivial
}

section Composability

variable (ψ₁ : S₁ → S₂ → Prop) (ψ₂ : S₁ → S₂ → Prop)

def and := λ s₁ s₂ => ψ₁ s₁ s₂ ∧ ψ₂ s₁ s₂
infixr:35 " ∧ " => and

def or := λ s₁ s₂ => ψ₁ s₁ s₂ ∨ ψ₂ s₁ s₂
infixr:35 " ∨ " => or

-- TODO: Is it an equivalence, can I deduce that ψ₁ is an SR from ψ₁ ∧ ψ₂? (Same for ψ₂)
instance [sr₁: SimulationRelation ψ₁ mod₁ mod₂] [sr₂: SimulationRelation ψ₂ mod₁ mod₂]: SimulationRelation (ψ₁ ∧ ψ₂) mod₁ mod₂ := {
  inputs_preserved := by
    intro _ _ _ _ _ _ ⟨h₁, h₂⟩ _ _
    and_intros
    . apply sr₁.inputs_preserved <;> assumption
    . apply sr₂.inputs_preserved <;> assumption
  internals_preserved := by
    intro _ _ _ _ ⟨h₁, h₂⟩ _ _
    and_intros
    . apply sr₁.internals_preserved <;> assumption
    . apply sr₂.internals_preserved <;> assumption
  outputs_preserved := by
    intro _ _ _ _ _ _ ⟨h₁, h₂⟩ _ _
    and_intros
    . apply sr₁.outputs_preserved <;> assumption
    . apply sr₂.outputs_preserved <;> assumption
  initial_state_preserves := by
    intros
    and_intros
    . apply sr₁.initial_state_preserves <;> assumption
    . apply sr₂.initial_state_preserves <;> assumption
}

-- TODO: Is it an equivalence, can I deduce that ψ₁ is an SR from ψ₁ ∨ ψ₂? (Same for ψ₂)
instance [sr₁: SimulationRelation ψ₁ mod₁ mod₂] [sr₂: SimulationRelation ψ₂ mod₁ mod₂]: SimulationRelation (ψ₁ ∨ ψ₂) mod₁ mod₂ := {
  inputs_preserved := by
    intro _ _ _ _ _ _ h _ _
    cases h
    . left
      apply sr₁.inputs_preserved <;> assumption
    . right
      apply sr₂.inputs_preserved <;> assumption
  internals_preserved := by
    intro _ _ _ _ h _ _
    cases h
    . left
      apply sr₁.internals_preserved <;> assumption
    . right
      apply sr₂.internals_preserved <;> assumption
  outputs_preserved := by
    intro _ _ _ _ _ _ h _ _
    cases h
    . left
      apply sr₁.outputs_preserved <;> assumption
    . right
      apply sr₂.outputs_preserved <;> assumption
  initial_state_preserves := by
    intros
    left
    apply sr₁.initial_state_preserves <;> assumption
}

-- TODO: Can we derive a simulation relation of the product of two modules? I believe that a lifted And should work

end Composability

section Transitivity

-- TODO: Can we build a simulation relation φ₃ from φ₁ and φ₂ for transitivity?

end Transitivity

end Graphiti
