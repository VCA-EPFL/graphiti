/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas

import Graphiti.Projects.Flushability.SimulationRelation

namespace Graphiti

variable {Ident S₁ S₂ : Type _}
variable [DecidableEq Ident]
variable (mod₁ : Module Ident S₁) (mod₂ : Module Ident S₂)
variable [mm: MatchInterface mod₁ mod₂]

section Outputability

variable {Ident S: Type _}
variable [DecidableEq Ident]

inductive direct_outputable: (Module Ident S) → S → InternalPort Ident → Prop where
| mk: ∀ mod ident s, (∃ v s', (mod.outputs.getIO ident).snd s v s') → direct_outputable mod s ident

inductive indirect_outputable: (Module Ident S) → S → InternalPort Ident → Prop where
| mk: ∀ mod ident s, (∃ v s₁ s₂, existSR (mod.internals) s s₁ ∧ (mod.outputs.getIO ident).snd s₁ v s₂) → indirect_outputable mod s ident

-- TODO: Add wrt to port?
inductive outputable: (Module Ident S) → S → InternalPort Ident → Prop where
| direct:   ∀ mod ident s, direct_outputable mod s ident   → outputable mod s ident
| indirect: ∀ mod ident s, indirect_outputable mod s ident → outputable mod s ident

-- TODO: If this theorem holds, we reduce the reasoning to only prove that the
--       state if `outputable` (in practice, we should only prove `indirect_outputable`)
--       The question remains how hard it is to define the pattern of
--       `indirect_outputable` states
-- TODO: In out running example, a non-direct, indirect outputable state has a single pattern
--       Can we derive that a state in rhs follows that pattern easily?
--theorem n:
--  ∀ (mod: Module Ident S) ident s, outputable mod ident s ∧ /- pf mod s -/ → direct_outputable mod ident s :=
--by
--  sorry

-- If a state is flushable and outputable, then it is direct_outputable

--variable (mod: Module Ident S) in
--example: direct_outputable mod sorry sorry := by
--  sorry

end Outputability

section Indistinguishability

variable (ψ : S₁ → S₂ → Prop)

class Indistinguishable :=
  inputs: ∀ ident i₁ s₁ i₂ v,
    ψ i₁ s₁ →
    (mod₁.inputs.getIO ident).snd i₁ v i₂ →
    ∃ s₂, (mod₂.inputs.getIO ident).snd s₁ ((mm.input_types ident).mp v) s₂
  outputs: ∀ ident i₁ s₁ i₂ v,
    ψ i₁ s₁ →
    (mod₁.outputs.getIO ident).snd i₁ v i₂ →
    ∃ s₂, (mod₂.outputs.getIO ident).snd s₁ ((mm.output_types ident).mp v) s₂

end Indistinguishability

section Composition

variable (ψ₁: S₁ → S₂ → Prop) (ψ₂: S₁ → S₂ → Prop)

instance [ind: Indistinguishable mod₁ mod₂ ψ₁]: Indistinguishable mod₁ mod₂ (ψ₁ ∧ ψ₂) := {
  inputs := by
    intro _ _ _ _ _ ⟨_, _⟩ _
    apply ind.inputs <;> assumption
  outputs := by
    intro _ _ _ _ _ ⟨_, _⟩ _
    apply ind.outputs<;> assumption
}

instance [ind: Indistinguishable mod₁ mod₂ ψ₂]: Indistinguishable mod₁ mod₂ (ψ₁ ∧ ψ₂) := {
  inputs := by
    intro _ _ _ _ _ ⟨_, _⟩ _
    apply ind.inputs <;> assumption
  outputs := by
    intro _ _ _ _ _ ⟨_, _⟩ _
    apply ind.outputs<;> assumption
}

instance [ind₁: Indistinguishable mod₁ mod₂ ψ₁] [ind₂: Indistinguishable mod₁ mod₂ ψ₂]: Indistinguishable mod₁ mod₂ (ψ₁ ∨ ψ₂) := {
  inputs := by
    intro _ _ _ _ _ h _
    cases h
    . apply ind₁.inputs <;> assumption
    . apply ind₂.inputs <;> assumption
  outputs := by
    intro _ _ _ _ _ h _
    cases h
    . apply ind₁.outputs <;> assumption
    . apply ind₂.outputs <;> assumption
}

end Composition

end Graphiti
