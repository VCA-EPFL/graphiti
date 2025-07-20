/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Mathlib.Tactic

namespace Graphiti

  variable {Ident S : Type _}
  variable [DecidableEq Ident]

class DeterministicInputs (mod: Module Ident S) where
  input_deterministic: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂
    → (mod.inputs.getIO ident).snd s₁ v s₃
    → s₂ = s₃

class DeterministicInternals (mod: Module Ident S) where
  internal_deterministic: ∀ rule ∈ mod.internals , ∀ s₁ s₂ s₃,
    rule s₁ s₂ → rule s₁ s₃ → s₂ = s₃

class DeterministicOutputs (mod: Module Ident S) where
  output_deterministic: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂
    → (mod.outputs.getIO ident).snd s₁ v s₃
    → s₂ = s₃

-- TODO: Make it an abbrev? (https://lean-lang.org/doc/reference/latest//Type-Classes/Class-Declarations/#class-abbrev)
class Deterministic (mod: Module Ident S) extends
  DeterministicInputs mod,
  DeterministicInternals mod,
  DeterministicOutputs mod

variable {mod: Module Ident S} in
instance [d₁: DeterministicInputs mod] [d₂: DeterministicInternals mod] [d₃: DeterministicOutputs mod]: Deterministic mod := {
  input_deterministic    := d₁.input_deterministic
  internal_deterministic := d₂.internal_deterministic
  output_deterministic   := d₃.output_deterministic
}

end Graphiti
