/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Graph.Module

namespace Graphiti

variable {Ident S : Type _}

variable (mod: Module Ident S)
variable [DecidableEq Ident]

-- TODO: Define RuleMayStronglySwap, etc. (bring it closer to Confluence definitions for merging)
class RuleMaySwap: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂
    → existSR mod.internals s₁ s₃
    → ∃ s₄, (mod.inputs.getIO ident).snd s₃ v s₄ ∧ existSR mod.internals s₂ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂
    → existSR mod.internals s₁ s₃
    → ∃ s₄, (mod.outputs.getIO ident).snd s₃ v s₄ ∧ existSR mod.internals s₂ s₄

end Graphiti
