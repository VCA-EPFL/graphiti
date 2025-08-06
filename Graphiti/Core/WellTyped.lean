/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Graphiti.Core.ExprLow
import Graphiti.Core.Environment

namespace Graphiti

structure ModuleInterface (Ident) where
  inputs : PortMap Ident Type
  outputs : PortMap Ident Type

def Module.toModuleInterface {S Ident} (m : Module Ident S) : ModuleInterface Ident :=
  ⟨m.inputs.mapVal (λ k v => v.1), m.outputs.mapVal (λ k v => v.1)⟩

namespace ExprLow

section BuildModule

universe i t
variable {Ident : Type i}
variable {Typ : Type i}
variable [DecidableEq Ident]
variable [DecidableEq Typ]

variable (ε : Env Ident Typ)

def build_module_interface : ExprLow Ident Typ → Option (ModuleInterface Ident)
| .base i e =>
  match ε e with
  | .some mod => (mod.2.renamePorts i).toModuleInterface
  | .none => none
| .connect c e =>
  e.build_module_interface >>= λ mi =>
  pure ⟨mi.inputs.eraseAll c.input, mi.outputs.eraseAll c.output⟩
| product e₁ e₂ =>
  e₁.build_module_interface >>= λ m₁ =>
  e₂.build_module_interface >>= λ m₂ =>
  pure ⟨m₁.inputs ++ m₂.inputs, m₁.outputs ++ m₂.outputs⟩

def well_typed : ExprLow Ident Typ → Prop
| .base i e => True
| .connect c e =>
  e.well_typed
  ∧ ∃ mi T,
      e.build_module_interface ε = .some mi
      ∧ mi.inputs.find? c.input = .some T
      ∧ mi.outputs.find? c.output = .some T
| product e₁ e₂ => e₁.well_typed ∧ e₂.well_typed

end BuildModule

end ExprLow

namespace ExprHigh

section WellTyped

variable {Ident Typ}
variable [DecidableEq Ident]
variable [DecidableEq Typ]

variable (ε : Env Ident Typ)

def well_typed (h : ExprHigh Ident Typ) : Prop :=
  ∃ hl, h.lower_TR = some hl ∧ hl.well_typed ε

end WellTyped

end ExprHigh

end Graphiti
