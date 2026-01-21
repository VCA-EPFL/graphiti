/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean
public import Batteries.Data.UnionFind
public import Graphiti.Core.Graph.Environment
public import Graphiti.Core.Graph.ExprLow

@[expose] public section

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
variable {Typ : Type t}
variable [DecidableEq Ident]
-- variable [DecidableEq Typ]

variable (ε : Env Ident Typ)

def build_module_interface : ExprLow Ident Typ → Option (ModuleInterface Ident)
| .base i e =>
  (ε e).map (λ mod => (mod.2.renamePorts i).toModuleInterface)
| .connect c e =>
  e.build_module_interface >>= λ mi =>
  pure ⟨mi.inputs.eraseAll c.input, mi.outputs.eraseAll c.output⟩
| product e₁ e₂ =>
  e₁.build_module_interface >>= λ m₁ =>
  e₂.build_module_interface >>= λ m₂ =>
  pure ⟨m₁.inputs ++ m₂.inputs, m₁.outputs ++ m₂.outputs⟩

def build_module_interface' : ExprLow Ident Typ → Option (ModuleInterface Ident)
| .base i e =>
  (ε e).map (λ mod => (mod.2.renamePorts i).toModuleInterface)
| .connect c e =>
  e.build_module_interface'
| product e₁ e₂ =>
  e₁.build_module_interface' >>= λ m₁ =>
  e₂.build_module_interface' >>= λ m₂ =>
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

def well_typed'' (m : ModuleInterface Ident) : ExprLow Ident Typ → Prop
| .base i e => True
| .connect c e =>
  e.well_typed'' m
  ∧ ∃ T,
      m.inputs.find? c.input = .some T
      ∧ m.outputs.find? c.output = .some T
| product e₁ e₂ => e₁.well_typed'' m ∧ e₂.well_typed'' m

def well_typed' e :=
  ∃ mi, e.build_module_interface' ε = some mi ∧ well_typed'' mi e

def valsList : ExprLow Ident Typ → List (InternalPort Ident) × List (InternalPort Ident)
| base inst typ => (inst.input.valsList, inst.output.valsList)
| product e1 e2 => let e1' := e1.valsList; let e2' := e2.valsList; (e1'.1 ++ e2'.1, e1'.2 ++ e2'.2)
| connect c e => e.valsList

def unique_valsList (e : ExprLow Ident Typ) := e.valsList.1.Nodup ∧ e.valsList.2.Nodup

variable {ε}

theorem build_module_interface_product {e1 e2 : ExprLow Ident Typ} {m} :
  (e1.product e2).build_module_interface ε = some m →
  ∃ m1 m2, e1.build_module_interface ε = some m1 ∧ e2.build_module_interface ε = some m2
           ∧ m.inputs = m1.inputs ++ m2.inputs ∧ m.outputs = m1.outputs ++ m2.outputs := by
  dsimp [build_module_interface]; grind [Option.bind_eq_some_iff]

theorem build_module_interface_connect {e : ExprLow Ident Typ} {c} {m} :
  (e.connect c).build_module_interface ε = some m →
  ∃ m', e.build_module_interface ε = some m'
        ∧ m.inputs = m'.inputs.eraseAll c.input ∧ m.outputs = m'.outputs.eraseAll c.output := by
  dsimp [build_module_interface]; grind [Option.bind_eq_some_iff]

theorem build_module_interface'_product {e1 e2 : ExprLow Ident Typ} {m} :
  (e1.product e2).build_module_interface' ε = some m →
  ∃ m1 m2, e1.build_module_interface' ε = some m1 ∧ e2.build_module_interface' ε = some m2
           ∧ m.inputs = m1.inputs ++ m2.inputs ∧ m.outputs = m1.outputs ++ m2.outputs := by
  dsimp [build_module_interface']; grind [Option.bind_eq_some_iff]

theorem build_module_interface'_connect {e : ExprLow Ident Typ} {c} {m} :
  (e.connect c).build_module_interface' ε = some m →
  e.build_module_interface' ε = some m := by
  dsimp [build_module_interface']; grind [Option.bind_eq_some_iff]

theorem well_typed_prod_symm {e1 e2 : ExprLow Ident Typ} :
  (e1.product e2).well_typed ε →
  (e2.product e1).well_typed ε := by
  intro ⟨wt1, wt2⟩; constructor <;> assumption

theorem build_module_interface_build_module_interface'' {e : ExprLow Ident Typ} {mi} :
  e.build_module_interface ε = some mi →
  ∃ mi', e.build_module_interface' ε = some mi' := by
  induction e generalizing mi with
  | base inst typ => dsimp [build_module_interface, build_module_interface']; grind
  | connect c e ih =>
    intro hbuild
    dsimp [build_module_interface, build_module_interface'] at *
    rw [] at hbuild
    obtain ⟨mi'', h1, h2⟩ := Option.bind_eq_some_iff.mp hbuild
    cases h2
    rw [h1] at hbuild; dsimp at hbuild; cases hbuild
    solve_by_elim
  | product e1 e2 he1 he2 =>
    intro h1
    have h1_2 := build_module_interface_product h1
    obtain ⟨m1, m2, h1', h2', h3', h4'⟩ := h1_2
    dsimp [build_module_interface', build_module_interface] at *
    rw [h1'] at h1
    rw [h2'] at h1; dsimp at h1; cases h1; cases h3'; cases h4'
    grind

end BuildModule

end ExprLow

namespace ExprHigh

section WellTyped

variable {Ident Typ}
variable [DecidableEq Ident]
variable [DecidableEq Typ]

variable (ε : Env Ident Typ)

def well_typed (h : ExprHigh Ident Typ) : Prop :=
  ∃ hl, h.lower = some hl ∧ hl.well_typed ε

end WellTyped

end ExprHigh

end Graphiti
