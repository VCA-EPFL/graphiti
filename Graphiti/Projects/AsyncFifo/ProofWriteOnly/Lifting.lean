/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Refinement
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.TimedRefinementR

/-!
# Substitution in a graph

`ExprLow.refines_env`: a graph read in two environments refines itself whenever every node's
implementation in the first refines its implementation in the second.  This is the one lemma
that turns the per-component theorems into a theorem about the circuit of gates
(`ProofWriteOnly/WriteDomainGates.lean`, `ReadDomainGates.lean`, `FifoGates.lean`,
`StorageGates.lean`).  And `asyncFifoF_expr_refines`: the FIFO's implementation is its reduced
form `asyncFifoF`, which `Refinement.lean` proves against `fifoSpec`.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

open Batteries (AssocList)

/-! ### Refinement of a lowered expression across environments -/

/-- If every base component refines its counterpart in the other environment, so does the whole
expression. -/
theorem ExprLow.refines_env {Ident Typ : Type} [DecidableEq Ident] {ε₁ ε₂ : Env Ident Typ} :
    ∀ (e : ExprLow Ident Typ), ExprLow.wf ε₁ e → ExprLow.wf ε₂ e →
      (∀ (i : PortMapping Ident) (t : Typ), [e| .base i t, ε₁ ] ⊑ [e| .base i t, ε₂ ]) →
      [e| e, ε₁ ] ⊑ [e| e, ε₂ ]
  | .base i t, _, _, hb => hb i t
  | .product a b, hwf₁, hwf₂, hb =>
    have ⟨h1, h2⟩ := ExprLow.wf_product.mp hwf₁
    have ⟨h3, h4⟩ := ExprLow.wf_product.mp hwf₂
    ExprLow.refines_product h1 h2 h3 h4 (ExprLow.refines_env a h1 h3 hb) (ExprLow.refines_env b h2 h4 hb)
  | .connect c e, hwf₁, hwf₂, hb =>
    ExprLow.refines_connect (ExprLow.wf_connect.mp hwf₁) (ExprLow.wf_connect.mp hwf₂)
      (ExprLow.refines_env e (ExprLow.wf_connect.mp hwf₁) (ExprLow.wf_connect.mp hwf₂) hb)

/-- Two environments agreeing on a type give equal base modules. -/
theorem ExprLow.refines_base_of_eq {Ident Typ : Type} [DecidableEq Ident] {ε₁ ε₂ : Env Ident Typ}
    (i : PortMapping Ident) (t : Typ) (h : ε₁ t = ε₂ t) : [e| .base i t, ε₁ ] ⊑ [e| .base i t, ε₂ ] := by
  apply Module.refines_eq'
  simp only [ExprLow.build_module, ExprLow.build_module', h]

/-- A base component whose implementations refine each other. -/
theorem ExprLow.refines_base_of_refines {Ident Typ : Type} [DecidableEq Ident] {ε₁ ε₂ : Env Ident Typ}
    (i : PortMapping Ident) (t : Typ) {T₁ T₂ : Type} {m₁ : Module Ident T₁} {m₂ : Module Ident T₂}
    (h₁ : ε₁ t = some ⟨T₁, m₁⟩) (h₂ : ε₂ t = some ⟨T₂, m₂⟩) (h : m₁ ⊑ m₂) :
    [e| .base i t, ε₁ ] ⊑ [e| .base i t, ε₂ ] := by
  have e₁ : ExprLow.build_module ε₁ (.base i t) = ⟨T₁, m₁.renamePorts i⟩ := by
    unfold ExprLow.build_module ExprLow.build_module'; rw [h₁]; rfl
  have e₂ : ExprLow.build_module ε₂ (.base i t) = ⟨T₂, m₂.renamePorts i⟩ := by
    unfold ExprLow.build_module ExprLow.build_module'; rw [h₂]; rfl
  show (ExprLow.build_module ε₁ (.base i t)).2 ⊑ (ExprLow.build_module ε₂ (.base i t)).2
  rw [e₁, e₂]
  exact Module.refines_renamePorts h

section Circuit

variable (α : Type) [Inhabited α] (n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat)

/-! ### The reduced filtered circuit is the expression-level one -/

seal envF in
theorem asyncFifoF_sigma :
    (⟨asyncFifoFT α n, asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r⟩ : Σ T, StringModule T) =
      ExprLow.build_module (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? asyncFifoLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

theorem asyncFifoF_expr_refines :
    [e| asyncFifoLowered, (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? ] ⊑ asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_eq' (asyncFifoF_sigma α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).symm

end Circuit

theorem wf_envF {α : Type} [Inhabited α] {n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat} :
    ExprLow.wf (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? asyncFifoLowered := by
  rfl

end Graphiti.AsyncFifo
