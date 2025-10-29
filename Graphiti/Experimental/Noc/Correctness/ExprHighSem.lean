/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Graphiti.Core.ModuleReduction
import Graphiti.Core.ExprHigh
import Graphiti.Core.ExprLowLemmas
import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Component

open Batteries (AssocList)

-- This file define an alternative build_module function to give a module
-- semantics to ExprHigh without a lowering to ExprLow.

namespace Graphiti.ExprHigh

  variable {Ident Typ}
  variable [DecidableEq Ident]
  variable (ε : Env Ident Typ)

  section Definitions

    @[drunfold_defs]
    abbrev build_module_high_type' (ms : List (PortMapping Ident × TModule Ident)) : Type _ :=
      HVector (·.2.1) ms

    @[drunfold_defs]
    def lift_module (ms : List (PortMapping Ident × TModule Ident)) (i : Nat) (hi : i < ms.length) : Module Ident (build_module_high_type' ms) :=
      let idx : Fin ms.length := ⟨i, hi⟩
      let m := ms[i].2.2
      let pm := ms[i].1
      {
        inputs := m.inputs.map (λ k f => (pm.input.bijectivePortRenaming k, ⟨f.1, λ s v s' => f.2 (s.get idx) v (s'.get idx)⟩))
        outputs := m.outputs.map (λ k f => (pm.output.bijectivePortRenaming k, ⟨f.1, λ s v s' => f.2 (s.get idx) v (s'.get idx)⟩))
        internals := m.internals.map (λ f => λ s s' => f (s.get idx) (s'.get idx))
        init_state := λ s => m.init_state (s.get idx)
      }

    @[drunfold_defs]
    def merge_modules {S} (ms : List (Module Ident S)) : Module Ident S :=
      {
        inputs := ms.map (·.inputs) |> AssocList.flatten
        outputs := ms.map (·.outputs) |> AssocList.flatten
        internals := ms.map (·.internals) |>.flatten
        init_state := ms.map (·.init_state) |>.foldl (λ acc p => λ s => p s ∧ acc s) (λ s => True)
      }

    @[drunfold_defs]
    def apply_connections {S} (cs : List (Connection Ident)) (m : Module Ident S) : Module Ident S :=
      cs.foldl (λ m c => m.connect' c.output c.input) m

    @[drunfold_defs]
    def build_module_high'' (ms : List (PortMapping Ident × TModule Ident)) (e : ExprHigh Ident Typ) : Module Ident (build_module_high_type' ms) :=
      ms.mapFinIdx (λ i _ hi => lift_module ms i hi)
      |> merge_modules
      |> apply_connections e.connections

    @[drunfold_defs]
    def collapse {α} (l : List (Option α)) : Option (List α) :=
      l.mapM (λ i => i.bind (λ i' => i'))

    @[drunfold_defs]
    def build_module_high' (e : ExprHigh Ident Typ) : Option (TModule Ident) :=
      match (e.modules.valsList.map (λ (i, t) => do let m ← ε t; (i, m))) |> collapse with
      | .some ms  => .some ⟨build_module_high_type' ms, build_module_high'' ms e⟩
      | .none     => .none

    @[drunfold_defs]
    def build_module_high (e : ExprHigh Ident Typ) : TModule Ident :=
      build_module_high' ε e |>.getD ⟨ PUnit, Module.empty _ ⟩

    @[drunfold_defs]
    def build_module_high_type (e : ExprHigh Ident Typ) : Type _ :=
      build_module_high ε e |>.fst

    @[drunfold_defs]
    def build_module_high_expr (e : ExprHigh Ident Typ) : Module Ident (build_module_high_type ε e) :=
      build_module_high ε e |>.snd

  end Definitions

  section Proofs

    -- TODO: This is not exactly correct since the state of a ExprHigh with one
    -- module would be a HVector of size 1
    -- TODO: Prove with build_moduleD
    -- theorem build_base_in_env {T inst i mod} :
    --   ε i = some ⟨ T, mod ⟩ →
    --   build_module_high ε { modules =  inst i) = some ⟨ T, mod.renamePorts inst ⟩ := by
    --     sorry

    -- TODO: What is needed here?
    -- Should we prove that this semantics is equal to the lowering semantics ?
    -- If yes, should we do this by refinement? This would be a bit sad since
    -- our refinement relation is somewhat weak, and these semantics should be
    -- much more matching

  end Proofs

end Graphiti.ExprHigh
