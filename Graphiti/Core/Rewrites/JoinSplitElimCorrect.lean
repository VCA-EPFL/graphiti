/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import Graphiti.Core.Simp
import Graphiti.Core.Module
import Graphiti.Core.ModuleReduction
import Graphiti.Core.ExprLow
import Graphiti.Core.Component
import Graphiti.Core.KernelRefl
import Graphiti.Core.Reduce
import Graphiti.Core.List
import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Tactic
import Graphiti.Core.Rewrites.JoinSplitElim
import Mathlib.Tactic

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace Graphiti.JoinSplitElim

open StringModule

@[drunfold_defs]
def lhsNames := ((rewrite.rewrite ["Nat", "Nat"]).get rfl).input_expr.build_module_names
@[drunfold_defs]
def rhsNames := ((rewrite.rewrite ["Nat", "Nat"]).get rfl).output_expr.build_module_names

@[drunfold_defs]
def rewriteLhsRhs := rewrite.rewrite ["Nat", "Nat"] |>.get rfl

def ε : IdentMap String (TModule1 String) :=
  [ ("join Nat Nat", ⟨_, join Nat Nat⟩)
  , ("split Nat Nat", ⟨_, split Nat Nat⟩)
  , ("pure (Nat×Nat) (Nat×Nat)", ⟨_, @pure (Nat×Nat) (Nat×Nat) id⟩)].toAssocList

@[drenv] theorem find?_join1_data : (Batteries.AssocList.find? "join Nat Nat" ε) = .some ⟨_, join Nat Nat⟩ := by simp [ε]
@[drenv] theorem find?_split1_data : (Batteries.AssocList.find? "split Nat Nat" ε) = .some ⟨_, split Nat Nat⟩ := by simp [ε]
@[drenv] theorem find?_pure1_data : (Batteries.AssocList.find? "pure (Nat×Nat) (Nat×Nat)" ε) = .some ⟨_, @StringModule.pure (Nat×Nat) (Nat×Nat) id⟩ := by simp [ε]

seal ε in
def_module lhsModuleType : Type :=
  [T| rewriteLhsRhs.input_expr, ε.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_join1_data, find?_split1_data]
  dsimp
--   skip
  -- dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  -- dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  -- dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  -- simp only [find?_pure_data2, find?_join2_data2, find?_join2_data, find?_join1_data, find?_join1_data2]
  -- dsimp

def cast_module_type {α} {f : α → Type _} {s s' : Σ T, f T} (heq : s = s') : f s.1 = f s'.1 := by simp_all

seal ε in
def_module lhsModule : StringModule lhsModuleType :=
  [e| rewriteLhsRhs.input_expr, ε.find? ]

seal ε in
def_module rhsModuleType : Type :=
  [T| rewriteLhsRhs.output_expr, ε.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_pure1_data]
  dsimp

seal ε in
def_module rhsModule : StringModule rhsModuleType :=
  [e| rewriteLhsRhs.output_expr, ε.find? ]
reduction_by
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?, drcomponents]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp [reduceAssocListfind?])

instance : MatchInterface (rhsModule) (lhsModule) := by
  dsimp [rhsModule, lhsModule]
  solve_match_interface

@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

theorem sigma_rw_simp {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by simp [drunfold,drcompute,seval]; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

inductive φ : rhsModuleType → lhsModuleType → Prop where
| inputs ident r l r' l' v :
  φ r' l' →
  ((rhsModule).inputs.getIO ident).snd r v r' →
  ((lhsModule).inputs.getIO ident).snd l ((MatchInterface.input_types ident).mp v) l' →
  φ r l
| outputs ident r l r' l' v :
  φ r' l' →
  ((rhsModule).outputs.getIO ident).snd r v r' →
  ((lhsModule).outputs.getIO ident).snd l ((MatchInterface.output_types ident).mp v) l' →
  φ r l
| internal r l r' rule :
  φ r' l →
  rule ∈ (rhsModule).internals →
  rule r r' →
  φ r l

theorem refines {T: Type _} [DecidableEq T]: rhsModule ⊑_{φ} lhsModule := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  -- induction Hφ with
  -- | inputs ident r l r' l' v hφ ir il ih =>
  --   skip
  sorry

end Graphiti.JoinSplitElim
