/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

import Graphiti.Core.Module
import Graphiti.Core.Simp
import Graphiti.Core.ExprHigh
import Graphiti.Core.AssocList.Basic
import Graphiti.Core.Component

namespace Graphiti

def Env Ident Typ := Typ → Option (TModule1 Ident)

abbrev FinEnv Ident Typ := Batteries.AssocList Typ (TModule1 Ident)

namespace Env

def subsetOf {Ident Typ} (ε₁ ε₂ : Env Ident Typ) : Prop :=
  ∀ i v, ε₁ i = .some v → ε₂ i = .some v

theorem subsetOf_reflexive {Ident Typ} {ε : Env Ident Typ} :
  subsetOf ε ε := by simp [subsetOf]

def union {Ident Typ} (ε₁ ε₂ : Env Ident Typ) : Env Ident Typ := λ s =>
  match ε₁ s with
  | some x => pure x
  | none => ε₂ s

def independent {Ident Typ} (ε₁ ε₂ : Env Ident Typ) : Prop :=
  ∀ i v, ε₁ i = some v → ε₂ i = none

theorem independent_symm {Ident Typ} {ε₁ ε₂ : Env Ident Typ} :
  independent ε₁ ε₂ → independent ε₂ ε₁ := by
  unfold independent
  intro h i v h1
  cases h:  ε₁ i <;> grind

theorem subset_of_union {Ident Typ} {ε₁ ε₂ : Env Ident Typ} :
  ε₁.subsetOf (ε₁.union ε₂) := by
  intros; simp only [subsetOf, independent, union] at *
  intros; simp only [*]; rfl

theorem independent_subset_of_union {Ident Typ} {ε₁ ε₂ : Env Ident Typ} :
  ε₁.independent ε₂ →
  ε₂.subsetOf (ε₁.union ε₂) := by
  intros; simp [subsetOf, independent, union] at *
  grind

def well_formed {α} (ε : Env String (String × α)) (s : String) : Prop :=
  match s with
  | "branch" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.branch T⟩
  | "cntrl_merge" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.cntrl_merge T⟩
  | "constant" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Sigma id), mod = ⟨_, StringModule.constant T.2⟩
  | "fork" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Nat), mod = ⟨_, StringModule.fork T.1 T.2⟩
  | "fork2" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.fork T 2⟩
  | "init" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Sigma id), mod = ⟨_, StringModule.init T.1 T.2⟩
  | "initBool" => ∀ a mod, ε (s, a) = some mod → mod = ⟨_, StringModule.init Bool false⟩
  | "join" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Type _), mod = ⟨_, StringModule.join T.1 T.2⟩
  | "load" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Type _), mod = ⟨_, StringModule.load T.1 T.2⟩
  | "merge" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Nat), mod = ⟨_, StringModule.merge T.1 T.2⟩
  | "merge2" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.merge T 2⟩
  | "mux" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.mux T⟩
  | "operator1" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × (Sigma (λ x => Inhabited x)) × String), mod = ⟨_, @StringModule.operator1 T.1 T.2.1.1 T.2.1.2 T.2.2⟩
  | "operator2" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Type _ × (Sigma (λ x => Inhabited x)) × String), mod = ⟨_, @StringModule.operator2 T.1 T.2.1 T.2.2.1.1 T.2.2.1.2 T.2.2.2⟩
  | "operator3" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Type _ × Type _ × (Sigma (λ x => Inhabited x)) × String), mod = ⟨_, @StringModule.operator3 T.1 T.2.1 T.2.2.1 T.2.2.2.1.1 T.2.2.2.1.2 T.2.2.2.2⟩
  | "pure" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Sigma (λ ((x, y) : Type _ × Type _) => x -> y)), mod = ⟨_, StringModule.pure T.2⟩
  | "queue" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.queue T⟩
  | "sink" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Nat), mod = ⟨_, StringModule.sink T.1 T.2⟩
  | "split" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Type _), mod = ⟨_, StringModule.split T.1 T.2⟩
  | "tagger_untagger_val" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Sigma (λ x => DecidableEq x) × Type _ × Type _), mod = ⟨_, @StringModule.tagger_untagger_val T.1.1 T.1.2 T.2.1 T.2.2⟩
  | _ => True

end Env

namespace FinEnv

@[simp]
def toEnv {Ident Typ} [DecidableEq Typ] (ε : FinEnv Ident Typ) : Env Ident Typ := ε.find?

theorem exists_fresh {Ident} {ε : FinEnv Ident (String × String)} {a : List String}
  : ∃ (b : List String), a.length = b.length ∧ (∀ a' b', (a', b') ∈ a.zip b → ¬ ε.contains (a', b')) ∧ (a.zip b).Nodup := by sorry

noncomputable def select_fresh' {Ident} (ε : FinEnv Ident (String × String)) (a : List String) : List String :=
  Exists.choose (@exists_fresh Ident ε a)

theorem select_fresh'_spec {Ident} {ε : FinEnv Ident (String × String)} {a : List String} :
  a.length = (select_fresh' ε a).length ∧ (∀ a' b', (a', b') ∈ a.zip (select_fresh' ε a) → ¬ ε.contains (a', b')) ∧ (a.zip (select_fresh' ε a)).Nodup :=
  Exists.choose_spec exists_fresh

noncomputable def select_fresh {Ident} (ε : FinEnv Ident (String × String)) (a : List String) : List (String × String) :=
  a.zip (select_fresh' ε a)

theorem select_fresh_spec {Ident} {ε : FinEnv Ident (String × String)} {a : List String} :
  a.length = (select_fresh ε a).length ∧ (∀ a' b', (a', b') ∈ select_fresh ε a → ¬ ε.contains (a', b')) ∧ (select_fresh ε a).Nodup := by
  grind [select_fresh, select_fresh'_spec]

def max_type {Ident} (f : FinEnv Ident (String × Nat)) : Option Nat :=
  f.keysList.map Prod.snd |>.max?

def max_typeD {Ident} (f : FinEnv Ident (String × Nat)) : Nat :=
  f.max_type |>.getD 0

theorem union_eq {Ident Typ} [DecidableEq Typ] {ε₁ ε₂ : FinEnv Ident Typ} :
  (ε₁ ++ ε₂).toEnv = Env.union ε₁.toEnv ε₂.toEnv := by
  unfold toEnv Env
  ext i v; dsimp [Env.union]
  constructor
  · intro hfinda; have := Batteries.AssocList.append_find?2 hfinda; grind
  · grind [Batteries.AssocList.append_find_left, Batteries.AssocList.append_find_right]

theorem subset_of_union {Ident Typ} [DecidableEq Typ] {ε₁ ε₂ : FinEnv Ident Typ} :
  Env.subsetOf ε₁.toEnv (ε₁ ++ ε₂).toEnv := by
  rw [union_eq]; exact Env.subset_of_union

theorem independent_subset_of_union {Ident Typ} [DecidableEq Typ] {ε₁ ε₂ : FinEnv Ident Typ} :
  Env.independent ε₁.toEnv ε₂.toEnv →
  Env.subsetOf ε₂.toEnv (ε₁ ++ ε₂).toEnv := by
  rw [union_eq]; exact Env.independent_subset_of_union

end FinEnv

end Graphiti
