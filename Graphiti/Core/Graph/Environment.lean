/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean

public import Graphiti.Core.Simp
public import Graphiti.Core.AssocList.Basic
public import Graphiti.Core.Graph.Module
public import Graphiti.Core.Graph.ExprHigh

@[expose] public section

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

theorem max_typeD_none [BEq (String × Nat)] [LawfulBEq (String × Nat)] {Ident n m} {f : FinEnv Ident (String × Nat)} :
  f.max_typeD ≤ m →
  m < n.2 →
  f.find? n = none := by
  dsimp [max_typeD, max_type]; intro h hlt
  match hsome : (List.map Prod.snd (Batteries.AssocList.keysList f)).max? with
  | some n' =>
    have hsome' := @List.max?_le_iff _ _ _ _ _ _ hsome
    rw [hsome] at h; dsimp at h
    rw [hsome'] at h
    match hfind? : f.find? n with
    | some elem =>
      exfalso
      specialize h n.2
      specialize h (by apply List.mem_map_of_mem; apply Batteries.AssocList.keysList_find'; rw [hfind?]; rfl)
      grind
    | none => rfl
  | none => simp_all [Batteries.AssocList.keysList]

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
