/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean

public import Graphiti.Core.Module
public import Graphiti.Core.Simp
public import Graphiti.Core.ExprHigh
public import Graphiti.Core.AssocList.Basic
public import Graphiti.Core.Component

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

def well_formed'' (s : String) (m : TModule1 String) : Prop :=
  match s with
  | "branch" => ∃ T, m = ⟨_, StringModule.branch T⟩
  | "cntrl_merge" => ∃ T, m = ⟨_, StringModule.cntrl_merge T⟩
  | "constant" => ∃ (T : Sigma id), m = ⟨_, StringModule.constant T.2⟩
  | "fork" => ∃ (T : Type _ × Nat), m = ⟨_, StringModule.fork T.1 T.2⟩
  | "fork2" => ∃ T, m = ⟨_, StringModule.fork2 T⟩
  | "init" => ∃ (T : Sigma id), m = ⟨_, StringModule.init T.1 T.2⟩
  | "initBool" => m = ⟨_, StringModule.init Bool false⟩
  | "join" => ∃ (T : Type _ × Type _), m = ⟨_, StringModule.join T.1 T.2⟩
  | "load" => ∃ (T : Type _ × Type _), m = ⟨_, StringModule.load T.1 T.2⟩
  | "merge" => ∃ (T : Type _ × Nat), m = ⟨_, StringModule.merge T.1 T.2⟩
  | "merge2" => ∃ T, m = ⟨_, StringModule.merge T 2⟩
  | "mux" => ∃ T, m = ⟨_, StringModule.mux T⟩
  | "operator1" => ∃ (T : Type _ × (Sigma (λ x => Inhabited x)) × String), m = ⟨_, @StringModule.operator1 T.1 T.2.1.1 T.2.1.2 T.2.2⟩
  | "operator2" => ∃ (T : Type _ × Type _ × (Sigma (λ x => Inhabited x)) × String), m = ⟨_, @StringModule.operator2 T.1 T.2.1 T.2.2.1.1 T.2.2.1.2 T.2.2.2⟩
  | "operator3" => ∃ (T : Type _ × Type _ × Type _ × (Sigma (λ x => Inhabited x)) × String), m = ⟨_, @StringModule.operator3 T.1 T.2.1 T.2.2.1 T.2.2.2.1.1 T.2.2.2.1.2 T.2.2.2.2⟩
  | "pure" => ∃ (T : Σ R, Σ S, R → S), m = ⟨_, StringModule.pure T.2.2⟩
  | "queue" => ∃ T, m = ⟨_, StringModule.queue T⟩
  | "sink" => ∃ (T : Type _ × Nat), m = ⟨_, StringModule.sink T.1 T.2⟩
  | "split" => ∃ (T : Type _ × Type _), m = ⟨_, StringModule.split T.1 T.2⟩
  | "tagger_untagger_val" => ∃ (T : Sigma (λ x => DecidableEq x) × Type _ × Type _), m = ⟨_, @StringModule.tagger_untagger_val T.1.1 T.1.2 T.2.1 T.2.2⟩
  | "tagger_untagger_val_ghost" => ∃ (T : Sigma (λ x => DecidableEq x) × Type _), m = ⟨_, @StringModule.tagger_untagger_val_ghost T.1.1 T.1.2 T.2⟩
  | _ => True

def well_formed' {α} (ε : Env String (String × α)) (s : String × α) : Prop :=
  match s.1 with
  | "branch" => ∃ T, ε s = some ⟨_, StringModule.branch T⟩
  | "cntrl_merge" => ∃ T, ε s = some ⟨_, StringModule.cntrl_merge T⟩
  | "constant" => ∃ (T : Sigma id), ε s = some ⟨_, StringModule.constant T.2⟩
  | "fork" => ∃ (T : Type _ × Nat), ε s = some ⟨_, StringModule.fork T.1 T.2⟩
  | "fork2" => ∃ T, ε s = some ⟨_, StringModule.fork2 T⟩
  | "init" => ∃ (T : Sigma id), ε s = some ⟨_, StringModule.init T.1 T.2⟩
  | "initBool" => ε s = some ⟨_, StringModule.init Bool false⟩
  | "join" => ∃ (T : Type _ × Type _), ε s = some ⟨_, StringModule.join T.1 T.2⟩
  | "load" => ∃ (T : Type _ × Type _), ε s = some ⟨_, StringModule.load T.1 T.2⟩
  | "merge" => ∃ (T : Type _ × Nat), ε s = some ⟨_, StringModule.merge T.1 T.2⟩
  | "merge2" => ∃ T, ε s = some ⟨_, StringModule.merge T 2⟩
  | "mux" => ∃ T, ε s = some ⟨_, StringModule.mux T⟩
  | "operator1" => ∃ (T : Type _ × (Sigma (λ x => Inhabited x)) × String), ε s = some ⟨_, @StringModule.operator1 T.1 T.2.1.1 T.2.1.2 T.2.2⟩
  | "operator2" => ∃ (T : Type _ × Type _ × (Sigma (λ x => Inhabited x)) × String), ε s = some ⟨_, @StringModule.operator2 T.1 T.2.1 T.2.2.1.1 T.2.2.1.2 T.2.2.2⟩
  | "operator3" => ∃ (T : Type _ × Type _ × Type _ × (Sigma (λ x => Inhabited x)) × String), ε s = some ⟨_, @StringModule.operator3 T.1 T.2.1 T.2.2.1 T.2.2.2.1.1 T.2.2.2.1.2 T.2.2.2.2⟩
  | "pure" => ∃ (T : Σ R, Σ S, R → S), ε s = some ⟨_, StringModule.pure T.2.2⟩
  | "queue" => ∃ T, ε s = some ⟨_, StringModule.queue T⟩
  | "sink" => ∃ (T : Type _ × Nat), ε s = some ⟨_, StringModule.sink T.1 T.2⟩
  | "split" => ∃ (T : Type _ × Type _), ε s = some ⟨_, StringModule.split T.1 T.2⟩
  | "tagger_untagger_val" => ∃ (T : Sigma (λ x => DecidableEq x) × Type _ × Type _), ε s = some ⟨_, @StringModule.tagger_untagger_val T.1.1 T.1.2 T.2.1 T.2.2⟩
  | "tagger_untagger_val_ghost" => ∃ (T : Sigma (λ x => DecidableEq x) × Type _), ε s = some ⟨_, @StringModule.tagger_untagger_val_ghost T.1.1 T.1.2 T.2⟩
  | _ => True

def well_formed {α} (ε : Env String (String × α)) : Prop :=
  ∀ s, (ε s).isSome → well_formed' ε s

def well_formed_alt {α} (ε : Env String (String × α)) : Prop :=
  ∀ s y, ε s = some y → well_formed'' s.1 y

theorem well_formed_alt_correct {α} {ε : Env String (String × α)} :
  well_formed ε ↔ well_formed_alt ε := by
  constructor
  · intro hwf
    dsimp [well_formed, well_formed_alt] at *
    intro s y hsome
    specialize hwf _ (by rw [hsome]; rfl)
    dsimp [well_formed'', well_formed'] at *
    split at hwf
    all_goals
      try obtain ⟨T, ht⟩ := hwf; exists T
      grind
  · intro hwf
    dsimp [well_formed, well_formed_alt] at *
    intro s hsome
    have ⟨y, hsome'⟩ := Option.isSome_iff_exists.mp hsome
    specialize hwf _ _ hsome'
    dsimp [well_formed'', well_formed'] at *
    split at hwf
    all_goals
      try obtain ⟨T, ht⟩ := hwf; exists T
      grind

end Env

def ExprLow.well_formed_wrt {α} (ε : Env String (String × α)) : ExprLow String (String × α) → Prop
| product e1 e2 =>
  e1.well_formed_wrt ε ∧ e2.well_formed_wrt ε
| connect c e => e.well_formed_wrt ε
| base inst t => ε.well_formed' t

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
