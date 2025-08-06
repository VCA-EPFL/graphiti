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

def union {Ident Typ} (ε₁ ε₂ : Env Ident Typ) : Env Ident Typ := λ s =>
  match ε₁ s with
  | some x => pure x
  | none => ε₂ s

def well_formed {α} (ε : Env String (String × α)) (s : String) : Prop :=
  match s with
  | "branch" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.branch T⟩
  | "cntrl_merge" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.cntrl_merge T⟩
  | "constant" => ∀ a mod, ε (s, a) = some mod → ∃ T, ∃ (t : T), mod = ⟨_, StringModule.constant t⟩
  | "fork" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Nat), mod = ⟨_, StringModule.fork T.1 T.2⟩
  | "init" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Sigma id), mod = ⟨_, StringModule.init T.1 T.2⟩
  | "join" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Type _), mod = ⟨_, StringModule.join T.1 T.2⟩
  | "load" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Type _), mod = ⟨_, StringModule.load T.1 T.2⟩
  | "merge" => ∀ a mod, ε (s, a) = some mod → ∃ (T : Type _ × Nat), mod = ⟨_, StringModule.merge T.1 T.2⟩
  | "mux" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.mux T⟩
  | "operator1" => ∀ a mod, ε (s, a) = some mod → ∃ T1 T2 T2m s, mod = ⟨_, @StringModule.operator1 T1 T2 T2m s⟩
  | "operator2" => ∀ a mod, ε (s, a) = some mod → ∃ T1 T2 T3 T3m s, mod = ⟨_, @StringModule.operator2 T1 T2 T3 T3m s⟩
  | "operator3" => ∀ a mod, ε (s, a) = some mod → ∃ T1 T2 T3 T4 T4m s, mod = ⟨_, @StringModule.operator3 T1 T2 T3 T4 T4m s⟩
  | "pure" => ∀ a mod, ε (s, a) = some mod → ∃ α β, ∃ (f : α → β), mod = ⟨_, StringModule.pure f⟩
  | "queue" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.queue T⟩
  | "sink" => ∀ a mod, ε (s, a) = some mod → ∃ T n, mod = ⟨_, StringModule.sink T n⟩
  | "split" => ∀ a mod, ε (s, a) = some mod → ∃ T T', mod = ⟨_, StringModule.split T T'⟩
  | "tagger_untagger_val" => ∀ a mod, ε (s, a) = some mod → ∃ TagT mm T T', mod = ⟨_, @StringModule.tagger_untagger_val TagT mm T T'⟩
  | _ => True

end Env

namespace FinEnv

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

def max_type {Ident} (f : FinEnv Ident (String × Nat)) : Nat :=
  f.keysList.map Prod.snd |>.foldl Nat.max 0

end FinEnv

end Graphiti
