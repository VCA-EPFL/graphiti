/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Mathlib.Logic.Function.Basic

public import Graphiti.Core.AssocList.Basic
public import Graphiti.Core.AssocList.Lemmas
public import Graphiti.Core.Simp

@[expose] public section

namespace Batteries.AssocList

theorem mapKey_find? {α β γ} [DecidableEq α] [DecidableEq γ] {a : AssocList α β} {f : α → γ} {i} (hinj : Function.Injective f) :
  (a.mapKey f).find? (f i) = a.find? i := by
  induction a with
  | nil => simp
  | cons k v xs ih => by_cases h : k = i <;> simp_all [hinj.eq_iff, mapKey_cons, -find?_eq]

theorem mapKey_contains {α β γ} [DecidableEq α] [DecidableEq γ] {m : AssocList α β} {f : α → γ} {k} {hf : Function.Injective f} :
  m.contains k = (m.mapKey f).contains (f k) := by
  rw [Bool.eq_iff_iff, ← contains_find?_isSome_iff, ← contains_find?_isSome_iff, mapKey_find? hf]

theorem eraseAll_comm_mapKey {α β γ} [DecidableEq α] [DecidableEq γ] {f : α → γ}
  {Hinj : Function.Injective f} {i} {m : AssocList α β} :
  (m.mapKey f).eraseAll (f i) = (m.eraseAll i).mapKey f := by
  induction m with
  | nil => simp [eraseAll]
  | cons k v tl H => by_cases k = i <;> simp_all [eraseAll, eraseAllP_TR_eraseAll, Hinj.eq_iff]

theorem bijectivePortRenaming_involutive {α} [DecidableEq α] {p : AssocList α α} :
  Function.Involutive p.bijectivePortRenaming := by
  intro i
  dsimp [bijectivePortRenaming]
  split
  next hinv =>
    cases h' : (p.filterId ++ p.inverse.filterId).find? i with
    | none => simp only [h', Option.getD_none]
    | some v => simp only [h', Option.getD_some, invertibleMap hinv h']
  next => rfl

theorem bijectivePortRenaming_bijective {α} [DecidableEq α] {p : AssocList α α} :
  Function.Bijective p.bijectivePortRenaming :=
  bijectivePortRenaming_involutive.bijective

theorem mapKey_involutive {α β} {f : α → α} (a : AssocList α β) :
  Function.Involutive f →
  (a.mapKey f).mapKey f = a := by
  intro hinv; induction a <;> simp_all [Function.Involutive, mapKey_cons, mapKey_nil]

end Batteries.AssocList
