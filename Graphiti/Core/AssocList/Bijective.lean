/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.AssocList.Basic
import Graphiti.AssocList.Lemmas
import Graphiti.Simp

import Mathlib.Logic.Function.Basic

namespace Batteries.AssocList

theorem mapKey_find? {α β γ} [DecidableEq α] [DecidableEq γ] {a : AssocList α β} {f : α → γ} {i} (hinj : Function.Injective f) :
  (a.mapKey f).find? (f i) = a.find? i := by
  induction a with
  | nil => simp
  | cons k v xs ih =>
    dsimp
    by_cases h : f k = f i
    · have h' := hinj h; simpa [h']
    · have h' := hinj.ne_iff.mp h;
      rw [Batteries.AssocList.find?.eq_2]
      rw [Batteries.AssocList.find?.eq_2]; rw [ih]
      have t1 : (f k == f i) = false := by simpa [*]
      have t2 : (k == i) = false := by simpa [*]
      rw [t1, t2]

theorem mapKey_contains {α β γ} [DecidableEq α] [DecidableEq γ] {m : AssocList α β} {f : α → γ} {k} {hf : Function.Injective f} :
  m.contains k = (m.mapKey f).contains (f k) := by
  cases h : contains k m <;> symm
  · rw [← Bool.not_eq_true] at *; intro hcont; apply h; clear h
    rw [←contains_find?_iff] at *; rcases hcont with ⟨v, hcont⟩; exists v
    rwa [mapKey_find?] at hcont; assumption
  · rw [←contains_find?_iff] at *; rcases h with ⟨v, h⟩; exists v
    rwa [mapKey_find?]; assumption

theorem eraseAll_comm_mapKey {α β γ} [DecidableEq α] [DecidableEq γ] {f : α → γ}
  {Hinj : Function.Injective f} {i} {m : AssocList α β} :
  (m.mapKey f).eraseAll (f i) = (m.eraseAll i).mapKey f := by
    induction m
    · simpa [eraseAll]
    · rename_i k v tl H
      cases Hfeq: f k == f i
      · simp only [eraseAll, eraseAllP, eraseAllP_TR_eraseAll] at *
        dsimp [eraseAll, eraseAllP]
        rw [Hfeq]
        dsimp
        cases Heq : k == i
        · simpa
        · simp [beq_iff_eq] at Heq Hfeq
          subst i
          contradiction
      · simp [beq_iff_eq] at Hfeq
        simpa [Hinj Hfeq]

theorem bijectivePortRenaming_bijective {α} [DecidableEq α] {p : AssocList α α} :
  Function.Bijective p.bijectivePortRenaming := by
  rw [Function.bijective_iff_existsUnique]
  intro b
  by_cases h : p.filterId.keysList.inter p.inverse.filterId.keysList = ∅ && p.keysList.Nodup && p.inverse.keysList.Nodup
  · cases h' : (p.filterId ++ p.inverse.filterId).find? b
    · refine ⟨b, ?_, ?_⟩ <;> (unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq])
      intro y Hy; simp only [List.empty_eq, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [invertible, h, List.empty_eq, and_self, decide_true, ↓reduceIte] at Hy
      cases h'' : AssocList.find? y (p.filterId ++ p.inverse.filterId) <;> (rw [h''] at Hy; dsimp at Hy) <;> try assumption
      subst b
      have := invertibleMap (by unfold invertible; simp [*]) h''
      simp only [lift_append] at this
      rw [this] at h'; injection h'
    · rename_i val
      refine ⟨val, ?_, ?_⟩ <;> (unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq])
      · simp at h; simp [invertible, h, -AssocList.find?_eq]
        rw [invertibleMap]; rfl; simp [invertible, *]; assumption
      · intros y hY
        simp at h; simp [invertible, h, -AssocList.find?_eq] at hY
        cases h'' : AssocList.find? y (p.filterId ++ p.inverse.filterId)
        · rw [h''] at hY; dsimp at hY; subst y; rw [h''] at h'; injection h'
        · rename_i val'; rw [h''] at hY; dsimp at *; subst b
          have := invertibleMap (by simp [invertible, *]) h''; rw [this] at h'; injection h'
  · refine ⟨b, ?_, ?_⟩ <;> (unfold bijectivePortRenaming; simp [invertible, *])
    · intros; exfalso; apply h; simp [*]
    · split; exfalso; apply h; simp [*]; simpa

end Batteries.AssocList
