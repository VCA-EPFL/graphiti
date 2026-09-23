/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncOutMono
import Graphiti.Projects.AsyncFifo.components.level1.Gates

/-! # `Gates`: the lemmas

Facts about the definitions in `components/level1/Gates.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.Gates
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed

@[simp] theorem gateOut_length (f : Bool → Bool → Bool) (a b : List Bool) :
    (gateOut f a b).length = min a.length b.length + 1 := by
  simp [gateOut, List.length_zipWith]

@[simp] theorem gate1Out_length (f : Bool → Bool) (a : List Bool) :
    (gate1Out f a).length = a.length + 1 := by
  simp [gate1Out]

@[simp] theorem gate3Out_length (f : Bool → Bool → Bool → Bool) (a b c : List Bool) :
    (gate3Out f a b c).length = min (min a.length b.length) c.length + 1 := by
  simp [gate3Out, List.length_zipWith]

theorem gateOut_getD_zero (f : Bool → Bool → Bool) (a b : List Bool) :
    (gateOut f a b).getD 0 false = false := rfl

theorem gate1Out_getD_zero (f : Bool → Bool) (a : List Bool) :
    (gate1Out f a).getD 0 false = false := rfl

theorem gate3Out_getD_zero (f : Bool → Bool → Bool → Bool) (a b c : List Bool) :
    (gate3Out f a b c).getD 0 false = false := rfl

theorem gateOut_getD (f : Bool → Bool → Bool) (a b : List Bool) {t : Nat} (ht : 1 ≤ t)
    (ht' : t < min a.length b.length + 1) :
    (gateOut f a b).getD t false = f (a.getD (t - 1) false) (b.getD (t - 1) false) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hta : t < a.length := by omega
  have htb : t < b.length := by omega
  have hz : t < (List.zipWith f a b).length := by simp only [List.length_zipWith]; omega
  unfold gateOut
  rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_eq_getElem hz,
    Option.getD_some, List.getElem_zipWith]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hta, List.getElem?_eq_getElem htb]

theorem gate1Out_getD (f : Bool → Bool) (a : List Bool) {t : Nat} (ht : 1 ≤ t)
    (ht' : t < a.length + 1) :
    (gate1Out f a).getD t false = f (a.getD (t - 1) false) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hta : t < a.length := by omega
  unfold gate1Out
  rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  simp [List.getElem?_map, List.getElem?_eq_getElem hta, List.getD_eq_getElem?_getD]

theorem gate3Out_getD (f : Bool → Bool → Bool → Bool) (a b c : List Bool) {t : Nat} (ht : 1 ≤ t)
    (ht' : t < min (min a.length b.length) c.length + 1) :
    (gate3Out f a b c).getD t false =
      f (a.getD (t - 1) false) (b.getD (t - 1) false) (c.getD (t - 1) false) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hta : t < a.length := by omega
  have htb : t < b.length := by omega
  have htc : t < c.length := by omega
  have hz : t < (List.zipWith (fun x yz => f x yz.1 yz.2) a (b.zip c)).length := by
    simp only [List.length_zipWith, List.length_zip]; omega
  unfold gate3Out
  rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_eq_getElem hz,
    Option.getD_some, List.getElem_zipWith, List.getElem_zip]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hta, List.getElem?_eq_getElem htb,
    List.getElem?_eq_getElem htc]

theorem gate3Out_mono (f : Bool → Bool → Bool → Bool) {a a' b b' c c' : List Bool}
    (ha : a <+: a') (hb : b <+: b') (hc : c <+: c') : gate3Out f a b c <+: gate3Out f a' b' c' := by
  rw [prefix_iff_length_getD false]
  have := ha.length_le; have := hb.length_le; have := hc.length_le
  refine ⟨by simp only [gate3Out_length]; omega, fun t ht => ?_⟩
  simp only [gate3Out_length] at ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [gate3Out_getD_zero, gate3Out_getD_zero]
  · rw [gate3Out_getD f a b c hpos ht, gate3Out_getD f a' b' c' hpos (by omega),
      ha.getD_eq_left (by omega), hb.getD_eq_left (by omega), hc.getD_eq_left (by omega)]

theorem gateOut_mono (f : Bool → Bool → Bool) {a a' b b' : List Bool} (ha : a <+: a') (hb : b <+: b') :
    gateOut f a b <+: gateOut f a' b' := by
  rw [prefix_iff_length_getD false]
  have := ha.length_le; have := hb.length_le
  refine ⟨by simp only [gateOut_length]; omega, fun t ht => ?_⟩
  simp only [gateOut_length] at ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [gateOut_getD_zero, gateOut_getD_zero]
  · rw [gateOut_getD f a b hpos ht, gateOut_getD f a' b' hpos (by omega), ha.getD_eq_left (by omega),
      hb.getD_eq_left (by omega)]

theorem gate1Out_mono (f : Bool → Bool) {a a' : List Bool} (ha : a <+: a') : gate1Out f a <+: gate1Out f a' := by
  rw [prefix_iff_length_getD false]
  have := ha.length_le
  refine ⟨by simp only [gate1Out_length]; omega, fun t ht => ?_⟩
  simp only [gate1Out_length] at ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [gate1Out_getD_zero, gate1Out_getD_zero]
  · rw [gate1Out_getD f a hpos ht, gate1Out_getD f a' hpos (by omega), ha.getD_eq_left (by omega)]

/-- Two streams agree when they have the same length and the same elements. -/
theorem list_eq_of_getD {α : Type} {l₁ l₂ : List α} (d : α) (hl : l₁.length = l₂.length)
    (h : ∀ t, t < l₁.length → l₁.getD t d = l₂.getD t d) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro t h₁ h₂
  have := h t h₁
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂, Option.getD_some, Option.getD_some] at this
end Graphiti.AsyncFifo.Gates