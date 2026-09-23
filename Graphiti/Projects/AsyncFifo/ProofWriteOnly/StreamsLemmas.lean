/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.components.level0.Streams

/-! # `Streams`: the lemmas

Facts about the definitions in `components/level0/Streams.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo
variable {α β S I O : Type _}


theorem StrictPrefix.isPrefix {s₁ s₂ : List α} (h : s₁ ⊏ s₂) : s₁ <+: s₂ := h.1

theorem _root_.List.IsPrefix.getD_eq_left {l₁ l₂ : List α} (h : l₁ <+: l₂) {t : Nat} (ht : t < l₁.length) (d : α) :
    l₁.getD t d = l₂.getD t d := by
  obtain ⟨r, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

theorem prefix_iff_length_getD {l₁ l₂ : List α} (d : α) :
    l₁ <+: l₂ ↔ l₁.length ≤ l₂.length ∧ ∀ t, t < l₁.length → l₁.getD t d = l₂.getD t d := by
  constructor
  · intro h; exact ⟨h.length_le, fun t ht => h.getD_eq_left ht d⟩
  · rintro ⟨hlen, h⟩
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem
    · simp; omega
    · intro t h₁ h₂
      have := h t h₁
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
        List.getElem?_eq_getElem (by lia)] at this
      simp only [Option.getD_some] at this
      simp [List.getElem_take, this]

/-- Appending the next element of a longer stream keeps the prefix relation. -/
theorem prefix_append_getD {l₁ l₂ : List α} (h : l₁ <+: l₂) (hlt : l₁.length < l₂.length) (d : α) :
    l₁ ++ [l₂.getD l₁.length d] <+: l₂ := by
  obtain ⟨r, rfl⟩ := h
  cases r with
  | nil => simp at hlt
  | cons x r =>
    simp [List.getD_eq_getElem?_getD]

@[simp] theorem timeline_length (f : Nat → O) (N : Nat) : (timeline f N).length = N := by
  simp [timeline]

theorem timeline_getD (f : Nat → O) {N t : Nat} (ht : t < N) (d : O) : (timeline f N).getD t d = f t := by
  simp [timeline, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]

theorem timeline_mono {f f' : Nat → O} {N N' : Nat} (hN : N ≤ N') (h : ∀ t, t < N → f t = f' t) :
    timeline f N <+: timeline f' N' := by
  classical
  rw [prefix_iff_length_getD (f 0)]
  refine ⟨by simpa, fun t ht => ?_⟩
  simp only [timeline_length] at ht
  rw [timeline_getD _ ht, timeline_getD _ (Nat.lt_of_lt_of_le ht hN), h t ht]

@[simp] theorem run_zero (step : S → I → S) (init : S) (inp : Nat → I) : run step init inp 0 = init := rfl

@[simp] theorem run_succ (step : S → I → S) (init : S) (inp : Nat → I) (t : Nat) :
    run step init inp (t + 1) = step (run step init inp t) (inp t) := rfl

theorem run_congr (step : S → I → S) (init : S) {inp inp' : Nat → I} {T : Nat}
    (h : ∀ t, t < T → inp t = inp' t) : ∀ t, t ≤ T → run step init inp t = run step init inp' t := by
  intro t
  induction t with
  | zero => intro; rfl
  | succ t ih =>
    intro ht
    simp only [run_succ]
    rw [ih (by lia), h t (by lia)]

/-- Output stream of a Moore machine: `g` of the state at times `0, …, L`
(so it has length `L + 1`). -/
def moore (step : S → I → S) (init : S) (inp : Nat → I) (g : S → O) (L : Nat) : List O :=
  timeline (fun t => g (run step init inp t)) (L + 1)

@[simp] theorem moore_length (step : S → I → S) (init : S) (inp : Nat → I) (g : S → O) (L : Nat) :
    (moore step init inp g L).length = L + 1 := by simp [moore]

theorem moore_getD (step : S → I → S) (init : S) (inp : Nat → I) (g : S → O) {L t : Nat} (ht : t ≤ L) (d : O) :
    (moore step init inp g L).getD t d = g (run step init inp t) := by
  unfold moore; exact timeline_getD _ (Nat.lt_succ_of_le ht) d

theorem moore_mono (step : S → I → S) (init : S) {inp inp' : Nat → I} (g : S → O) {L L' : Nat}
    (hL : L ≤ L') (h : ∀ t, t < L → inp t = inp' t) :
    moore step init inp g L <+: moore step init inp' g L' := by
  apply timeline_mono (by lia)
  intro t ht
  rw [run_congr step init h t (by lia)]

theorem riseAt_prefix {c c' : List Bool} (h : c <+: c') {t : Nat} (ht : t < c.length) :
    riseAt c t = riseAt c' t := by
  unfold riseAt
  rw [h.getD_eq_left ht, h.getD_eq_left (t := t - 1) (by lia)]

@[simp] theorem events_zero (ev : Nat → Bool) (vals : Nat → α) : events ev vals 0 = [] := rfl

theorem events_succ (ev : Nat → Bool) (vals : Nat → α) (T : Nat) :
    events ev vals (T + 1) = events ev vals T ++ (if ev T then [vals T] else []) := by
  unfold events
  rw [List.range_succ, List.filterMap_append]
  congr 1
  by_cases h : ev T <;> simp [h]

theorem events_succ_of_pos {ev : Nat → Bool} {vals : Nat → α} {T : Nat} (h : ev T = true) :
    events ev vals (T + 1) = events ev vals T ++ [vals T] := by
  rw [events_succ]; simp [h]

theorem events_prefix_succ (ev : Nat → Bool) (vals : Nat → α) (T : Nat) :
    events ev vals T <+: events ev vals (T + 1) := by
  rw [events_succ]; exact List.prefix_append _ _

theorem events_prefix (ev : Nat → Bool) (vals : Nat → α) {T T' : Nat} (h : T ≤ T') :
    events ev vals T <+: events ev vals T' := by
  induction T' with
  | zero => cases Nat.le_zero.mp h; exact List.prefix_rfl
  | succ T' ih =>
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · exact (ih (by lia)).trans (events_prefix_succ _ _ _)
    · subst h'; exact List.prefix_rfl

theorem events_length_mono (ev : Nat → Bool) (vals : Nat → α) {T T' : Nat} (h : T ≤ T') :
    (events ev vals T).length ≤ (events ev vals T').length :=
  (events_prefix ev vals h).length_le

theorem events_congr {ev ev' : Nat → Bool} {vals vals' : Nat → α} {T : Nat}
    (h : ∀ t, t < T → ev t = ev' t ∧ vals t = vals' t) :
    events ev vals T = events ev' vals' T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [events_succ, events_succ, ih (fun t ht => h t (by lia))]
    obtain ⟨h₁, h₂⟩ := h T (by lia)
    rw [h₁, h₂]

/-- Congruence where the values only need to agree where an event fires. -/
theorem events_congr' {ev ev' : Nat → Bool} {vals vals' : Nat → α} {T : Nat}
    (h : ∀ t, t < T → ev t = ev' t ∧ (ev t = true → vals t = vals' t)) :
    events ev vals T = events ev' vals' T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [events_succ, events_succ, ih (fun t ht => h t (by lia))]
    obtain ⟨h1, h2⟩ := h T (Nat.lt_succ_self T)
    rw [← h1]
    by_cases hT : ev T = true
    · rw [h2 hT]
    · simp [hT]
end Graphiti.AsyncFifo