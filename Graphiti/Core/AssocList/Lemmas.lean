/-
Copyright (c) 2024, 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.AssocList.Basic
import Graphiti.Core.Simp

namespace Batteries.AssocList

theorem append_eq {α β} {a b : AssocList α β} :
  (a ++ b).toList = a.toList ++ b.toList := by
  induction a generalizing b <;> simpa [*, append]

theorem append_eq2 {α β} {a b : AssocList α β} :
  a ++ b = (a.toList ++ b.toList).toAssocList := by
  induction a generalizing b <;> simpa [*, append]

theorem append_assoc {α β} {a b c : AssocList α β} :
  a ++ b ++ c = a ++ (b ++ c) := by
  induction a with
  | nil => rfl
  | cons k v xs ih => simp [*]

@[simp, drcompute] theorem append_nil {α β} {l : AssocList α β}:
  l ++ AssocList.nil = l := by induction l <;> simpa [append]

@[simp, drcompute] theorem cons_concat_append {α β} {l l' : AssocList α β} {k v}:
  l ++ l'.cons k v = l.concat k v ++ l' := by
  induction l generalizing l' with
  | nil => rfl
  | cons k' v' xs ih =>
    rw [show xs.cons k' v' = AssocList.nil.cons k' v' ++ xs by rfl]
    rw [show cons k' v' nil ++ xs ++ cons k v l' = cons k' v' nil ++ (xs ++ cons k v l') by rfl]
    rw [ih]
    rfl

@[simp] theorem cons_concat_append2 {α β} {l l' : AssocList α β} {k v}:
  (l ++ l').concat k v = l ++ l'.concat k v := append_assoc

private theorem eraseAllP_TR_go_eraseAll {α β} [DecidableEq α] {f : α → β → Bool} {m' m : AssocList α β} :
  m' ++ (m.eraseAllP f) = eraseAllP_TR.go f m' m := by
  induction m generalizing m' with
  | nil => simp [eraseAllP_TR.go, append_nil]
  | cons k v xs ih =>
    dsimp [eraseAllP, eraseAllP_TR.go]
    cases f k v <;> simp [*, cons_concat_append]

@[simp] theorem eraseAllP_TR_eraseAll {α β} [DecidableEq α] (f : α → β → Bool) {m : AssocList α β} :
  m.eraseAllP_TR f = m.eraseAllP f := @eraseAllP_TR_go_eraseAll _ _ _ f .nil m |>.symm

theorem append_find? {α β} [DecidableEq α] (a b : AssocList α β) (i) :
  (a ++ b).find? i = a.find? i
  ∨ (a ++ b).find? i = b.find? i := by
  induction a with
  | nil => simp
  | cons k v t ih =>
    by_cases h : k = i
    <;> simp_all [List.find?_cons_of_pos, List.find?_cons_of_neg, find?_eq]

theorem append_find?2 {α β} [DecidableEq α] {a b : AssocList α β} {i x} :
  (a ++ b).find? i = some x →
  a.find? i = some x ∨ (a.find? i = none ∧ b.find? i = some x) := by
  induction a with
  | nil => simp
  | cons k v t ih =>
    by_cases h : k = i
    <;> simp_all [List.find?_cons_of_pos, List.find?_cons_of_neg]

theorem find?_mapVal {α β γ} [DecidableEq α] {a : AssocList α β} {f : α → β → γ} {i}:
  (a.mapVal f).find? i = (a.find? i).map (f i) := by
  induction a with
  | nil => simp
  | cons k v a ih => dsimp [find?]; split <;> simp_all

theorem disjoint_cons_left {α β γ} [DecidableEq α] {t : AssocList α β} {b : AssocList α γ} {a y} :
  (cons a y t).disjoint_keys b = true → t.disjoint_keys b = true := by
  unfold disjoint_keys; intros; simp [*]
  simp [List.inter.eq_1] at *
  rename_i h
  intro el hin; apply h
  simp_all [keysList]

theorem disjoint_keys_symm {α β γ} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} :
  a.disjoint_keys b → b.disjoint_keys a := by
  unfold disjoint_keys
  simp; intro H
  simp [List.inter.eq_1] at *
  unfold Not at *; intros
  solve_by_elim

theorem append_find_left {α β} [DecidableEq α] {a b : AssocList α β} {i x} :
  a.find? i = some x →
  (a ++ b).find? i = some x := by
  induction a with
  | nil => simp
  | cons a y t ih =>
    intro hfind
    simp only [cons_append]
    rw [Batteries.AssocList.find?.eq_2] at hfind ⊢
    split <;> rename_i _ heq
    · simp_all
    · simp only [heq] at hfind; solve_by_elim

theorem append_find_right {α β} [DecidableEq α] (a b : AssocList α β) {i} :
  a.find? i = none →
  (a ++ b).find? i = b.find? i := by
  induction a with
  | nil => simp
  | cons a y t ih =>
    intro hfind
    simp only [cons_append]
    rw [Batteries.AssocList.find?.eq_2] at hfind ⊢
    split <;> rename_i _ heq
    · simp_all
    · simp only [heq] at hfind; solve_by_elim

private theorem map_keys_list' {α β γ} [DecidableEq α] {f : α → β → γ} {l : List (α × β)} {ident val} :
  List.find? (fun x => x.fst == ident) l = some val →
  List.find? ((fun x => x.fst == ident) ∘ fun x => (x.fst, f x.fst x.snd)) l = some (ident, val.snd) := by
  induction l generalizing ident val <;> simp_all
  rename_i head tail iH
  intro Hfirst
  rcases Hfirst with ⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩
  subst_vars; left; simp
  right; and_intros; assumption
  apply iH
  assumption

theorem map_keys_list {α β γ} [DecidableEq α] {ident} {l : AssocList α β} {f : α → β → γ} :
    (l.mapVal f).find? ident = (l.find? ident).map (f ident) := by
  simp only [find?_eq, toList_mapVal, List.find?_map, Option.map_map]
  cases h : List.find? (fun x => x.fst == ident) l.toList <;> simp_all
  · assumption
  · rename_i val
    refine ⟨ ident, val.snd, ?_ ⟩
    and_intros <;> try rfl
    apply map_keys_list'; assumption

theorem mapKey_toList {α β} {l : AssocList α β} {f : α → α} :
  l.mapKey f = (l.toList.map (λ | (a, b) => (f a, b))).toAssocList := by
  induction l <;> simp [*]

theorem mapKey_id {α β} {l : AssocList α β} :
  l.mapKey id = l := by induction l <;> simp [*]

@[drcompute]
theorem mapVal_map_toAssocList {T α β1 β2} {l : List T}
  {f : α → β1 → β2} {g : T → α} {h : T → β1}:
  mapVal f (List.map (λ x => (g x, h x)) l).toAssocList
  = (List.map (λ x => (g x, f (g x) (h x))) l).toAssocList := by
  induction l <;> simpa

@[drcompute]
theorem mapVal_map_toAssocList2 {α1 α2 β1 β2 β3} {l : List (α1 × β1)}
  {f : α2 → β2 → β3} {g : α1 → α2} {h : β1 → β2}:
  mapVal f (List.map (λ (k, v) => (g k, h v)) l).toAssocList
  = (List.map (λ (k, v) => (g k, f (g k) (h v))) l).toAssocList := by
  induction l <;> simpa

@[drcompute]
theorem mapKey_map_toAssocList {T α1 α2 β} {l : List T}
  {f : α1 → α2} {g : T → α1} {h : T → β}:
  mapKey f (List.map (λ x => (g x, h x)) l).toAssocList
  = (List.map (λ x => (f (g x), h x)) l).toAssocList := by
  induction l <;> simpa

@[drcompute]
theorem mapKey_map_toAssocList2 {α1 α2 α3 β1 β2} {l : List (α1 × β1)}
  {f : α2 → α3} {g : α1 → α2} {h : β1 → β2}:
  mapKey f (List.map (λ (k, v) => (g k, h v)) l).toAssocList
  = (List.map (λ (k, v) => (f (g k), (h v))) l).toAssocList := by
  induction l <;> simpa

theorem mapKey_toList2 {α β} {l : AssocList α β} {f : α → α} :
  (l.mapKey f).toList = (l.toList.map (λ | (a, b) => (f a, b))) := by
  induction l <;> simpa

theorem contains_none {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ¬ m.contains ident → m.find? ident = none := by
    intros H; rw [Batteries.AssocList.contains_eq] at H
    rw [Batteries.AssocList.find?_eq, Option.map_eq_none', List.find?_eq_none]
    intros x H
    rcases x with ⟨a, b⟩
    simp at *; intros _; apply H
    subst_vars; assumption

theorem find?_eq_contains {α β} [DecidableEq α] {x y : AssocList α β} {k} :
  (∀ i, x.contains i → x.find? i = y.find? i) →
  (∀ i, y.contains i → x.find? i = y.find? i) →
  x.find? k = y.find? k := by
  intro h1 h2
  by_cases x.contains k
  · solve_by_elim
  · by_cases y.contains k
    · solve_by_elim
    · repeat1' rw [AssocList.contains_none]
      all_goals assumption

theorem find?_map_neq {α β γ} [DecidableEq β] k (f : α → β) (g : α → γ) {l : List α}
  (Hneq: ∀ x, x ∈ l → f x ≠ k):
  AssocList.find? k (List.map (λ x => ⟨f x, g x⟩) l).toAssocList = none := by
      simpa [contains_none, Hneq]

theorem contains_some {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    m.contains ident →
    (m.find? ident).isSome := by
  intros H; rw [Batteries.AssocList.contains_eq] at H; simp at H; rcases H with ⟨ a, H ⟩
  simp [*]; constructor; assumption

theorem contains_some2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (m.find? ident).isSome →
    m.contains ident := by
  intro; by_cases contains ident m = true; assumption
  rename_i a b; have := contains_none b
  rw [this] at a; contradiction

theorem contains_some3 {α β} [DecidableEq α] {m : AssocList α β} {ident x} :
    m.find? ident = some x →
    m.contains ident := by
  intro h; apply contains_some2; rw [h]; rfl

theorem contains_find?_iff {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (∃ x, m.find? ident = some x) ↔ m.contains ident := by
  constructor
  · intro h; cases h; solve_by_elim [contains_some3]
  · intro h; rw [← Option.isSome_iff_exists]; solve_by_elim [contains_some]

theorem contains_find?_isSome_iff {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (m.find? ident).isSome ↔ m.contains ident := by
  rw [Option.isSome_iff_exists]; apply contains_find?_iff

theorem contains_find?_none_iff {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    m.find? ident = none ↔ m.contains ident = false := by
  constructor
  · intro find?; cases h : contains ident m <;> try rfl
    rw [←contains_find?_isSome_iff, find?] at h; contradiction
  · intro cont; cases h : find? ident m <;> try rfl
    have h' : (find? ident m).isSome := by rewrite [h]; rfl
    grind [contains_find?_isSome_iff]

theorem keysList_find {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  (m.find? ident).isSome → ident ∈ m.keysList := by simp_all [keysList]

theorem keysList_find2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ident ∈ m.keysList → (m.find? ident).isSome := by simp_all [keysList]

theorem notkeysList_find2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ident ∉ m.keysList → m.find? ident = none := by
  have : ¬ (m.find? ident).isSome → m.find? ident = none := by
    intro h; simp at h; simp
    skip; intros; unfold Not; intros; apply h; subst_vars; assumption
  intro; apply this; unfold Not; intros; simp_all [keysList]

theorem keysList_cons {α β} {xs : AssocList α β} {k v} :
  (cons k v xs).keysList = k :: xs.keysList := by rfl

theorem valsList_cons {α β} {xs : AssocList α β} {k v} :
  (cons k v xs).valsList = v :: xs.valsList := by rfl

theorem append_find_right_disjoint {α β} [DecidableEq α] {a b : AssocList α β} {i x} :
  a.disjoint_keys b →
  b.find? i = some x →
  (a ++ b).find? i = some x := by
  induction a with
  | nil => simp
  | cons a y t ih =>
    intro hdisj hfind
    simp only [cons_append]
    rw [Batteries.AssocList.find?.eq_2]
    split <;> rename_i _ heq
    · exfalso; clear ih;
      simp_all only [disjoint_keys]
      simp [Inter.inter, List.instInterOfBEq_batteries, List.inter.eq_1] at hdisj
      apply hdisj; constructor; simp at heq; subst_vars
      apply keysList_find; rw [Option.isSome_iff_exists]
      solve_by_elim
    · solve_by_elim [disjoint_cons_left]

-- @[simp] theorem erase_map_comm {α β γ} [DecidableEq α] {a : AssocList α β} ident (f : α → β → γ) :
--   (a.erase ident).mapVal f = (a.mapVal f).erase ident := by sorry

@[simp, drcompute] theorem eraseAllP_cons {α β} [DecidableEq α] {a : AssocList α β} {p : α → β → Bool} {ident val} :
  (a.cons ident val).eraseAllP p = if p ident val then a.eraseAllP p else (a.eraseAllP p).cons ident val := by simpa

@[simp, drcompute] theorem eraseAll_cons_eq {α β} [DecidableEq α] {a : AssocList α β} {ident val} :
  ((a.cons ident val).eraseAll ident) = a.eraseAll ident := by simp [*, eraseAll]

@[simp, drcompute] theorem eraseAll_cons_neq {α β} [DecidableEq α] {a : AssocList α β} {ident ident' val} :
  ident' ≠ ident →
  ((a.cons ident' val).eraseAll ident) = (a.eraseAll ident).cons ident' val := by
  simpa +contextual [eraseAll, beq_false_of_ne]

@[simp, drcompute] theorem eraseAllP_nil {α β} [DecidableEq α] {a : AssocList α β} {p : α → β → Bool} :
  ((@nil α β).eraseAllP p) = .nil := by simp [*, eraseAll]

@[simp, drcompute] theorem eraseAll_nil {α β} [DecidableEq α] {ident} :
  ((@nil α β).eraseAll ident) = .nil := by rfl

@[simp, drcompute] theorem eraseAllP_concat {α β} [DecidableEq α] {a b : AssocList α β} {p : α → β → Bool} :
  (a ++ b).eraseAllP p = (a.eraseAllP p) ++ (b.eraseAllP p) := by
    induction a with
    | nil => rfl
    | cons k v tl ih => dsimp; rw [ih] <;> cases p k v <;> dsimp

@[simp] theorem eraseAllP_map_comm {α β γ} [DecidableEq α] {a : AssocList α β} {p : α → Bool} {f : α → β → γ} :
  (a.eraseAllP (λ k _ => p k)).mapVal f = (a.mapVal f).eraseAllP (λ k _ => p k) := by
  induction a with
  | nil => rfl
  | cons k v xs ih => dsimp <;> cases p k <;> dsimp <;> rw [ih] <;> dsimp

@[simp] theorem eraseAll_map_comm {α β γ} [DecidableEq α] {a : AssocList α β} {ident} {f : α → β → γ} :
  (a.eraseAll ident).mapVal f = (a.mapVal f).eraseAll ident := by
  induction a generalizing ident with
  | nil => rfl
  | cons k v xs ih =>
    by_cases k = ident <;> simpa [*, eraseAll_cons_eq, mapVal, eraseAll_cons_neq]

@[simp] theorem find?_cons_eq {α β} [DecidableEq α] {a : AssocList α β} {ident val} :
  ((a.cons ident val).find? ident) = some val := by
    simpa

@[simp] theorem find?_cons_eq' {α β} [BEq α] [LawfulBEq α] {a : AssocList α β} {ident val} :
  ((a.cons ident val).find? ident) = some val := by
  simpa

@[simp] theorem find?_cons_neq {α β} [DecidableEq α] {a : AssocList α β} {ident ident' val} :
  ident' ≠ ident → ((a.cons ident' val).find? ident) = a.find? ident := by
    simp +contextual (disch := assumption) [find?, beq_false_of_ne]

@[simp] theorem find?_cons_neq' {α β} [BEq α] [LawfulBEq α] {a : AssocList α β} {ident ident' val} :
  ident' ≠ ident → ((a.cons ident' val).find? ident) = a.find? ident := by
    simp +contextual (disch := assumption) [find?, beq_false_of_ne]

@[simp, drcompute] theorem find?_nil {α β} [DecidableEq α] {ident} :
  (nil : AssocList α β).find? ident = none := rfl

@[deprecated find?_cons_eq (since := "2025-05-06")]
theorem find?_gss : ∀ {α} [DecidableEq α] {β x v} {pm: AssocList α β},
  (AssocList.find? x (AssocList.cons x v pm)) = .some v := find?_cons_eq

@[deprecated find?_cons_neq (since := "2025-05-06")]
theorem find?_gso : ∀ {α} [DecidableEq α] {β x' x v} {pm: AssocList α β},
  x ≠ x' → AssocList.find? x' (AssocList.cons x v pm) = AssocList.find? x' pm := find?_cons_neq

@[deprecated find?_nil (since := "2025-05-06")]
theorem find?_ge : ∀ {α} [DecidableEq α] {β x},
  AssocList.find? x (.nil : AssocList α β) = .none := find?_nil

@[simp] theorem find?_map_comm {α β γ} [DecidableEq α] {a : AssocList α β} ident (f : β → γ) :
  (a.find? ident).map f = (a.mapVal (λ _ => f)).find? ident := by
  induction a with
  | nil => rfl
  | cons k v xs ih =>
    by_cases k = ident
    · subst k; simp
    · simp (disch := assumption) only [*, find?_cons_neq, mapVal]

@[simp] theorem find?_eraseAll_eq {α β} [DecidableEq α] (a : AssocList α β) i :
  (a.eraseAll i).find? i = none := by
  induction a with
  | nil => rfl
  | cons k v xs ih =>
    by_cases i = k
    · subst i; rwa [eraseAll_cons_eq]
    · have : i ≠ k := by assumption
      symm_saturate; simp [*]

@[simp] theorem find?_eraseAll_list {α β} { T : α} [DecidableEq α] (a : AssocList α β):
  List.find? (fun x => x.1 == T) (AssocList.eraseAllP (fun k x => decide (k = T)) a).toList = none := by
  rw [←Batteries.AssocList.findEntry?_eq, ←Option.map_eq_none', ←Batteries.AssocList.find?_eq_findEntry?]
  have := find?_eraseAll_eq a T; unfold eraseAll at *; rw [eraseAllP_TR_eraseAll] at *; assumption

@[simp] theorem find?_eraseAll_neq {α β} [DecidableEq α] {a : AssocList α β} {i i'} :
  i ≠ i' → (a.eraseAll i').find? i = a.find? i := by
  induction a with
  | nil => simp [eraseAll]
  | cons k v xs ih =>
    intro neq
    by_cases i' = k
    · subst i'; symm_saturate; simp (disch := assumption) only [eraseAll_cons_eq, find?_cons_neq, *]
    · have : i' ≠ k := by assumption
      symm_saturate; simp (disch := assumption) only [eraseAll_cons_neq];
      by_cases i = k
      · subst i; simp
      · have : i ≠ k := by assumption
        symm_saturate; simp (disch := assumption) only [eraseAll_cons_eq, find?_cons_neq, *]

@[simp] theorem find?_eraseAll_neg {α β} { T : α} { T' : α} [DecidableEq α] (a : AssocList α β) (i : β):
  Batteries.AssocList.find? T (AssocList.eraseAllP (fun k x => decide (k = T')) a) = some i -> ¬ (T = T') -> (Batteries.AssocList.find? T a = some i) := by
  intro hfind hne
  have := find?_eraseAll_neq (a := a) hne
  unfold eraseAll at this
  simp only [BEq.beq] at this; rw [eraseAllP_TR_eraseAll] at *; rwa [this] at hfind

theorem find?_eraseAll_neg_full {α β} { T : α} { T' : α} [DecidableEq α] {a : AssocList α β} {i : β}:
  (AssocList.eraseAll T' a).find? T = some i → T ≠ T' ∧ a.find? T = some i := by
  by_cases h : T = T' <;> grind [find?_eraseAll_eq, find?_eraseAll_neq]

theorem find?_eraseAll {α β} [DecidableEq α] {a : AssocList α β} {i i' v} :
  (a.eraseAll i').find? i = some v → a.find? i = some v := by
  intro h; by_cases heq : i = i'
  · subst i'; rw [find?_eraseAll_eq] at h; contradiction
  . rwa [find?_eraseAll_neq] at h; assumption

theorem contains_eraseAll {α β} [DecidableEq α] {a : AssocList α β} {i i'} :
  (a.eraseAll i').contains i → a.contains i := by
  simp only [←contains_find?_iff]; intro ⟨_, _⟩; solve_by_elim [find?_eraseAll]

theorem eraseAll_not_contains {α β} [DecidableEq α] (a : AssocList α β) (i : α) :
  ¬a.contains i → a.eraseAll i = a := by
    intros H
    induction a <;> simp [eraseAll]
    rename_i k v a' HR
    cases Heq: (k == i)
    · simp; rw [←eraseAllP_TR_eraseAll]; apply HR; intros Hcontains; apply H; simp; right;
      simp at Hcontains; assumption
    · exfalso; apply H
      simp; left; simp at Heq; assumption

theorem eraseAll_not_contains2 {α β} [DecidableEq α] (a : AssocList α β) (i : α) :
  ¬ (a.eraseAll i).contains i := by
  rw [← contains_find?_iff]; intro ⟨x, h⟩
  rw [find?_eraseAll_eq] at h; contradiction

@[simp, drcompute] theorem eraseAll_map_neq {α β γ} [DecidableEq α] [DecidableEq β]
    (f : α → β) (g : α → γ) (l : List α) (k : β) (Hneq : ∀ x, f x ≠ k) :
    (List.map (λ x => (f x, g x)) l).toAssocList.eraseAll k =
    (List.map (λ x => (f x, g x)) l).toAssocList :=
  by
    apply (eraseAll_not_contains (a := (List.map (fun x => (f x, g x)) l).toAssocList))
    induction l <;> simp
    and_intros <;> try intros <;> apply Hneq

@[drcompute]
theorem eraseAll_append {α β} [DecidableEq α] {l1 l2 : AssocList α β} {i}:
  AssocList.eraseAll i (l1 ++ l2) =
  AssocList.eraseAll i l1 ++ AssocList.eraseAll i l2 := by
    induction l1 <;> simp [eraseAll, append]
    rename_i k _ _ _
    cases k == i <;> simp [eraseAllP_TR_eraseAll, eraseAll] at * <;> simpa [append, eraseAll]

@[simp, drcompute] theorem eraseAll_concat_eq {α β} [DecidableEq α] {a : AssocList α β} {ident val} :
  ((a.concat ident val).eraseAll ident) = a.eraseAll ident := by
    dsimp [AssocList.concat]
    rw [eraseAll_append, eraseAll_cons_eq, eraseAll_nil, append_nil]

@[simp, drcompute] theorem eraseAll_concat_neq {α β} [DecidableEq α] {a : AssocList α β} {ident ident' val} :
  ident' ≠ ident →
  ((a.concat ident' val).eraseAll ident) = (a.eraseAll ident).concat ident' val := by
    intros Hneq
    dsimp [AssocList.concat]
    rw [eraseAll_append, eraseAll_cons_neq Hneq, eraseAll_nil]

@[simp] theorem any_map {α β} {f : α → β} {l : List α} {p : β → Bool} : (l.map f).any p = l.any (p ∘ f) := by
  induction l <;> simp

theorem keysInMap {α β} [DecidableEq α] {m : AssocList α β} {k} : m.contains k → k ∈ m.keysList := by
  unfold Batteries.AssocList.contains Batteries.AssocList.keysList
  intro Hk; simp_all

theorem keysNotInMap {α β} [DecidableEq α] {m : AssocList α β} {k} : ¬ m.contains k → k ∉ m.keysList := by
  unfold Batteries.AssocList.contains Batteries.AssocList.keysList
  intro Hk; simp_all

theorem keysList_contains_iff {α β} [DecidableEq α] {m : AssocList α β} {k} :
  m.contains k ↔ k ∈ m.keysList := by
  constructor
  · exact keysInMap
  · intro h
    by_cases h' : contains k m <;> try assumption
    exfalso; apply keysNotInMap (α := α) <;> assumption

theorem keysList_find?_isSome_iff {α β} [DecidableEq α] {m : AssocList α β} {k} :
  (m.find? k).isSome ↔ k ∈ m.keysList := by
  rw [contains_find?_isSome_iff, keysList_contains_iff]

theorem keysList_find?_iff {α β} [DecidableEq α] {m : AssocList α β} {k} :
  (∃ v, m.find? k = .some v) ↔ k ∈ m.keysList := by
  rw [contains_find?_iff, keysList_contains_iff]

-- theorem disjoint_keys_mapVal {α β γ μ} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} {f : α → γ → μ} :
--   a.disjoint_keys b → a.disjoint_keys (b.mapVal f)

-- theorem disjoint_keys_mapVal_both {α β γ μ η} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} {f : α → γ → μ} {g : α → β → η} :
--   a.disjoint_keys b → (a.mapVal g).disjoint_keys (b.mapVal f) := by
--   intros; solve_by_elim [disjoint_keys_mapVal, disjoint_keys_symm]

-- theorem keysList_EqExt {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) :
--   a.EqExt b → a.wf → b.wf → a.keysList.Perm b.keysList

/-
These are needed because ExprLow currently only checks equality and uniqueness against the map
-/

-- axiom filterId_wf {α} [DecidableEq α] (p : AssocList α α) : p.wf → p.filterId.wf

-- axiom filderId_Nodup {α} [DecidableEq α] (p : AssocList α α) : p.keysList.Nodup → p.filterId.keysList.Nodup

-- theorem filterId_EqExt {α} [DecidableEq α] (p : AssocList α α) := sorry

theorem mapVal_mapKey {α β γ σ} {f : α → γ} {g : β → σ} {m : AssocList α β}:
  (m.mapKey f).mapVal (λ _ => g) = (m.mapVal (λ _ => g)).mapKey f := by
    induction m <;> simpa

@[drcompute]
theorem mapKey_mapKey {α β γ σ} {f : α → β} {g : β → γ} {m : AssocList α σ}:
  (m.mapKey f).mapKey g = m.mapKey (λ k => g (f k)) := by
    induction m <;> simpa

@[drcompute]
theorem mapVal_mapVal {α β γ σ} {f : α → σ → β} {g : α → β → γ} {m : AssocList α σ}:
  (m.mapVal f).mapVal g = m.mapVal (λ k v => g k (f k v)) := by
    induction m <;> simpa

@[drcompute]
theorem mapKey_append {α β γ} {f : α → γ} {m n : AssocList α β}:
  m.mapKey f ++ n.mapKey f = (m ++ n).mapKey f := by
  induction m <;> simpa

theorem bijectivePortRenaming_id {α} [DecidableEq α] : @bijectivePortRenaming α _ ∅ = id := by rfl

theorem bijectivePortRenaming_invert {α} [DecidableEq α] {p : AssocList α α}:
  p.invertible →
  p.bijectivePortRenaming = fun i => ((p.filterId.append p.inverse.filterId).find? i).getD i := by
  unfold AssocList.bijectivePortRenaming; simp +contextual

@[simp] theorem in_eraseAll_list {α β} {Ta : α} {elem : (α × β)} [DecidableEq α] (a : AssocList α β):
  elem ∈ (AssocList.eraseAllP (fun k x => decide (k = Ta)) a).toList -> elem ∈ a.toList := by
  induction a with
  | nil => simp
  | cons k v xs ht =>
    dsimp; intro ha
    by_cases h' : decide (k = Ta)
    · simp at h'; subst k; simp at ha
      obtain ht := ht ha
      grind
    · have : decide (k = Ta) = false := by simp [*]
      rw [this] at ha; dsimp at ha
      grind

@[simp] theorem in_eraseAll_list' {α β} {Ta : α} {elem : (α × β)} [DecidableEq α] {a : AssocList α β}:
  elem ∈ (AssocList.eraseAll Ta a).toList -> elem ∈ a.toList := by
  unfold AssocList.eraseAll
  rw [eraseAllP_TR_eraseAll]
  apply in_eraseAll_list

theorem noDup_subset {α} {l1 l2 l2' : List α} : l2'.Nodup → l2' ⊆ l2 → (l1 ++ l2).Nodup → (l1 ++ l2').Nodup := by
  simp only [List.nodup_append]
  intro hp ha hb; simp [*]
  obtain ⟨_, _, _⟩ := hb
  grind

theorem eraseAll_Nodup' {α β} [DecidableEq α] {p : AssocList α β} {k} :
  p.toList.Nodup → (eraseAll k p).toList.Nodup := by
  induction p generalizing k with
  | nil => intros; simp [keysList]
  | cons k' v xs ih =>
    intro hnodup
    simp [keysList_cons] at hnodup
    by_cases heq : k' = k
    · grind [eraseAll_cons_eq]
    · rw [eraseAll_cons_neq] <;> try assumption
      simp [keysList_cons]
      and_intros
      · intro hin
        apply hnodup.left
        simp only [←keysList_contains_iff] at *
        apply in_eraseAll_list'; assumption
      · grind

theorem eraseAll_sublist {α β} [DecidableEq α] {k} {a : AssocList α β} :
  (eraseAll k a).toList.Sublist a.toList := by
  induction a with
  | nil => constructor
  | cons k' v xs ih =>
    by_cases heq : k' = k
    · subst k; rw [eraseAll_cons_eq]; constructor; assumption
    · rw [eraseAll_cons_neq] <;> simp [*]

private theorem of_append_right {α} {l₁ l₂ : List α} : List.Nodup (l₁ ++ l₂) → List.Nodup l₂ :=
  List.Nodup.sublist (List.sublist_append_right l₁ l₂)

theorem in_eraseAll_noDup {α β γ δ} {l : List ((α × β) × γ × δ)} (Ta : α) [DecidableEq α](a : AssocList α (β × γ × δ)):
  (List.map Prod.fst ( List.map Prod.fst (l ++ (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) a.toList)))).Nodup ->
  (List.map Prod.fst ( List.map Prod.fst (l ++ List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) (AssocList.eraseAllP (fun k x => decide (k = Ta)) a).toList))).Nodup := by
  simp at *; intro hnodup
  apply noDup_subset <;> try assumption
  · obtain hnodup := of_append_right hnodup
    apply List.Nodup.sublist <;> try assumption
    apply List.Sublist.map
    have hthis := eraseAll_sublist (k := Ta) (a := a)
    unfold eraseAll at hthis; rwa [eraseAllP_TR_eraseAll] at hthis
  · dsimp [· ⊆ ·, List.Subset]; intro a ha
    have h' := List.exists_of_mem_map ha
    obtain ⟨a', ha1, ha2⟩ := h'
    rw [← ha2]
    apply List.mem_map_of_mem
    apply in_eraseAll_list
    assumption

theorem eraseAll_comm {α β} [DecidableEq α] {a b : α} {m : AssocList α β}:
  (m.eraseAll a).eraseAll b = (m.eraseAll b).eraseAll a := by
  induction m with
  | nil => rfl
  | cons k v xs ih =>
    by_cases heq1 : k = a <;> by_cases heq2 : k = b <;> subst_vars
      <;> simp (disch := assumption) only [eraseAll_cons_eq, *, eraseAll_cons_neq]

theorem find?_append {α β} [DecidableEq α] {l1 l2 : AssocList α β} {k}:
  find? k (l1 ++ l2) = match find? k l1 with
  | some x => x
  | none => find? k l2 := by
    induction l1
    · simp [append]
    · rename_i k1 v1 l1 HR
      cases Heq: decide (k1 = k) <;> simp at Heq
      · rw [find?_cons_neq Heq, ←HR, cons_append, find?_cons_neq Heq]
      · simp [find?, Heq]

@[drcompute]
theorem filterId_cons_eq {α} [DecidableEq α] {a} {n : AssocList α α} :
  (n.cons a a).filterId = n.filterId := by simpa [filterId, filter]

private theorem filterId_cons {α β} [DecidableEq α] {f : α → β → Bool} {l l' : AssocList α β} {a b} :
  (l.cons a b).foldl (λ c a' b' => if f a' b' then c.concat a' b' else c) l'
  = l.foldl (λ c a' b' => if f a' b' then c.concat a' b' else c) (if f a b then l'.concat a b else l') := rfl

private theorem filterId_append {α β} [DecidableEq α] {f : α → β → Bool} {l l' l'' : AssocList α β} :
  l.foldl (λ c a' b' => if f a' b' then c.concat a' b' else c) (l' ++ l'')
  = l' ++ l.foldl (λ c a' b' => if f a' b' then c.concat a' b' else c) l'' := by
  induction l generalizing l' l'' with
  | nil => rfl
  | cons k v xs ih =>
    simp only [filterId_cons]; split <;> simp only [cons_concat_append2, ih]

@[drcompute]
theorem filterId_cons_neq {α} [DecidableEq α] {a b} {n : AssocList α α} (H : b ≠ a) :
  (n.cons a b).filterId = n.filterId.cons a b := by
  dsimp [filterId, filter]; rw [filterId_cons]
  simp only [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ite_not]
  rw [show (if a = b then nil else concat a b nil) = concat a b nil by simp [*, H.symm]]
  rw [show concat a b nil = concat a b nil ++ nil by rfl]
  have := @filterId_append _ _ _ (fun a b => a ≠ b) n (concat a b nil) nil
  simp only [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ite_not] at *
  rw [this]; rfl

@[drcompute]
theorem filterId_nil {α} [DecidableEq α] :
  (.nil : AssocList α α).filterId = .nil := by rfl

@[drcompute]
theorem inverse_cons {α β} {a b} {n : AssocList α β} :
  (n.cons a b).inverse = n.inverse.cons b a := by
  induction n generalizing a b <;> solve | rfl | simpa [inverse, H]

@[drcompute]
theorem inverse_nil {α β} :
  (.nil : AssocList α β).inverse = .nil := by rfl

@[drcompute]
theorem mapKey_cons {α β γ} {a b} {f : α → γ} {m : AssocList α β}:
  (m.cons a b).mapKey f = (m.mapKey f).cons (f a) b := rfl

@[drcompute]
theorem mapKey_nil {α β γ} {f : α → γ}:
  (@Batteries.AssocList.nil α β).mapKey f = .nil := rfl

@[drcompute]
theorem mapVal_cons {α β γ} {a b} {f : α → β → γ} {m : AssocList α β}:
  (m.cons a b).mapVal f = (m.mapVal f).cons a (f a b) := rfl

@[drcompute]
theorem mapVal_nil {α β γ} {f : α → β → γ}:
  (@Batteries.AssocList.nil α β).mapVal f = .nil := rfl

theorem mapVal_append {α β γ} {f : α → β → γ} {m1 m2 : AssocList α β}:
  m1.mapVal f ++ m2.mapVal f = (m1 ++ m2).mapVal f := by
  induction m1 <;> simp [mapVal_cons, *]

theorem list_inter_cons_nin {α} [DecidableEq α] {a : α} {x y : List α} :
  a ∉ y → (a :: x).inter y = x.inter y := by
  unfold List.inter; simp +contextual

theorem list_inter_cons_in {α} [DecidableEq α] {a : α} {x y : List α} :
  a ∈ y → (a :: x).inter y = a :: (x.inter y) := by
  unfold List.inter; simp +contextual

theorem list_inter_cons_nin2 {α} [DecidableEq α] {a : α} {x y : List α} :
  a ∉ x → x.inter (a :: y) = x.inter y := by
  unfold List.inter; simp +contextual
  intro h
  induction x with
  | nil => rfl
  | cons xa xs ih =>
    simp_all only [List.mem_cons, not_or, not_false_eq_true, forall_const]
    repeat rw [List.filter.eq_2]
    split
    · rename_i heq
      simp at heq; cases heq
      · grind
      · rw [show decide (xa ∈ y) = true by simp [*]]; simp [*]
    · simp_all

theorem list_inter_cons_in2 {α} [DecidableEq α] {a : α} {x y : List α} :
  a ∈ x → a ∈ x.inter (a :: y) := by
  unfold List.inter; simp

theorem invertible_cons {α} [DecidableEq α] {xs : AssocList α α} {a b} :
  (cons a b xs).invertible → xs.invertible := by
  unfold invertible; intro h
  by_cases heq : a = b
  · subst a; simp only [filterId_cons_eq, inverse_cons] at h
    simp only [List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at *
    obtain ⟨h1, h2, h3⟩ := h
    and_intros <;> simp_all [keysList]
  · simp only [List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at *
    obtain ⟨h1, h2, h3⟩ := h
    and_intros <;> try (simp_all [keysList, inverse]; done)
    have h : a ≠ b := heq
    simp (disch := symm_saturate; assumption) [filterId_cons_neq, inverse_cons] at *
    rw [keysList_cons] at *
    by_cases hc1 : a ∈ (cons b a xs.inverse.filterId).keysList
    · grind [list_inter_cons_in]
    · rw [list_inter_cons_nin] at h1 <;> try assumption
      rw [keysList_cons] at *
      by_cases hc1 : b ∈ xs.filterId.keysList
      · have := list_inter_cons_in2 (y := xs.inverse.filterId.keysList) hc1
        rw [h1] at this; contradiction
      · rw [list_inter_cons_nin2] at h1 <;> assumption

@[drcompute]
theorem bijectivePortRenaming_same {α} {β} [DecidableEq α] (f : β → α) (l : List β) :
  (List.map (λ i => (f i, f i)) l).toAssocList.bijectivePortRenaming = id := by
  induction l with
  | nil => rfl
  | cons a b ih =>
    ext j; dsimp [bijectivePortRenaming]
    split <;> try rfl
    simp only [filterId_cons_eq, inverse_cons]
    have := invertible_cons ‹_›
    unfold bijectivePortRenaming at ih
    rw (occs := [3]) [show j = id j by rfl]
    rw [←ih]; simp [this]

theorem filterId_correct_none {α} [DecidableEq α] {m : AssocList α α} {i} :
  m.find? i = none → m.filterId.find? i = none := by
  induction m with
  | nil => intros; rfl
  | cons k v xs ih =>
    intro h
    by_cases heq : k = i
    · subst i; rw [find?_cons_eq] at h; cases h
    · rw [find?_cons_neq] at h <;> try assumption
      by_cases heq' : v = k
      · subst k; rw [filterId_cons_eq]
        solve_by_elim
      · simp (disch := assumption) only [find?_cons_neq, filterId_cons_neq, ih]

theorem filterId_correct {α} [DecidableEq α] {m : AssocList α α} {i} :
  m.keysList.Nodup → m.find? i = some i → m.filterId.find? i = none := by
  induction m generalizing i with
  | nil => intros; rfl
  | cons k v xs ih =>
    intro hnodup h; by_cases heq : k = i
    · subst i
      rw [find?_cons_eq] at h; cases h
      rw [AssocList.filterId_cons_eq]
      simp only [keysList_cons, List.nodup_cons] at hnodup
      obtain ⟨hnin, hnodup⟩ := hnodup
      apply filterId_correct_none
      rw [←keysList_contains_iff] at hnin
      rw [contains_none]; assumption
    . rw [find?_cons_neq] at h <;> try assumption
      simp only [List.nodup_cons, keysList_cons] at hnodup
      cases hnodup
      by_cases heq' : k = v
      · subst k; rw [filterId_cons_eq]; solve_by_elim
      · have : k ≠ v := heq'; symm_saturate; rw [filterId_cons_neq, find?_cons_neq] <;> solve_by_elim

theorem filterId_correct2 {α} [DecidableEq α] {m : AssocList α α} {i v} :
  i ≠ v → m.find? i = some v → m.filterId.find? i = some v := by
  induction m generalizing i with
  | nil => grind [find?_nil]
  | cons k v' xs ih =>
    intro hne h; by_cases heq : k = i
    · subst i; rw [find?_cons_eq] at h; cases h
      rw [AssocList.filterId_cons_neq, find?_cons_eq]; symm; assumption
    . rw [find?_cons_neq] at h <;> try assumption
      by_cases heq' : v' = k
      · subst v'; rw [filterId_cons_eq]; solve_by_elim
      · rw [filterId_cons_neq, find?_cons_neq] <;> try assumption
        solve_by_elim

theorem filterId_correct3 {α} [DecidableEq α] {m : AssocList α α} {i y} :
  m.keysList.Nodup → m.filterId.find? i = some y → m.find? i = some y ∧ i ≠ y := by
  intro hnod hfilter
  cases hc : m.find? i
  · exfalso; have := filterId_correct_none hc; grind
  · rename_i y'
    by_cases heq : i = y'
    · subst y'
      have := filterId_correct ‹_› hc
      grind
    · have := filterId_correct2 ‹_› hc
      rw [this] at hfilter; cases hfilter; simp [*]

theorem inverse_find?_in {α β} [DecidableEq α] [DecidableEq β] {m : AssocList α β} {i v} :
  m.find? i = some v → v ∈ m.inverse.keysList := by
  induction m generalizing i v with
  | nil => grind [find?_nil]
  | cons k v' xs ih =>
    intro hfind
    by_cases heq : k = i
    · subst i; rw [find?_cons_eq] at hfind; cases hfind
      simp [inverse_cons, keysList_cons]
    · rw [find?_cons_neq] at hfind <;> try assumption
      simp only [inverse_cons, keysList_cons]; right
      apply ih; assumption

theorem inverse_correct {α β} [DecidableEq α] [DecidableEq β] {m : AssocList α β} {i v} :
  m.inverse.keysList.Nodup → m.find? i = some v → m.inverse.find? v = some i := by
  induction m generalizing i v with
  | nil => grind [find?_nil]
  | cons k v' xs ih =>
    simp only [inverse_cons, keysList_cons, List.nodup_cons]
    intro ⟨heql, hnodup⟩ hfind
    by_cases heq : k = i
    · subst i; rw [find?_cons_eq] at hfind; cases hfind; rw [find?_cons_eq]
    · rw [find?_cons_neq] at hfind <;> try assumption
      by_cases heq' : v' = v
      · grind [inverse_find?_in]
      · rw [find?_cons_neq] <;> solve_by_elim

theorem inverse_idempotent {α β} {m : AssocList α β} :
  m = m.inverse.inverse := by
  induction m <;> grind [inverse_cons, inverse_nil]

theorem inverse_correct2 {α β} [DecidableEq α] [DecidableEq β] {m : AssocList α β} {i v} :
  m.keysList.Nodup → m.inverse.find? i = some v → m.find? v = some i := by
  have hinv := inverse_correct (m := m.inverse) (i := i) (v := v)
  simp only [← inverse_idempotent] at *; assumption

theorem EqExt_contains {α β} [DecidableEq α] {m1 m2 : AssocList α β} {i} :
  m1.EqExt m2 → m1.contains i → m2.contains i := by
  intro heq hcont
  unfold EqExt at *
  rw [←contains_find?_iff] at hcont
  obtain ⟨x, hfind⟩ := hcont
  rw [heq] at hfind
  rw [←contains_find?_iff]; solve_by_elim

theorem beq_ooo_ext_1_l {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.EqExt b → a.beq_left_ooo b := by
  unfold beq_left_ooo EqExt
  intro heq
  simp only [List.all_eq_true, beq_iff_eq]; intro v hkey
  solve_by_elim

theorem beq_ooo_ext_1_r {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.EqExt b → b.beq_left_ooo a := by
  unfold beq_left_ooo EqExt
  intro heq
  simp only [List.all_eq_true, beq_iff_eq]; intro v hkey
  symm; solve_by_elim

theorem beq_ooo_ext_1 {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.EqExt b → a.beq_ooo b := by
  intro heq; unfold beq_ooo
  simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true]; solve_by_elim [beq_ooo_ext_1_l, beq_ooo_ext_1_r]

theorem beq_ooo_ext_2 {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.beq_ooo b → a.EqExt b := by
  unfold beq_ooo EqExt; intro hbeq i
  simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at hbeq
  obtain ⟨hl, hr⟩ := hbeq
  unfold beq_left_ooo at *; simp only [List.all_eq_true, beq_iff_eq] at *
  cases h1 : find? i a <;> cases h2 : find? i b <;> try rfl
  · specialize hr i (by apply keysList_find; rw [h2]; rfl); grind
  · specialize hl i (by apply keysList_find; rw [h1]; rfl); grind
  · specialize hr i (by apply keysList_find; rw [h2]; rfl); grind

theorem beq_ooo_ext  {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.EqExt b ↔ a.beq_ooo b := by solve_by_elim [beq_ooo_ext_1, beq_ooo_ext_2]

def DecidableEqExt {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) : Decidable (EqExt a b) :=
  if h : a.beq_ooo b
  then isTrue (beq_ooo_ext.mpr h)
  else isFalse (fun _ => by apply h; rw [← beq_ooo_ext]; assumption)

instance {α β} [DecidableEq α] [DecidableEq β] : DecidableRel (@EqExt α β _) := DecidableEqExt

theorem EqExt_nil {α β} [DecidableEq α] {p : AssocList α β} :
  nil.EqExt p → p = nil := by
  induction p with
  | nil => intros; rfl
  | cons k v xs ih =>
    intro h; exfalso
    dsimp [EqExt] at *
    specialize h k
    grind [find?_cons_eq]

theorem EqExt_cons1 {α β} [DecidableEq α] {p' xs : AssocList α β} {k v} :
  (cons k v xs).EqExt p' → p'.find? k = some v := by
  intro hcons
  unfold EqExt at *
  specialize hcons k; rw [find?_cons_eq] at hcons; symm; assumption

theorem EqExt_eraseAll {α β} [DecidableEq α] {p' p : AssocList α β} k :
  p.EqExt p' → (p.eraseAll k).EqExt (p'.eraseAll k) := by
  unfold EqExt; intro heq i
  by_cases h : i = k
  · subst_vars; simp only [find?_eraseAll_eq]
  · simp (disch := assumption) only [find?_eraseAll_neq, heq]

theorem EqExt_cons2 {α β} [DecidableEq α] {p' xs : AssocList α β} {k v} :
  (cons k v xs).EqExt p' → (xs.eraseAll k).EqExt (p'.eraseAll k) := by
  intro h
  rw [show eraseAll k xs = eraseAll k (cons k v xs) by rw [eraseAll_cons_eq]]
  apply EqExt_eraseAll; assumption

theorem inverse_keysList {α β} {p : AssocList α β} :
  p.inverse.keysList = p.valsList := by
  induction p with
  | nil => rfl
  | cons k v xs ih =>
    simp only [inverse_cons, keysList_cons, valsList_cons, ih]

theorem filterId_contains {α} [DecidableEq α] {p : AssocList α α} {x} :
  p.filterId.contains x → p.contains x := by
  induction p generalizing x with
  | nil => intros; contradiction
  | cons k v xs ih =>
    intro hcont
    by_cases heq : v = k
    · subst k; rw [filterId_cons_eq] at hcont
      by_cases heq' : v = x
      · subst x; simp
      · simp only [← contains_find?_isSome_iff] at *
        rw [find?_cons_neq] <;> solve_by_elim
    · rw [filterId_cons_neq] at hcont <;> try assumption
      by_cases heq : k = x
      · subst k; simp
      · simp only [← contains_find?_isSome_iff] at *
        simp (disch := assumption) only [find?_cons_neq] at *
        solve_by_elim

theorem filterId_Nodup {α} [DecidableEq α] {p : AssocList α α} :
  p.keysList.Nodup → p.filterId.keysList.Nodup := by
  induction p with
  | nil => intros; simp [filterId_nil, keysList]
  | cons k v xs ih =>
    simp only [keysList_cons]; simp; intro hkl hnodup
    by_cases heq : v = k
    · subst k; rw [filterId_cons_eq]; solve_by_elim
    · rw [filterId_cons_neq] <;> try assumption
      rw [keysList_cons]; simp; and_intros <;> try solve_by_elim
      simp only [← keysList_contains_iff] at *
      intro hcont; apply hkl; clear hkl
      solve_by_elim [filterId_contains]

theorem filterId_EqExt {α} [DecidableEq α] {p p' : AssocList α α} :
  p.EqExt p' → p.wf → p'.wf → p.filterId.EqExt p'.filterId := by
  unfold EqExt; intro heq hwf1 hwf2 k
  cases h : find? k p <;> (have h' := h; rw [heq] at h')
  · simp (disch := assumption) only [filterId_correct_none]
  · rename_i v
    by_cases heq : k = v
    · subst v
      unfold wf at *; simp (disch := assumption) only [filterId_correct]
    · simp (disch := assumption) only [filterId_correct2]

theorem EqExt_inverse {α β} [DecidableEq α] [DecidableEq β] {p p' : AssocList α β} :
  p.EqExt p' → p.wf → p'.wf → p.inverse.keysList.Nodup → p'.inverse.keysList.Nodup → p.inverse.EqExt p'.inverse := by
  unfold EqExt
  intro heq hwf1 hwf2 hwf3 hwf4 k
  cases h : find? k p.inverse <;> symm <;> cases h' : find? k p'.inverse <;> try rfl
  · have hcorr := inverse_correct2 ‹_› h'
    rw [←heq] at hcorr
    have hcorr' := inverse_correct ‹_› hcorr
    grind
  · have hcorr := inverse_correct2 ‹_› h
    rw [heq] at hcorr
    have hcorr' := inverse_correct ‹_› hcorr
    grind
  · have hcorr := inverse_correct2 ‹_› h
    rw [heq] at hcorr
    have hcorr' := inverse_correct ‹_› hcorr
    grind

theorem EqExt_append {α β} [DecidableEq α] {p1 p2 p1' p2' : AssocList α β} :
  p1.EqExt p1' →
  p2.EqExt p2' →
  (p1 ++ p2).EqExt (p1' ++ p2') := by
  unfold EqExt at *; intro h1 h2 k
  specialize h1 k; specialize h2 k
  cases h : find? k p1
  · cases h' : find? k p2
    all_goals
      repeat rw [append_find_right] <;> try assumption
      rwa [← h1]
  · repeat rw [append_find_left] <;> try assumption
    rwa [← h1]

theorem toList_erase_eraseAll {α β} [DecidableEq α] [DecidableEq β] {p : AssocList α β} {k v}:
  p.keysList.Nodup →
  p.find? k = .some v →
  p.toList.erase (k, v) = (p.eraseAll k).toList := by
  induction p generalizing k v with
  | nil => intros; rfl
  | cons k' v' xs ih =>
    intro hnodup hfind
    dsimp
    by_cases heq : k' = k
    · subst k'; rw [find?_cons_eq] at hfind; cases hfind;
      simp only [List.erase, BEq.rfl, eraseAll_cons_eq]
      rw [eraseAll_not_contains]
      intro hcont
      simp [keysList_cons] at hnodup
      apply hnodup.left
      rw [←keysList_contains_iff]; assumption
    · simp only [List.erase]
      have heq : ((k', v') == (k, v)) = false := by simp [*]
      rw [heq]; dsimp
      rw [eraseAll_cons_neq] <;> try assumption
      dsimp; congr
      apply ih
      · simp [keysList_cons] at hnodup; apply hnodup.right
      · rw [find?_cons_neq] at hfind <;> assumption

theorem eraseAll_Nodup {α β} [DecidableEq α] {p : AssocList α β} {k} :
  p.keysList.Nodup → (eraseAll k p).keysList.Nodup := by
  induction p generalizing k with
  | nil => intros; simp [keysList]
  | cons k' v xs ih =>
    intro hnodup
    simp [keysList_cons] at hnodup
    by_cases heq : k' = k
    · grind [eraseAll_cons_eq]
    · rw [eraseAll_cons_neq] <;> try assumption
      simp [keysList_cons]
      and_intros
      intro hin
      apply hnodup.left
      simp only [←keysList_contains_iff] at *
      apply contains_eraseAll; assumption
      grind

theorem find?_in_toList {α β} [DecidableEq α] {p : AssocList α β} {k v} :
  find? k p = some v → (k, v) ∈ p.toList := by
  induction p generalizing k v with
  | nil => simp
  | cons k' v' xs ih =>
    intro hfind
    by_cases h : k' = k
    · subst k'; rw [find?_cons_eq] at hfind; cases hfind; simp
    · rw [find?_cons_neq] at hfind <;> try assumption
      simp [h]; right
      solve_by_elim

theorem find?_in_toList2 {α β} [DecidableEq α] {p : AssocList α β} {k v} :
  p.keysList.Nodup → (k, v) ∈ p.toList → find? k p = some v := by
  induction p generalizing k v with
  | nil => simp
  | cons k' v' xs ih =>
    intro hnodup hkv
    dsimp at *; cases hkv
    · rw [find?_cons_eq]
    · simp only [keysList_cons, List.nodup_cons] at hnodup
      rename_i hin
      rcases hnodup with ⟨hk, hnodup⟩
      by_cases heq : k' = k
      · subst k; exfalso
        apply hk; unfold keysList
        simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right]
        solve_by_elim
      · rw [find?_cons_neq] <;> solve_by_elim

theorem find?_in_toList_iff {α β} [DecidableEq α] {p : AssocList α β} {k v} :
  p.keysList.Nodup → ((k, v) ∈ p.toList ↔ find? k p = some v) :=
  fun h => { mp := find?_in_toList2 h, mpr := find?_in_toList }

theorem EqExt_Perm {α β} [DecidableEq α] [DecidableEq β] {p p' : AssocList α β} :
  p.EqExt p' → p.wf → p'.wf → p.toList.Perm p'.toList := by
  induction p generalizing p' with
  | nil => intros; have h' := EqExt_nil ‹_›; subst_vars; trivial
  | cons k v xs ih =>
    intro heq hwf1 hwf2
    unfold EqExt wf at *; simp only [keysList_cons, List.nodup_cons] at hwf1
    obtain ⟨hwf1, hwf1'⟩ := hwf1
    simp only [toList]
    rw [List.cons_perm_iff_perm_erase]
    and_intros
    · specialize heq k; rw [find?_cons_eq] at heq; symm at heq
      apply find?_in_toList; assumption
    · rw [toList_erase_eraseAll] <;> try assumption
      · apply ih <;> try assumption
        · intro k'
          by_cases heqk : k' = k
          · subst k'; rw [find?_eraseAll_eq]
            rw [←keysList_contains_iff] at hwf1
            rw [←contains_find?_isSome_iff] at hwf1
            simp_all [-AssocList.find?_eq]
          · rw [find?_eraseAll_neq] <;> try assumption
            rw [←heq]; rw [find?_cons_neq]; symm; assumption
        · apply eraseAll_Nodup; assumption
      · rw [← heq]; rw [find?_cons_eq]

theorem valsList_Nodup {α β} [DecidableEq α] [DecidableEq β] {p p' : AssocList α β} :
  p.EqExt p' → p.wf → p'.wf → p.valsList.Nodup → p'.valsList.Nodup
 := by
  intro heq hwf1 hwf2 hvallist
  have hperm := EqExt_Perm heq hwf1 hwf2
  unfold valsList at *
  have hperm' := List.Perm.map (fun x => x.snd) hperm
  apply List.Nodup.perm <;> assumption

theorem EqExt_invertible {α} [DecidableEq α] {p p' : AssocList α α} :
  p.EqExt p' → p.wf → p'.wf → p.invertible → p'.invertible := by
  intro heq hwf1 hwf2 hinv
  unfold invertible at *; simp only [List.empty_eq, Bool.decide_and, Bool.and_eq_true,
    decide_eq_true_eq] at *
  obtain ⟨hinv1, hinv2, hinv3⟩ := hinv
  and_intros
  · simp [List.inter] at *
    intro k hk
    simp only [← keysList_contains_iff, ← contains_find?_iff] at *
    intro hcont
    obtain ⟨v1, hk⟩ := hk
    obtain ⟨v2, hcont⟩ := hcont
    unfold EqExt at *
    have hk' := hk
    have heq' := filterId_EqExt heq ‹_› ‹_›
    rw [←heq'] at hk'
    have hinv1' := hinv1 k ⟨_, hk'⟩
    apply hinv1'
    simp only [inverse_keysList] at *
    have hinv4 := valsList_Nodup heq hwf1 hwf2 hinv3
    simp only [←inverse_keysList] at *
    exists v2; rw [←hcont]
    apply filterId_EqExt <;> try assumption
    apply EqExt_inverse <;> assumption
  · assumption
  · simp only [inverse_keysList] at *
    apply valsList_Nodup <;> assumption

private theorem EqExt_invertible_iff' {α} [DecidableEq α] {p p' : AssocList α α} :
  p.EqExt p' → p.wf → p'.wf → (p.invertible ↔ p'.invertible) := by
  intro heq hwf1 hwf2
  constructor
  · intros; apply EqExt_invertible <;> assumption
  · replace heq := heq.symm
    intros; apply EqExt_invertible <;> assumption

theorem EqExt_invertible_iff {α} [DecidableEq α] {p p' : AssocList α α} :
  p.EqExt p' → p.wf → p'.wf → p.invertible = p'.invertible := by
    intro heq hwf1 hwf2
    cases h : p.invertible <;> symm
    · rw [← Bool.not_eq_true] at *
      intro h'; apply h
      replace heq := heq.symm; apply EqExt_invertible <;> assumption
    · apply EqExt_invertible <;> assumption

/- With the length argument this should be true, and we can easily check length in practice. -/
theorem bijectivePortRenaming_EqExt {α} [DecidableEq α] (p p' : AssocList α α) :
  p.EqExt p' → p.wf → p'.wf → bijectivePortRenaming p = bijectivePortRenaming p' := by
  intro heq hwf1 hwf2
  unfold bijectivePortRenaming
  rw [EqExt_invertible_iff heq] <;> try assumption
  cases h' : p'.invertible <;> dsimp
  ext i; congr 1
  apply EqExt_append
  · apply filterId_EqExt <;> try assumption
  · have h'' := h'
    have heq' := heq.symm
    rw [EqExt_invertible_iff (p := p') (p' := p)] at h'' <;> try assumption
    unfold invertible at *
    simp only [List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h' h''
    obtain ⟨h1, h2, h3⟩ := h'
    obtain ⟨h1', h2', h3'⟩ := h''
    apply filterId_EqExt <;> try assumption
    apply EqExt_inverse <;> assumption

theorem filterId_inverse_comm {α} [DecidableEq α] {p : AssocList α α} :
  p.filterId.inverse = p.inverse.filterId := by
  induction p with
  | nil => rfl
  | cons k v xs ih =>
    by_cases heq : v = k
    · subst k; simp only [filterId_cons_eq, inverse_cons]; assumption
    · have : v ≠ k := by assumption
      have := this.symm
      simp (disch := assumption) only [filterId_cons_neq, inverse_cons, *]

theorem invertibleMap {α} [DecidableEq α] {p : AssocList α α} {a b} :
  invertible p →
  (p.filterId ++ p.inverse.filterId).find? a = some b → (p.filterId ++ p.inverse.filterId).find? b = some a := by
  intro hinvertible
  unfold invertible at *
  simp only [List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinvertible
  obtain ⟨h1, h2, h3⟩ := hinvertible
  intro hfind
  cases h : p.filterId.find? a
  · rw [append_find_right] at hfind <;> try assumption
    obtain ⟨hl, hr⟩ := filterId_correct3 ‹_› hfind
    have h' := inverse_correct2 ‹_› hl
    have h'' := filterId_correct2 hr.symm h'
    rw [append_find_left]; assumption
  · rename_i v;
    rw [append_find_left h] at hfind
    cases hfind
    simp [List.inter] at h1
    have h := inverse_find?_in h
    simp only [filterId_inverse_comm] at *
    cases hc : p.filterId.find? b
    · rw [append_find_right] <;> try assumption
      rw [← filterId_inverse_comm]
      apply inverse_correct <;> try assumption
      rw [filterId_inverse_comm]
      solve_by_elim [filterId_Nodup]
    · exfalso; apply h1
      rotate_left 1; assumption
      rw [← keysList_contains_iff, ← contains_find?_iff]
      constructor; assumption

theorem bijectivePortRenaming_eq1 {α} [DecidableEq α] {p : AssocList α α} {a}:
  p.find? a = some a →
  AssocList.bijectivePortRenaming p a = a := by
  unfold AssocList.bijectivePortRenaming
  intro hf; split <;> try rfl
  rename_i hinv; unfold invertible at hinv; simp only [List.empty_eq, Bool.decide_and,
    Bool.and_eq_true, decide_eq_true_eq] at hinv; dsimp
  rcases hinv with ⟨ha, hb, hc⟩
  rw [append_find_right, filterId_correct]; rfl; assumption
  rwa [inverse_correct]; assumption
  rwa [filterId_correct]; assumption

theorem bijectivePortRenaming_eq2 {α} [DecidableEq α] {p : AssocList α α} {a}:
  p.find? a = none →
  p.inverse.find? a = none →
  AssocList.bijectivePortRenaming p a = a := by
  unfold AssocList.bijectivePortRenaming
  intro hf hf'; split <;> try rfl
  rename_i hinv; unfold invertible at hinv; simp only [List.empty_eq, Bool.decide_and,
    Bool.and_eq_true, decide_eq_true_eq] at hinv; dsimp
  rcases hinv with ⟨ha, hb, hc⟩
  rw [append_find_right, filterId_correct_none]; rfl; assumption
  rwa [filterId_correct_none]

theorem bijectivePortRenaming_eq3 {α} [DecidableEq α] {p : AssocList α α} {a b}:
  p.invertible →
  p.find? a = some b →
  AssocList.bijectivePortRenaming p a = b := by
  intro inv hfind
  by_cases heq : a = b
  · subst b; solve_by_elim [bijectivePortRenaming_eq1]
  · rw [bijectivePortRenaming_invert] <;> try assumption
    dsimp; rw [append_find_left]; rfl
    rwa [filterId_correct2]; assumption

theorem bijectivePortRenaming_eq4 {α} [DecidableEq α] {p : AssocList α α} {a b}:
  p.invertible →
  p.find? a = some b →
  AssocList.bijectivePortRenaming p b = a := by
  intro inv hfind
  by_cases heq : a = b
  · subst b; solve_by_elim [bijectivePortRenaming_eq1]
  · rw [bijectivePortRenaming_invert] <;> try assumption
    dsimp; rw [invertibleMap]; rfl; assumption
    rw [append_find_left]; rwa [filterId_correct2]; assumption

theorem bijectivePortRenaming_eq5 {α} [DecidableEq α] {p : AssocList α α} {a}:
  ¬ p.invertible →
  AssocList.bijectivePortRenaming p a = a := by
  intro hinv
  simp only [Bool.not_eq_true] at hinv
  unfold bijectivePortRenaming; rw [hinv]; rfl

theorem contains_append {α β} [DecidableEq α] {m1 m2 : AssocList α β} {i} :
  (m1 ++ m2).contains i = (m1.contains i || m2.contains i) := by
  cases h : (m1 ++ m2).contains i <;> symm
  · simp only [← Bool.not_eq_true] at *
    intro hcont; apply h; clear h
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Prod.exists,
      exists_and_right, exists_eq_right] at hcont
    rcases hcont with hcont | hcont
    · simp only [← contains_find?_iff] at *
      obtain ⟨v, hfind⟩ := hcont
      exists v; rw [append_find_left]; assumption
    · cases h' : m1.contains i
      · simp only [← Bool.not_eq_true] at *
        simp only [← contains_find?_isSome_iff] at h'
        simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h'
        simp only [← contains_find?_iff] at *
        obtain ⟨v, hfind⟩ := hcont; exists v
        rw [append_find_right] <;> assumption
      · simp only [← contains_find?_iff] at *
        obtain ⟨v, hfind⟩ := h'
        exists v; rw [append_find_left]; assumption
  · simp only [Bool.or_eq_true]
    simp only [← contains_find?_iff] at *
    obtain ⟨v, hfind⟩ := h
    have := append_find?2 hfind
    rcases this with h | h
    · left; solve_by_elim
    · right; exists v; apply h.right

theorem contains_mapval {α β γ} [DecidableEq α] {f : α → β → γ} {m : AssocList α β} {i} : (m.mapVal f).contains i = m.contains i := by
  cases h : (m.mapVal f).contains i <;> symm
  · simp only [← Bool.not_eq_true] at *; intro hcont; apply h; clear h
    rw [←contains_find?_iff] at *
    obtain ⟨v, hfind⟩ := hcont
    exists (f i v)
    simp [find?_mapVal, hfind, -find?_eq]
  · rw [←contains_find?_iff] at *
    obtain ⟨v, hfind⟩ := h
    rw [find?_mapVal, Option.map_eq_some] at hfind
    obtain ⟨v', hfind, heq⟩ := hfind
    subst v; solve_by_elim

theorem contains_eraseAll3 {α β} [DecidableEq α] {m : AssocList α β} {i j} :
  i ≠ j → contains i m → contains i (eraseAll j m) := by
  intro hne hcont
  simp only [← contains_find?_iff] at *
  obtain ⟨x, hfind⟩ := hcont
  exists x; rw [find?_eraseAll_neq] <;> assumption

theorem contains_eraseAll2 {α β} [DecidableEq α] {m : AssocList α β} {i j} :
  (j ≠ i && AssocList.contains i m) = AssocList.contains i (AssocList.eraseAll j m) := by
  by_cases h : j = i
  · subst j; have hnocont := eraseAll_not_contains2 m i
    simp [-AssocList.find?_eq, -AssocList.contains_eq, *]
  · cases hc : contains i (eraseAll j m)
    · simp only [← Bool.not_eq_true] at *
      intro hdec; apply hc; clear hc
      simp [-contains_eq] at *
      obtain ⟨_, hdec⟩ := hdec
      apply contains_eraseAll3 <;> (solve | assumption | symm; assumption)
    · simp [-contains_eq]; and_intros; grind
      exact contains_eraseAll hc

theorem disjoint_keys_find_some {α β γ} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} {i x} :
  a.disjoint_keys b →
  a.find? i = some x →
  b.find? i = none := by
  unfold disjoint_keys; intro hdisj hfind
  simp only [List.inter, List.elem_eq_contains, List.contains_eq_mem, List.filter_eq_nil_iff,
    decide_eq_true_eq] at *
  have fsome : (find? i a).isSome := by rewrite [hfind]; rfl
  rw [contains_find?_isSome_iff, keysList_contains_iff] at fsome
  replace hdisj := hdisj _ fsome
  rw [←keysList_contains_iff, ←contains_find?_isSome_iff] at hdisj
  simp_all [-find?_eq]

@[simp] theorem eraseAllP_false {α β} (l : AssocList α β) :
    AssocList.eraseAllP (λ _ _ => false) l = l := by
      induction l; rfl; simpa

theorem eraseAll_eraseAllP {α β} [DecidableEq α] (P : α → β → Bool) (x : α) (l : AssocList α β) :
    (l.eraseAllP P).eraseAll x = l.eraseAllP (λ k v => k == x || P k v) := by
    induction l with
    | nil => rfl
    | cons k v tl HR =>
      cases Pkv: P k v
      <;> simp only [eraseAllP, Pkv, cond_false, Bool.or_false, Bool.or_true]
      · cases keqx: decide (k = x)
        · rw [decide_eq_false_iff_not] at keqx
          have heq : (k == x) = false := by simpa only [beq_eq_false_iff_ne, ne_eq]
          simpa only [
            ne_eq, keqx, not_false_eq_true, AssocList.eraseAll_cons_neq, HR,
            heq, cond_false
          ]
        · rw [decide_eq_true_eq] at keqx; subst k
          simpa only [AssocList.eraseAll_cons_eq, HR, BEq.rfl, cond_true]
      · exact HR

-- This statement could be made stronger by having not ∀v, P k v = false but
-- ∀ (_, v) ∈ a
theorem find?_eraseAllP_false {α β} [DecidableEq α] (a : AssocList α β) (k : α) (P : α → β → Bool)
  (Hv : ∀ v, P k v = false) :
  (a.eraseAllP P).find? k = a.find? k :=
  by
    induction a with
    | nil => rfl
    | cons k' v tl HR =>
      rw [AssocList.eraseAllP_cons]
      cases keqk' : decide (k = k')
      · have Hneq : k' ≠ k := by
          simp at keqk'; simp; intro H; subst k; apply keqk'; rfl
        rw [AssocList.find?_cons_neq Hneq]
        cases HPk' : P k' v
        <;> dsimp
        · rw [AssocList.find?_cons_neq Hneq]
          exact HR
        · exact HR
      · simp at keqk'; subst k'; simp [Hv]

end Batteries.AssocList
