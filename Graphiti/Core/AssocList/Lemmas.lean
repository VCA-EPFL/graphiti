/-
Copyright (c) 2024, 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.AssocList.Basic
public import Graphiti.Core.Simp

@[expose] public section

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
  simp [concat, append_assoc]

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
  have hk : (cons a y t).keysList = a :: t.keysList := rfl
  simp_all [disjoint_keys, List.inter, hk, List.filter_eq_nil_iff]

theorem disjoint_keys_symm {α β γ} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} :
  a.disjoint_keys b → b.disjoint_keys a := by
  grind [disjoint_keys, List.inter, List.filter_eq_nil_iff]

theorem append_find_left {α β} [DecidableEq α] {a b : AssocList α β} {i x} :
  a.find? i = some x →
  (a ++ b).find? i = some x := by
  simp_all [append_eq, List.find?_append]

theorem append_find_right {α β} [DecidableEq α] (a b : AssocList α β) {i} :
  a.find? i = none →
  (a ++ b).find? i = b.find? i := by
  intro h; rw [find?_eq, Option.map_eq_none_iff] at h; simp [append_eq, List.find?_append, h]

theorem map_keys_list {α β γ} [DecidableEq α] {ident} {l : AssocList α β} {f : α → β → γ} :
    (l.mapVal f).find? ident = (l.find? ident).map (f ident) := find?_mapVal

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
  simp only [contains_eq, find?_eq]; grind

theorem find?_eq_contains {α β} [DecidableEq α] {x y : AssocList α β} {k} :
  (∀ i, x.contains i → x.find? i = y.find? i) →
  (∀ i, y.contains i → x.find? i = y.find? i) →
  x.find? k = y.find? k := by
  grind [contains_none]

theorem find?_map_neq {α β γ} [DecidableEq β] k (f : α → β) (g : α → γ) {l : List α}
  (Hneq: ∀ x, x ∈ l → f x ≠ k):
  AssocList.find? k (List.map (λ x => ⟨f x, g x⟩) l).toAssocList = none := by
      simpa [contains_none, Hneq]

theorem contains_some {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    m.contains ident →
    (m.find? ident).isSome := by
  simp +contextual

theorem contains_some2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (m.find? ident).isSome →
    m.contains ident := by
  simp +contextual

theorem contains_some3 {α β} [DecidableEq α] {m : AssocList α β} {ident x} :
    m.find? ident = some x →
    m.contains ident := by
  intro h; apply contains_some2; rw [h]; rfl

theorem contains_find?_iff {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (∃ x, m.find? ident = some x) ↔ m.contains ident := by
  rw [← Option.isSome_iff_exists]; constructor <;> simp +contextual

theorem contains_find?_isSome_iff {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (m.find? ident).isSome ↔ m.contains ident := by
  rw [Option.isSome_iff_exists]; apply contains_find?_iff

theorem contains_find?_none_iff {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    m.find? ident = none ↔ m.contains ident = false := by
  rw [← Bool.not_eq_true, ← contains_find?_isSome_iff, Option.not_isSome_iff_eq_none]

theorem keysList_find {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  (m.find? ident).isSome → ident ∈ m.keysList := by simp_all [keysList]

theorem keysList_find' {α β} [BEq α] [LawfulBEq α] {m : AssocList α β} {ident} :
  (m.find? ident).isSome → ident ∈ m.keysList := by simp_all [keysList]

theorem keysList_find2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ident ∈ m.keysList → (m.find? ident).isSome := by simp_all [keysList]

theorem notkeysList_find2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ident ∉ m.keysList → m.find? ident = none := by
  intro h; cases hf : m.find? ident <;> grind [keysList_find]

theorem keysList_cons {α β} {xs : AssocList α β} {k v} :
  (cons k v xs).keysList = k :: xs.keysList := by rfl

theorem valsList_cons {α β} {xs : AssocList α β} {k v} :
  (cons k v xs).valsList = v :: xs.valsList := by rfl

theorem append_find_right_disjoint {α β} [DecidableEq α] {a b : AssocList α β} {i x} :
  a.disjoint_keys b →
  b.find? i = some x →
  (a ++ b).find? i = some x := by
  simp only [disjoint_keys, List.inter, decide_eq_true_eq, List.filter_eq_nil_iff, List.elem_eq_mem]
  intro hd hf
  grind [append_find_right, notkeysList_find2, keysList_find, Option.isSome_iff_exists]

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
    | cons k v tl ih => by_cases h : p k v <;> simp [ih, h]

@[simp] theorem eraseAllP_map_comm {α β γ} [DecidableEq α] {a : AssocList α β} {p : α → Bool} {f : α → β → γ} :
  (a.eraseAllP (λ k _ => p k)).mapVal f = (a.mapVal f).eraseAllP (λ k _ => p k) := by
  induction a with
  | nil => rfl
  | cons k v xs ih => by_cases h : p k <;> simp [*]

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
  | cons k v xs ih => by_cases h : k = ident <;> simp_all [mapVal, -find?_eq]

@[simp] theorem find?_eraseAll_eq {α β} [DecidableEq α] (a : AssocList α β) i :
  (a.eraseAll i).find? i = none := by
  induction a with
  | nil => rfl
  | cons k v xs ih => by_cases h : k = i <;> simp_all [eraseAll_cons_neq, -find?_eq]

@[simp] theorem find?_eraseAll_list {α β} { T : α} [DecidableEq α] (a : AssocList α β):
  List.find? (fun x => x.1 == T) (AssocList.eraseAllP (fun k x => decide (k = T)) a).toList = none := by
  rw [←Batteries.AssocList.findEntry?_eq, ←Option.map_eq_none_iff, ←Batteries.AssocList.find?_eq_findEntry?]
  have := find?_eraseAll_eq a T; unfold eraseAll at *; rw [eraseAllP_TR_eraseAll] at *; assumption

@[simp] theorem find?_eraseAll_neq {α β} [DecidableEq α] {a : AssocList α β} {i i'} :
  i ≠ i' → (a.eraseAll i').find? i = a.find? i := by
  intro neq
  induction a with
  | nil => rfl
  | cons k v xs ih =>
    by_cases h1 : k = i' <;> by_cases h2 : k = i <;>
      grind [eraseAll_cons_eq, eraseAll_cons_neq, find?_cons_eq, find?_cons_neq]

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
  simp only [← contains_find?_iff]; grind [find?_eraseAll]

theorem eraseAll_not_contains {α β} [DecidableEq α] (a : AssocList α β) (i : α) :
  ¬a.contains i → a.eraseAll i = a := by
    intros H
    induction a <;> simp_all [eraseAll, eraseAllP_TR_eraseAll]

theorem eraseAll_not_contains2 {α β} [DecidableEq α] (a : AssocList α β) (i : α) :
  ¬ (a.eraseAll i).contains i := by
  rw [← contains_find?_iff]; intro ⟨x, h⟩
  rw [find?_eraseAll_eq] at h; contradiction

@[simp, drcompute] theorem eraseAll_map_neq {α β γ} [DecidableEq α] [DecidableEq β]
    (f : α → β) (g : α → γ) (l : List α) (k : β) (Hneq : ∀ x, f x ≠ k) :
    (List.map (λ x => (f x, g x)) l).toAssocList.eraseAll k =
    (List.map (λ x => (f x, g x)) l).toAssocList := by
  apply eraseAll_not_contains; simp [Hneq]

@[drcompute]
theorem eraseAll_append {α β} [DecidableEq α] {l1 l2 : AssocList α β} {i}:
  AssocList.eraseAll i (l1 ++ l2) =
  AssocList.eraseAll i l1 ++ AssocList.eraseAll i l2 := by
  induction l1 with
  | nil => rfl
  | cons k v xs ih => by_cases h : k = i <;> simp_all [eraseAll_cons_neq]

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
  simp [keysList]

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
  | cons k v xs ih => by_cases h : k = Ta <;> simp_all <;> grind

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

theorem eraseAll_sublist {α β} [DecidableEq α] {k} {a : AssocList α β} :
  (eraseAll k a).toList.Sublist a.toList := by
  induction a with
  | nil => simp
  | cons k' v xs ih => by_cases heq : k' = k <;> simp_all [eraseAll_cons_neq]

theorem eraseAll_Nodup' {α β} [DecidableEq α] {p : AssocList α β} {k} :
  p.toList.Nodup → (eraseAll k p).toList.Nodup := by
  grind [eraseAll_sublist, List.Nodup.sublist]

theorem in_eraseAll_noDup {α β γ δ} {l : List ((α × β) × γ × δ)} (Ta : α) [DecidableEq α](a : AssocList α (β × γ × δ)):
  (List.map Prod.fst ( List.map Prod.fst (l ++ (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) a.toList)))).Nodup ->
  (List.map Prod.fst ( List.map Prod.fst (l ++ List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) (AssocList.eraseAllP (fun k x => decide (k = Ta)) a).toList))).Nodup := by
  intro h
  have := eraseAll_sublist (k := Ta) (a := a)
  unfold eraseAll at this; rw [eraseAllP_TR_eraseAll] at this
  refine List.Nodup.sublist ?_ h
  grind [List.Sublist.map, List.Sublist.append_left]

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
  induction l1 with
  | nil => simp [append]
  | cons k1 v1 l1 HR => by_cases h : k1 = k <;> simp_all

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
  (n.cons a b).inverse = n.inverse.cons b a := rfl

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
  intro h; unfold List.inter; apply List.filter_congr; grind

theorem list_inter_cons_in2 {α} [DecidableEq α] {a : α} {x y : List α} :
  a ∈ x → a ∈ x.inter (a :: y) := by
  unfold List.inter; simp

theorem invertible_cons {α} [DecidableEq α] {xs : AssocList α α} {a b} :
  (cons a b xs).invertible → xs.invertible := by
  simp only [invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, List.inter, List.filter_eq_nil_iff, List.elem_eq_mem]
  by_cases heq : b = a
  · subst heq; simp_all [filterId_cons_eq, inverse_cons, keysList_cons]
  · have := Ne.symm heq; simp_all [filterId_cons_neq, inverse_cons, keysList_cons]

@[drcompute]
theorem bijectivePortRenaming_same {α} {β} [DecidableEq α] (f : β → α) (l : List β) :
  (List.map (λ i => (f i, f i)) l).toAssocList.bijectivePortRenaming = id := by
  have h1 : ((List.map (λ i => (f i, f i)) l).toAssocList).filterId = .nil := by
    induction l <;> simp_all [filterId_cons_eq, filterId_nil, List.toAssocList]
  have h2 : ((List.map (λ i => (f i, f i)) l).toAssocList).inverse = (List.map (λ i => (f i, f i)) l).toAssocList := by
    clear h1; induction l <;> simp_all [inverse_cons, inverse_nil, List.toAssocList]
  ext j; simp [bijectivePortRenaming, h1, h2]

theorem filterId_correct_none {α} [DecidableEq α] {m : AssocList α α} {i} :
  m.find? i = none → m.filterId.find? i = none := by
  induction m with
  | nil => simp [filterId_nil, -find?_eq]
  | cons k v xs ih =>
    by_cases hk : k = i <;> by_cases hv : v = k <;>
      simp_all [filterId_cons_eq, filterId_cons_neq, -find?_eq]

theorem filterId_correct {α} [DecidableEq α] {m : AssocList α α} {i} :
  m.keysList.Nodup → m.find? i = some i → m.filterId.find? i = none := by
  induction m with
  | nil => simp
  | cons k v xs ih =>
    by_cases hk : k = i <;> by_cases hv : v = k <;>
      simp_all [filterId_cons_eq, filterId_cons_neq, keysList_cons, filterId_correct_none, notkeysList_find2, -find?_eq]

theorem filterId_correct2 {α} [DecidableEq α] {m : AssocList α α} {i v} :
  i ≠ v → m.find? i = some v → m.filterId.find? i = some v := by
  intro hne
  induction m with
  | nil => simp
  | cons k v' xs ih =>
    by_cases hk : k = i <;> by_cases hv : v' = k <;>
      simp_all [filterId_cons_eq, filterId_cons_neq, Ne.symm hne, -find?_eq]

theorem filterId_correct3 {α} [DecidableEq α] {m : AssocList α α} {i y} :
  m.keysList.Nodup → m.filterId.find? i = some y → m.find? i = some y ∧ i ≠ y := by
  intro hnod hf; cases hc : m.find? i <;> grind [filterId_correct_none, filterId_correct, filterId_correct2]

theorem inverse_find?_in {α β} [DecidableEq α] [DecidableEq β] {m : AssocList α β} {i v} :
  m.find? i = some v → v ∈ m.inverse.keysList := by
  induction m generalizing i v <;> grind [inverse_cons, keysList_cons, find?_cons_eq, find?_cons_neq, find?_nil]

theorem inverse_correct {α β} [DecidableEq α] [DecidableEq β] {m : AssocList α β} {i v} :
  m.inverse.keysList.Nodup → m.find? i = some v → m.inverse.find? v = some i := by
  induction m generalizing i v with
  | nil => simp
  | cons k v' xs ih =>
    simp only [inverse_cons, keysList_cons, List.nodup_cons]
    by_cases hk : k = i <;> by_cases hv : v' = v <;> grind [inverse_find?_in, find?_cons_eq, find?_cons_neq]

theorem inverse_idempotent {α β} {m : AssocList α β} :
  m = m.inverse.inverse := by
  induction m <;> grind [inverse_cons, inverse_nil]

theorem inverse_correct2 {α β} [DecidableEq α] [DecidableEq β] {m : AssocList α β} {i v} :
  m.keysList.Nodup → m.inverse.find? i = some v → m.find? v = some i := by
  simpa only [← inverse_idempotent] using inverse_correct (m := m.inverse) (i := i) (v := v)

theorem EqExt_contains {α β} [DecidableEq α] {m1 m2 : AssocList α β} {i} :
  m1.EqExt m2 → m1.contains i → m2.contains i := by
  intro heq; simp only [← contains_find?_isSome_iff, heq i, imp_self]

theorem beq_ooo_ext_1_l {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.EqExt b → a.beq_left_ooo b := by
  simp_all [beq_left_ooo, EqExt]

theorem beq_ooo_ext_1_r {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.EqExt b → b.beq_left_ooo a := by
  simp_all [beq_left_ooo, EqExt]

theorem beq_ooo_ext_1 {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.EqExt b → a.beq_ooo b := by
  simp +contextual [beq_ooo, beq_ooo_ext_1_l, beq_ooo_ext_1_r]

theorem beq_ooo_ext_2 {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.beq_ooo b → a.EqExt b := by
  simp only [beq_ooo, beq_left_ooo, EqExt, decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  intro ⟨hl, hr⟩ i
  cases h1 : find? i a <;> cases h2 : find? i b <;> grind [keysList_find]

theorem beq_ooo_ext  {α β} [DecidableEq α] [DecidableEq β] {a b : AssocList α β} :
  a.EqExt b ↔ a.beq_ooo b := ⟨beq_ooo_ext_1, beq_ooo_ext_2⟩

def DecidableEqExt {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) : Decidable (EqExt a b) :=
  if h : a.beq_ooo b
  then isTrue (beq_ooo_ext.mpr h)
  else isFalse (fun _ => by apply h; rw [← beq_ooo_ext]; assumption)

instance {α β} [DecidableEq α] [DecidableEq β] : DecidableRel (@EqExt α β _) := DecidableEqExt

theorem EqExt_nil {α β} [DecidableEq α] {p : AssocList α β} :
  nil.EqExt p → p = nil := by
  cases p with
  | nil => simp
  | cons k v xs => intro h; simpa [-find?_eq] using h k

theorem EqExt_cons1 {α β} [DecidableEq α] {p' xs : AssocList α β} {k v} :
  (cons k v xs).EqExt p' → p'.find? k = some v := by
  intro h; simpa using (h k).symm

theorem EqExt_eraseAll {α β} [DecidableEq α] {p' p : AssocList α β} k :
  p.EqExt p' → (p.eraseAll k).EqExt (p'.eraseAll k) := by
  intro heq i; by_cases h : i = k <;> simp_all [EqExt, -find?_eq]

theorem EqExt_cons2 {α β} [DecidableEq α] {p' xs : AssocList α β} {k v} :
  (cons k v xs).EqExt p' → (xs.eraseAll k).EqExt (p'.eraseAll k) := by
  intro h; simpa using EqExt_eraseAll k h

theorem inverse_keysList {α β} {p : AssocList α β} :
  p.inverse.keysList = p.valsList := by
  induction p <;> simp_all [inverse_cons, keysList_cons, valsList_cons, inverse_nil, keysList, valsList]

theorem filterId_contains {α} [DecidableEq α] {p : AssocList α α} {x} :
  p.filterId.contains x → p.contains x := by
  intro h; rw [← contains_find?_isSome_iff] at *; cases hf : p.find? x <;> simp_all [filterId_correct_none, -find?_eq]

theorem filterId_Nodup {α} [DecidableEq α] {p : AssocList α α} :
  p.keysList.Nodup → p.filterId.keysList.Nodup := by
  induction p with
  | nil => simp [filterId_nil, keysList]
  | cons k v xs ih =>
    by_cases h : v = k <;> simp_all [filterId_cons_eq, filterId_cons_neq, keysList_cons, ← keysList_contains_iff, -contains_eq] <;>
      grind [filterId_contains]

theorem filterId_EqExt {α} [DecidableEq α] {p p' : AssocList α α} :
  p.EqExt p' → p.wf → p'.wf → p.filterId.EqExt p'.filterId := by
  unfold EqExt wf; intro heq hwf1 hwf2 k
  cases h : p.find? k with
  | none => grind [filterId_correct_none]
  | some v => by_cases hkv : k = v <;> grind [filterId_correct, filterId_correct2]

theorem EqExt_inverse {α β} [DecidableEq α] [DecidableEq β] {p p' : AssocList α β} :
  p.EqExt p' → p.wf → p'.wf → p.inverse.keysList.Nodup → p'.inverse.keysList.Nodup → p.inverse.EqExt p'.inverse := by
  unfold EqExt wf
  intro heq hwf1 hwf2 hwf3 hwf4 k
  cases h : find? k p.inverse <;> cases h' : find? k p'.inverse <;> grind [inverse_correct, inverse_correct2]

theorem EqExt_append {α β} [DecidableEq α] {p1 p2 p1' p2' : AssocList α β} :
  p1.EqExt p1' →
  p2.EqExt p2' →
  (p1 ++ p2).EqExt (p1' ++ p2') := by
  intro h1 h2 k; simp only [find?_append, h1 k, h2 k]

theorem toList_erase_eraseAll {α β} [DecidableEq α] [DecidableEq β] {p : AssocList α β} {k v}:
  p.keysList.Nodup →
  p.find? k = .some v →
  p.toList.erase (k, v) = (p.eraseAll k).toList := by
  induction p generalizing k v with
  | nil => simp
  | cons k' v' xs ih =>
    by_cases heq : k' = k
    · subst heq; simp_all [keysList_cons, eraseAll_not_contains, keysList_contains_iff, -find?_eq, -contains_eq]
    · simp_all [keysList_cons, eraseAll_cons_neq, List.erase_cons, -find?_eq, -contains_eq]

theorem eraseAll_Nodup {α β} [DecidableEq α] {p : AssocList α β} {k} :
  p.keysList.Nodup → (eraseAll k p).keysList.Nodup := by
  simp only [keysList]; grind [eraseAll_sublist, List.Sublist.map, List.Nodup.sublist]

theorem find?_in_toList {α β} [DecidableEq α] {p : AssocList α β} {k v} :
  find? k p = some v → (k, v) ∈ p.toList := by
  simp +contextual [List.find?_eq_some_iff_append]

theorem find?_in_toList2 {α β} [DecidableEq α] {p : AssocList α β} {k v} :
  p.keysList.Nodup → (k, v) ∈ p.toList → find? k p = some v := by
  induction p generalizing k v with
  | nil => simp
  | cons k' v' xs ih =>
    by_cases heq : k' = k <;> simp_all [keysList_cons, -find?_eq] <;> grind [keysList, List.mem_map_of_mem]

theorem find?_in_toList_iff {α β} [DecidableEq α] {p : AssocList α β} {k v} :
  p.keysList.Nodup → ((k, v) ∈ p.toList ↔ find? k p = some v) :=
  fun h => { mp := find?_in_toList2 h, mpr := find?_in_toList }

theorem EqExt_Perm {α β} [DecidableEq α] [DecidableEq β] {p p' : AssocList α β} :
  p.EqExt p' → p.wf → p'.wf → p.toList.Perm p'.toList := by
  intro heq hwf1 hwf2
  have n1 : p.toList.Nodup := List.Pairwise.of_map Prod.fst (fun _ _ h h' => h (congrArg _ h')) hwf1
  have n2 : p'.toList.Nodup := List.Pairwise.of_map Prod.fst (fun _ _ h h' => h (congrArg _ h')) hwf2
  rw [List.perm_ext_iff_of_nodup n1 n2]
  intro ⟨k, v⟩
  rw [find?_in_toList_iff hwf1, find?_in_toList_iff hwf2, heq]

theorem valsList_Nodup {α β} [DecidableEq α] [DecidableEq β] {p p' : AssocList α β} :
  p.EqExt p' → p.wf → p'.wf → p.valsList.Nodup → p'.valsList.Nodup
 := by
  intro heq hwf1 hwf2; simp only [valsList]; grind [List.Perm.nodup_iff, List.Perm.map, EqExt_Perm]

private theorem EqExt_mem_keysList {α β} [DecidableEq α] {a b : AssocList α β} {k} :
  a.EqExt b → (k ∈ a.keysList ↔ k ∈ b.keysList) := by
  intro h; rw [← keysList_find?_isSome_iff, ← keysList_find?_isSome_iff, h k]

theorem EqExt_invertible {α} [DecidableEq α] {p p' : AssocList α α} :
  p.EqExt p' → p.wf → p'.wf → p.invertible → p'.invertible := by
  intro heq hwf1 hwf2 hinv
  unfold wf at *
  simp only [invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, List.inter,
    List.filter_eq_nil_iff, List.elem_eq_mem] at *
  obtain ⟨h1, h2, h3⟩ := hinv
  have hv : p'.inverse.keysList.Nodup := by
    simpa [inverse_keysList] using valsList_Nodup heq hwf1 hwf2 (by simpa [inverse_keysList] using h3)
  have hf := filterId_EqExt heq hwf1 hwf2
  have hi := filterId_EqExt (EqExt_inverse heq hwf1 hwf2 h3 hv) h3 hv
  grind [EqExt_mem_keysList]

theorem EqExt_invertible_iff {α} [DecidableEq α] {p p' : AssocList α α} :
  p.EqExt p' → p.wf → p'.wf → p.invertible = p'.invertible := by
  intro heq hwf1 hwf2
  rw [Bool.eq_iff_iff]; grind [EqExt_invertible, EqExt.symm]

/- With the length argument this should be true, and we can easily check length in practice. -/
private theorem append_eq_hAppend {α β} (a b : AssocList α β) : a.append b = a ++ b := rfl

theorem bijectivePortRenaming_EqExt {α} [DecidableEq α] (p p' : AssocList α α) :
  p.EqExt p' → p.wf → p'.wf → bijectivePortRenaming p = bijectivePortRenaming p' := by
  intro heq hwf1 hwf2
  funext i
  simp only [bijectivePortRenaming, EqExt_invertible_iff heq hwf1 hwf2]
  by_cases h : p'.invertible
  · have h' := EqExt_invertible heq.symm hwf2 hwf1 h
    simp only [invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h h'
    simp only [h, append_eq_hAppend, EqExt_append (filterId_EqExt heq hwf1 hwf2)
      (filterId_EqExt (EqExt_inverse heq hwf1 hwf2 h'.2.2 h.2.2) h'.2.2 h.2.2) i]
  · simp [h]

theorem filterId_inverse_comm {α} [DecidableEq α] {p : AssocList α α} :
  p.filterId.inverse = p.inverse.filterId := by
  induction p with
  | nil => rfl
  | cons k v xs ih => by_cases heq : v = k <;> simp_all [filterId_cons_eq, filterId_cons_neq, inverse_cons, eq_comm]

theorem invertibleMap {α} [DecidableEq α] {p : AssocList α α} {a b} :
  invertible p →
  (p.filterId ++ p.inverse.filterId).find? a = some b → (p.filterId ++ p.inverse.filterId).find? b = some a := by
  simp only [invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, List.inter,
    List.filter_eq_nil_iff, List.elem_eq_mem]
  intro ⟨h1, h2, h3⟩ hfind
  have := filterId_Nodup h3
  cases h : p.filterId.find? a with
  | none => grind [append_find_left, append_find_right, filterId_correct3, inverse_correct2, filterId_correct2]
  | some v =>
    have := inverse_find?_in h
    grind [append_find_left, append_find_right, notkeysList_find2, filterId_inverse_comm, inverse_correct]

theorem bijectivePortRenaming_eq1 {α} [DecidableEq α] {p : AssocList α α} {a}:
  p.find? a = some a →
  AssocList.bijectivePortRenaming p a = a := by
  simp only [bijectivePortRenaming, append_eq_hAppend, invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true,
    decide_eq_true_eq]
  intro hf; split <;> grind [append_find_right, filterId_correct, inverse_correct, Option.getD_none]

theorem bijectivePortRenaming_eq2 {α} [DecidableEq α] {p : AssocList α α} {a}:
  p.find? a = none →
  p.inverse.find? a = none →
  AssocList.bijectivePortRenaming p a = a := by
  intro hf hf'
  simp only [bijectivePortRenaming, append_eq_hAppend, append_find_right _ _ (filterId_correct_none hf),
    filterId_correct_none hf', Option.getD_none, ite_self]

theorem bijectivePortRenaming_eq3 {α} [DecidableEq α] {p : AssocList α α} {a b}:
  p.invertible →
  p.find? a = some b →
  AssocList.bijectivePortRenaming p a = b := by
  intro inv hfind
  by_cases heq : a = b
  · subst heq; grind [bijectivePortRenaming_eq1]
  · simp only [bijectivePortRenaming_invert inv, append_eq_hAppend, append_find_left (filterId_correct2 heq hfind),
      Option.getD_some]

theorem bijectivePortRenaming_eq4 {α} [DecidableEq α] {p : AssocList α α} {a b}:
  p.invertible →
  p.find? a = some b →
  AssocList.bijectivePortRenaming p b = a := by
  intro inv hfind
  by_cases heq : a = b
  · subst heq; grind [bijectivePortRenaming_eq1]
  · simp only [bijectivePortRenaming_invert inv, append_eq_hAppend,
      invertibleMap inv (append_find_left (filterId_correct2 heq hfind)), Option.getD_some]

theorem bijectivePortRenaming_eq5 {α} [DecidableEq α] {p : AssocList α α} {a}:
  ¬ p.invertible →
  AssocList.bijectivePortRenaming p a = a := by
  intro hinv
  simp only [Bool.not_eq_true] at hinv
  unfold bijectivePortRenaming; rw [hinv]; rfl

theorem contains_append {α β} [DecidableEq α] {m1 m2 : AssocList α β} {i} :
  (m1 ++ m2).contains i = (m1.contains i || m2.contains i) := by
  simp [append_eq]

theorem contains_mapval {α β γ} [DecidableEq α] {f : α → β → γ} {m : AssocList α β} {i} : (m.mapVal f).contains i = m.contains i := by
  simp [toList_mapVal, Function.comp_def]

theorem contains_eraseAll3 {α β} [DecidableEq α] {m : AssocList α β} {i j} :
  i ≠ j → contains i m → contains i (eraseAll j m) := by
  intro hne; simp only [← contains_find?_isSome_iff, find?_eraseAll_neq hne]; simp

theorem contains_eraseAll2 {α β} [DecidableEq α] {m : AssocList α β} {i j} :
  (j ≠ i && AssocList.contains i m) = AssocList.contains i (AssocList.eraseAll j m) := by
  by_cases h : j = i
  · subst h; simp [eraseAll_not_contains2, -contains_eq]
  · cases h1 : contains i m <;> cases h2 : contains i (eraseAll j m) <;> grind [contains_eraseAll, contains_eraseAll3]

theorem disjoint_keys_find_some {α β γ} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} {i x} :
  a.disjoint_keys b →
  a.find? i = some x →
  b.find? i = none := by
  simp only [disjoint_keys, List.inter, decide_eq_true_eq, List.filter_eq_nil_iff, List.elem_eq_mem]
  grind [notkeysList_find2, keysList_find, Option.isSome_iff_exists]

@[simp] theorem eraseAllP_false {α β} (l : AssocList α β) :
    AssocList.eraseAllP (λ _ _ => false) l = l := by
      induction l; rfl; simpa

theorem eraseAll_eraseAllP {α β} [DecidableEq α] (P : α → β → Bool) (x : α) (l : AssocList α β) :
    (l.eraseAllP P).eraseAll x = l.eraseAllP (λ k v => k == x || P k v) := by
  induction l with
  | nil => rfl
  | cons k v tl HR => by_cases h : k = x <;> cases hp : P k v <;> simp_all [eraseAll_cons_neq]

-- This statement could be made stronger by having not ∀v, P k v = false but
-- ∀ (_, v) ∈ a
theorem find?_eraseAllP_false {α β} [DecidableEq α] (a : AssocList α β) (k : α) (P : α → β → Bool)
  (Hv : ∀ v, P k v = false) :
  (a.eraseAllP P).find? k = a.find? k := by
  induction a with
  | nil => rfl
  | cons k' v tl HR => by_cases h : k' = k <;> cases hp : P k' v <;> simp_all

end Batteries.AssocList
