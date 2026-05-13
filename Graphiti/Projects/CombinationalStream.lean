/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Simp
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.AssocList.Basic
import Graphiti.Core.Netlist.VerilogExport

open Batteries (AssocList)

namespace Graphiti.CombModule

namespace List
variable {α : Type _} {β : Type _}

theorem zipWith_take {γ : Type _} (l₁ : List α) (l₂ : List β) (n₁ n₂ : ℕ) (f : α → β → γ)
  : List.zipWith f (l₁.take n₁) (l₂.take n₂) = List.take (min n₁ n₂) (List.zipWith f l₁ l₂)
  := by
  rw [List.ext_getElem_iff]
  split_ands
  . grind only [= List.length_zipWith, = List.length_take]
  . intro i h₁ h₂
    simp only [List.getElem_zipWith, List.getElem_take]

lemma zip_take (l₁ : List α) (l₂ : List β) (n₁ n₂ : ℕ)
  : List.zip (l₁.take n₁) (l₂.take n₂) = List.take (min n₁ n₂) (l₁.zip l₂)
  := by unfold List.zip; apply zipWith_take

def filter_window [BEq α] (delay: Nat) (a : List α): List Bool :=
  -- I'd use a List.finRange if it had enough theorems on it but
  -- I'm not good enough with that kind of type manipulation to do it quickly
  (List.range a.length).map
    (fun i => i >= delay ∧ ((a.take (i + 1)).drop (i + 1 - delay)).all (fun v => some v == a[i]?))

theorem length_filter_window [BEq α] (delay : Nat) (a : List α) :
    (filter_window delay a).length = a.length := by
      simp [List.length_range, filter_window]

theorem filter_window_nil [BEq α] (delay : Nat) :
    filter_window delay ([] : List α) = [] := by
      rfl

theorem filter_window_get [BEq α] (delay : Nat) (a : List α) (i : Nat)
    (hi : i < a.length) :
    (filter_window delay a)[i]'(by rw [length_filter_window]; assumption) = (Bool.and (i >= delay) (((a.take (i + 1)).drop (i + 1 - delay)).all
      (fun v => some v == a[i]?))) := by
        unfold filter_window; grind;

theorem filter_window_get_prefix [BEq α] (delay : Nat) (s1 s2 : List α)
    (h : s1 <+: s2) (i : Nat) (hi : i < s1.length) :
    (filter_window delay s1)[i]'(by rw [length_filter_window]; assumption) = (filter_window delay s2)[i]'(by rw [length_filter_window]; apply List.IsPrefix.length_le at h; omega) := by
      obtain ⟨t, ht⟩ := h;
      conv => enter [2, 1]; rw [← ht]
      rw [ filter_window_get, filter_window_get ];
      · rw [ List.take_append_of_le_length ];
        · grind;
        · grind;
      · grind;
      · exact hi

theorem filter_window_prefix [BEq α] :
    ∀ delay : Nat, ∀ s1 s2 : List α,
    s1 <+: s2 →
    (filter_window delay s1) <+: (filter_window delay s2) := by
      intros delay s1 s2 hs1s2
      have h_filter_eq_take : filter_window delay s1 = (filter_window delay s2).take s1.length := by
        refine' List.ext_get _ _;
        · rw [ List.length_take, length_filter_window, length_filter_window ];
          rw [ Nat.min_eq_left ( hs1s2.length_le ) ];
        · intro n hn hn';
          convert filter_window_get_prefix delay s1 s2 hs1s2 n _;
          · grind;
          · grind;
      exact h_filter_eq_take ▸ List.take_prefix _ _

theorem filter_window_take [BEq α] (l : List α) (delay i : ℕ)
  : (filter_window delay (List.take i l)) = List.take i (filter_window delay l)
  := by
  rw [List.ext_getElem_iff]
  split_ands
  . simp only [List.length_take, List.length_filter_window]
  . intro i' h₁ h₂
    rw [List.getElem_take]
    apply filter_window_get_prefix
    . apply List.take_prefix
    . rw [List.length_take, List.length_filter_window] at h₂
      rw [List.length_take]
      assumption

def strict_prefix (s1 s2 : List α) : Prop :=
  s1.length < s2.length ∧ s1 = s2.take s1.length

infix:50 " <<: " => strict_prefix

theorem strict_prefix_is_prefix (s1 s2 : List α)
  : s1 <<: s2 → s1 <+: s2
  := by
  intro H
  obtain ⟨_, H⟩ := H
  rw [H]
  apply List.take_prefix

theorem strict_prefix_iff_prefix_neq (s1 s2 : List α)
  : s1 <<: s2 ↔ (s1 <+: s2 ∧ ¬s1 = s2)
  := by
  apply Iff.intro
  . intro H
    apply And.intro
    . apply strict_prefix_is_prefix
      exact H
    . intro Heq
      unfold strict_prefix at H
      grind
  . intro H
    obtain ⟨Hp, Hneq⟩ := H
    unfold strict_prefix
    apply And.intro
    . apply Nat.lt_of_le_of_ne
      . apply List.IsPrefix.length_le
        exact Hp
      . intro Heq
        apply Hneq
        apply List.IsPrefix.eq_of_length
        <;> assumption
    . apply List.prefix_iff_eq_take.mp
      exact Hp

lemma strict_prefix_iff_prefix_length (s1 s2 : List α)
  : s1 <<: s2 ↔ (s1 <+: s2 ∧ s1.length < s2.length)
  := by
  apply Iff.trans
  . apply strict_prefix_iff_prefix_neq
  . apply Iff.intro
    . intro H
      obtain ⟨Hp, Hneq⟩ := H
      apply And.intro
      . assumption
      . apply Nat.lt_of_le_of_ne
        . apply List.IsPrefix.length_le Hp
        . intro Heq
          apply Hneq
          apply List.IsPrefix.eq_of_length
          <;> assumption
    . intro H
      obtain ⟨Hp, Hneq⟩ := H
      apply And.intro
      . assumption
      . intro H
        have Heq : s1.length = s2.length := by rw [H]
        grind

def filter_window3 [BEq α] (delay: Nat) (a b c : List α) : List Bool :=
  List.zipWith Bool.and (filter_window delay a) (List.zipWith Bool.and (filter_window delay b) (filter_window delay c))

theorem length_filter_window3 [BEq α] :
  ∀ d, ∀ a b c : List α,
    List.length (filter_window3 d a b c) = min a.length (min b.length c.length)
  := by
    intros
    unfold filter_window3
    grind only [List.length_zipWith, List.length_filter_window]

lemma zipWith_prefix.{u, v, w} {α : Type u} {β : Type v} {γ : Type w} :
  ∀f: α → β → γ, ∀ a a': List α, ∀ b b' : List β,
  a <+: a' → b <+: b' → List.zipWith f a b <+: List.zipWith f a' b'
  := by
  intros f a a' b b' Ha Hb
  revert a' b b'
  induction a with
  | nil => simp
  | cons hd tl iH =>
    intro a' b b' Ha Hb
    rw [List.cons_prefix_iff] at Ha
    obtain ⟨tl', Ha', Ha⟩ := Ha
    subst_vars
    unfold List.zipWith
    cases b
    . simp
    . rename_i bHd bTl
      rw [List.cons_prefix_iff] at Hb
      obtain ⟨btl', Hb', Hb⟩ := Hb
      simp
      grind

lemma zipWith_strict_prefix.{u, v, w} {α : Type u} {β : Type v} {γ : Type w} :
  ∀f: α → β → γ, ∀ a a': List α, ∀ b : List β,
  a <<: a' → a.length < b.length → List.zipWith f a b <<: List.zipWith f a' b
  := by
  intros f a a' b H Hlen
  apply (strict_prefix_iff_prefix_neq (List.zipWith f a b) (List.zipWith f a' b)).mpr
  apply And.intro
  . apply zipWith_prefix
    apply strict_prefix_is_prefix
    assumption
    apply List.prefix_rfl
  . intro Hzip
    obtain ⟨H, Hneq⟩ := (strict_prefix_iff_prefix_length a a').mp H
    have H : (List.zipWith f a b).length = (List.zipWith f a' b).length := by rw [Hzip]
    rw [List.length_zipWith, List.length_zipWith] at H
    grind

theorem filter_window3_prefix_1 [BEq α] :
  ∀ delay: Nat, ∀a a' b c : List α,
  filter_window delay a <+: filter_window delay a' →
  filter_window3 delay a b c <+: filter_window3 delay a' b c
  := by
  intros delay a a' b c H
  unfold filter_window3
  generalize (List.zipWith Bool.and (filter_window delay b) (filter_window delay c)) = v
  apply zipWith_prefix
  assumption
  apply List.prefix_rfl

def is_filtered_prefix (filter : List Bool) (s1 s2 : List α) : Prop :=
  s1.length <= s2.length ∧ s2.length <= filter.length ∧
  (∀ i : Nat, i < s1.length → filter[i]? = some true → s1[i]? = s2[i]?)

-- Notations are weird :(
notation s1 " <+:{" filter "}" s2:max => is_filtered_prefix filter s1 s2

def is_filtered_strict_prefix (filter : List Bool) (s1 s2 : List α) : Prop :=
  s1.length < s2.length ∧ s2.length <= filter.length ∧
  (∀ i : Nat, i < s1.length → filter[i]? = some true → s1[i]? = s2[i]?)

notation s1 " <<:{" filter "}" s2:max => is_filtered_strict_prefix filter s1 s2

theorem filter_prefix_filtered_prefix :
  ∀ f1 f2, ∀ s1 s2 : List α,
  is_filtered_prefix f1 s1 s2 →
  f1 <+: f2 →
  is_filtered_prefix f2 s1 s2
  := by
  intro f1 f2 s1 s2
  unfold is_filtered_prefix
  intros H Hprefix
  obtain ⟨Hslen, Hfslen, Hfsubs⟩ := H
  and_intros
  . assumption
  . grind
  . intro i Hi Hf
    apply Hfsubs
    . assumption
    . rw [List.getElem?_eq_getElem] at Hf
      rotate_left
      next => grind

      rw [List.getElem?_eq_getElem]
      rotate_left
      next => grind

      simp at Hf
      simp
      rw [← Hf, List.IsPrefix.getElem]
      assumption

theorem filter_prefix_filtered_strict_prefix :
  ∀ f1 f2, ∀ s1 s2 : List α,
    s1 <<:{f1} s2 →
    f1 <+: f2 →
    s1 <<:{f2} s2
  := by
  intro f1 f2 s1 s2
  unfold is_filtered_strict_prefix
  intros H Hprefix
  obtain ⟨Hslen, Hfslen, Hfsubs⟩ := H
  and_intros
  . assumption
  . grind
  . intro i Hi Hf
    apply Hfsubs
    . assumption
    . rw [List.getElem?_eq_getElem] at Hf
      rotate_left
      next => grind

      rw [List.getElem?_eq_getElem]
      rotate_left
      next => grind

      rw [← Hf, List.IsPrefix.getElem]
      assumption

def filtered_eq (filter : List Bool) (s1 s2 : List α) : Prop :=
  s1.length = s2.length ∧ filter.length = s1.length ∧
      (∀ i : Nat, filter[i]? = some true → s1[i]? = s2[i]?)

def select_from_filter (lt lf : List α) (filter : List Bool) : List α :=
  List.zipWith (fun v p => if v then p.1 else p.2) filter (List.zip lt lf)

def pad_with_list (target : Nat) (pad l : List α) : List α :=
  l ++ ((pad.drop l.length).take (target - l.length))

theorem length_pad_with_list : ∀ t, ∀ p l : List α, p.length >= t → (pad_with_list t p l).length = max t l.length
  := by
    unfold pad_with_list
    grind only [= List.length_append, = max_def, = List.length_take, = List.length_drop, = min_def]

theorem filtered_eq_select_from_filter :
  ∀ f, ∀ lt lf : List α, f.length = lt.length → lf.length >= lt.length → filtered_eq f lt (select_from_filter lt lf f)
    := by
      intros f lt lf Hfl Hll
      unfold select_from_filter
      split_ands
      . rw [List.length_zipWith, List.length_zip]
        omega
      . assumption
      . intros i Hf
        rw [List.getElem?_eq_some_iff] at Hf
        obtain ⟨Hi, Hf⟩ := Hf
        rw [(getElem?_pos _ _ (by omega))]
        rw [(getElem?_pos _ _ (by rw [List.length_zipWith, List.length_zip]; omega))]
        grind only [= List.getElem_zipWith, = List.getElem_zip]


lemma pad_with_list_eq_of_prefix (pad l : List α) (h : l <+: pad) :
    pad_with_list pad.length pad l = pad := by
      obtain ⟨ k, hk ⟩ := h;
      simp +decide [ hk.symm, pad_with_list ]

/-
`select_from_filter` is a prefix of `pad` when carry agrees with pad at
    all filter-true positions.
-/
lemma select_from_filter_prefix_of_agree
    (carry pad : List α) (filter : List Bool)
    (h : ∀ (i : Nat) (hi_f : i < filter.length) (hi_c : i < carry.length)
           (hi_p : i < pad.length),
           filter[i] = true → carry[i] = pad[i]) :
    select_from_filter carry pad filter <+: pad := by
      unfold select_from_filter
      revert carry pad
      induction filter with
      | nil =>
        intros carry pad h
        exact ⟨ pad, by simp +decide ⟩;
      | cons f fs ih =>
        intros carry pad h
        -- Sloowwww
        rcases carry with ( _ | ⟨ c, carry ⟩ ) <;> rcases pad with ( _ | ⟨ p, pad ⟩ ) <;> simp_all +decide;
        -- The first three "by grind" should be simpler but this works.
        exact ⟨ fun hf => h 0 (by grind) (by grind) (by grind) hf, ih _ _ fun i hi_f hi_c hi_p hi => h ( i + 1 ) ( by grind ) ( by grind ) ( by grind ) hi ⟩

def delay (d: α) (s: List α) := d :: s
def delayN (n: Nat) (d: α) (s: List α) := (List.replicate n d) ++ s

/-- Stateful scan: like scanl but drops the initial element, so the output
    has the same length as the input. Each output element depends on the
    previous state and the current input. -/
def scanl_drop (f : β → α → β) (init : β) (l : List α) : List β :=
  (l.scanl f init).drop 1

theorem length_scanl_drop (f : β → α → β) (init : β) (l : List α) :
    (scanl_drop f init l).length = l.length := by
  unfold scanl_drop; simp [List.length_drop, List.length_scanl]

theorem scanl_drop_prefix (f : β → α → β) (init : β) (l l' : List α) :
    l <+: l' → scanl_drop f init l <+: scanl_drop f init l' := by
  intro h
  unfold scanl_drop
  obtain ⟨t, ht⟩ := h; subst ht
  rw [List.scanl_append]
  simp only [List.drop_one, ne_eq, List.scanl_ne_nil, not_false_eq_true, List.tail_append_of_ne_nil,
    List.prefix_append]

theorem scanl_drop_nil (f : β → α → β) (init : β) :
    scanl_drop f init [] = [] := by
  unfold scanl_drop; simp

theorem scanl_drop_cons (f : β → α → β) (init : β) (a : α) (l : List α) :
    scanl_drop f init (a :: l) = f init a :: scanl_drop f (f init a) l := by
  unfold scanl_drop
  simp [List.scanl_cons, List.drop_cons]
  rw [←@List.cons_head_tail _ (List.scanl f (f init a) l)  (by apply List.scanl_ne_nil)]
  rw [List.head_scanl, List.tail_cons]

theorem scanl_drop_getElem (f : β → α → β) (init : β) (l : List α)
    (i : Nat) (hi : i < (scanl_drop f init l).length) :
    (scanl_drop f init l)[i] = (List.take (i + 1) l).foldl f init := by
  unfold scanl_drop
  simp only [List.getElem_drop, List.length_scanl] at *
  -- Kinda silly but whatever
  conv => enter [1, 2]; rw [Nat.add_comm]
  rw [List.getElem_scanl]

def not (s : List Bool) : List Bool := s.map Bool.not
def and (s1 s2 : List Bool) : List Bool := List.zipWith Bool.and s1 s2
def or (s1 s2 : List Bool) : List Bool := List.zipWith Bool.or s1 s2
def xor (s1 s2 : List Bool) : List Bool := List.zipWith Bool.xor s1 s2
def nand (s1 s2 : List Bool) : List Bool := not <| and s1 s2

def and3 (s1 s2 s3 : List Bool) : List Bool := List.zipWith Bool.and s1 (List.zipWith Bool.and s2 s3)
def xor3 (s1 s2 s3 : List Bool) : List Bool := List.zipWith Bool.xor s1 (List.zipWith Bool.xor s2 s3)
def nand3 (s1 s2 s3 : List Bool) : List Bool := not <| and3 s1 s2 s3

theorem not_prefix (l₁ l₁': List Bool) (h : l₁ <+: l₁')
  : not l₁ <+: not l₁' := List.IsPrefix.map _ h

theorem nand_prefix (l₁ l₁' l₂ l₂' : List Bool)
  : l₁ <+: l₁' → l₂ <+: l₂' → (nand l₁ l₂) <+: (nand l₁' l₂')
  := by
  intro h1 h2
  unfold nand
  apply not_prefix
  apply zipWith_prefix
  <;> assumption

theorem zip_prefix {γ : Type _} (l₁ l₁' : List α) (l₂ l₂' : List γ) :
    l₁ <+: l₁' → l₂ <+: l₂' → List.zip l₁ l₂ <+: List.zip l₁' l₂' := by
  intro h₁ h₂
  obtain ⟨t₁, ht₁⟩ := h₁; obtain ⟨t₂, ht₂⟩ := h₂; subst ht₁ ht₂
  induction l₁ generalizing l₂ t₂ with
  | nil => simp only [List.zip_nil_left, List.nil_append, List.nil_prefix]
  | cons hd₁ tl₁ iH =>
    obtain _ | ⟨hd₂, tl₂⟩ := l₂
    . simp only [List.zip_nil_right, List.cons_append, List.nil_prefix]
    . rw [List.cons_append, List.cons_append, List.zip_cons_cons, List.zip_cons_cons]
      rw [List.prefix_cons_inj]
      apply iH

theorem dropLast_both_prefix (l l' : List α) :
    l <+: l' → l.dropLast <+: l'.dropLast := by
  intro h
  obtain ⟨t, ht⟩ := h; subst ht
  simp only [List.dropLast_append, List.isEmpty_iff]
  cases t <;> dsimp
  . exact List.prefix_rfl
  . apply List.IsPrefix.trans
    . apply List.dropLast_prefix
    . apply List.prefix_append

end List

-- We thought we needed a top and bot value for streams, essentially operating on 4-valued logic.  However, we do not
-- need a top-value, because we don't have to signal any errors when two streams do not agree.  Instead, we block the
-- execution of the module if the streams do not agree.
-- For the same reason, we also do not need a bot value, because if we cannot define the result at some point, then we
-- can also block.
-- Also, I think we need integers instead of natural numbers for the domain, so that you have all the future and the
-- past values that you will ever get.  If you end up caring only about the past values, then maybe you can use naturals
-- again.

-- We are adding back a bot value (none) because it makes it easier to keep track of the most recent value that was
-- generated.
abbrev D := List Bool

open List
open VerilogExport

abbrev Named (s : String) (T : Type _) := T

def not_m : NatModule D :=
  { inputs := [(0, ⟨ D, λ s tt s' => s <<: tt ∧ s' = tt ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ not (delay false s) = tt⟩)].toAssocList
    init_state := λ s => s = default
  }

def not_m_template : VerilogTemplate where
  module := build_local_module "not_m" (simple_interface ["in1"] ["out1"]) "assign #1 out1 = ~ in1;"
  instantiation name inst := format_instantiation "not_m" name inst

def sink_m : NatModule Unit :=
  { inputs := [(0, ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    outputs := ∅
    init_state := λ s => s = default
  }

def sink_m_template : VerilogTemplate where
  module := build_local_module "sink_m" (simple_interface ["in1"] []) ""
  instantiation name inst := format_instantiation "sink_m" name inst

def nand_m (s : String) : NatModule (Named s (D × D)) :=
  { inputs := [(0, ⟨ Named s!"{s}.in1" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ Named s!"{s}.in2" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ Named s!"{s}.out1" D, λ s tt s' => s = s' ∧ tt = delay false (nand s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def nand_m_template : VerilogTemplate where
  module := build_local_module "nand_m" (simple_interface ["in1", "in2"] ["out1"]) "assign #1 out1 = ~ (in1 & in2);"
  instantiation name inst := format_instantiation "nand_m" name inst

def nand3_m : NatModule (D × D × D) :=
  { inputs := [(0, ⟨ D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ D, λ s tt s' => s.2.1 <<: tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
               (2, ⟨ D, λ s tt s' => s.2.2 <<: tt ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (nand3 s.1 s.2.1 s.2.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def nand3_m_template : VerilogTemplate where
  module := build_local_module "nand3_m" (simple_interface ["in1", "in2", "in3"] ["out1"]) "assign #1 out1 = ~ (in1 & in2 & in3);"
  instantiation name inst := format_instantiation "nand3_m" name inst

def and_m : NatModule (D × D) :=
  { inputs := [(0, ⟨ D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (nand s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def and_m_template : VerilogTemplate where
  module := build_local_module "and_m" (simple_interface ["in1", "in2"] ["out1"]) "assign #1 out1 = in1 & in2;"
  instantiation name inst := format_instantiation "and_m" name inst

def fork_m (s : String) : NatModule (Named s D) :=
  { inputs := [(0, ⟨ Named s!"{s}.in1" D, λ s tt s' => s <<: tt ∧ s' = tt ⟩)].toAssocList,
    outputs := [(0, ⟨ Named s!"{s}.out1" D, λ s tt s' => s = s' ∧ tt = s ⟩), (1, ⟨ Named s!"{s}.out2" D, λ s tt s' => s = s' ∧ tt = s ⟩)].toAssocList
    init_state := λ s => s = default
  }

def fork_m_template : VerilogTemplate where
  module := build_local_module "fork_m" (simple_interface ["in1"] ["out1", "out2"]) "assign out1 = in1;\nassign out2 = in1;"
  instantiation name inst := format_instantiation "fork_m" name inst

def fork3_m : NatModule D :=
  { inputs := [(0, ⟨ D, λ s tt s' => s <<: tt ∧ s' = tt ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩), (1, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩), (2, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩)].toAssocList
    init_state := λ s => s = default
  }

def fork3_m_template : VerilogTemplate where
  module := build_local_module "fork3_m" (simple_interface ["in1"] ["out1", "out2", "out3"]) "assign out1 = in1;\nassign out2 = in1;\nassign out3 = in1;"
  instantiation name inst := format_instantiation "fork3_m" name inst

def not_sm := not_m.stringify
def sink_sm := sink_m.stringify
def and_sm := and_m.stringify
def nand_sm (s : String := "") := (nand_m s).stringify
def nand3_sm := nand3_m.stringify
def fork_sm (s : String := "") := (fork_m s).stringify
def fork3_sm := fork3_m.stringify

def env : IdentMap String VerilogTemplate :=
  [("sink_m", sink_m_template), ("and_m", and_m_template), ("nand_m", nand_m_template), ("nand3_m", nand3_m_template), ("fork_m", fork_m_template), ("fork3_m", fork3_m_template), ("not_m", not_m_template)].toAssocList

namespace FlipFlop

def d_latch'_m := [graphEnv|
    d [type="io"];
    clk [type="io"];
    q [type="io"];
    q_bar [type="io"];

    n1 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n2 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n3 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n4 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];

    d_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    clk_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n3_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n4_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];

    not1 [type="not_m", typeImp=$(⟨_, not_sm⟩)];

    d -> d_2 [to="in1"];
    d_2 -> n1 [from="out1",to="in1"];
    d_2 -> not1 [from="out2",to="in1"];

    clk -> clk_2 [to="in1"];
    clk_2 -> n1 [from="out1",to="in2"];
    clk_2 -> n2 [from="out2",to="in2"];

    not1 -> n2 [from="out1",to="in1"];

    n1 -> n3 [from="out1",to="in1"];
    n2 -> n4 [from="out1",to="in2"];

    n3 -> n3_2 [from="out1",to="in1"];

    n4 -> n4_2 [from="out1",to="in1"];

    n3_2 -> n4 [from="out2",to="in1"];
    n3_2 -> q [from="out1"];

    n4_2 -> n3 [from="out1",to="in2"];
    n4_2 -> q_bar [from="out2"];
  ]

def d_latch_m := [graphEnv|
    d [type="io"];
    clk [type="io"];
    q [type="io"];
    q_bar [type="io"];

    n1 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n2 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n3 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n4 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];

    clk_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n3_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n4_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n1_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];

    d -> n1 [to="in1"];

    n1 -> n1_2 [from="out1", to="in1"];

    clk -> clk_2 [to="in1"];
    clk_2 -> n1 [from="out1",to="in2"];
    clk_2 -> n2 [from="out2",to="in2"];

    n1_2 -> n2 [from="out2",to="in1"];

    n1_2 -> n3 [from="out1",to="in1"];
    n2 -> n4 [from="out1",to="in2"];

    n3 -> n3_2 [from="out1",to="in1"];

    n4 -> n4_2 [from="out1",to="in1"];

    n3_2 -> n4 [from="out2",to="in1"];
    n3_2 -> q [from="out1"];

    n4_2 -> n3 [from="out1",to="in2"];
    n4_2 -> q_bar [from="out2"];
  ]

def d_latch_m_template : VerilogTemplate where
  module := build_local_module "d_latch_m" (simple_interface ["d", "clk"] ["q", "q_bar"]) ((build_verilog_body env d_latch_m.1).get rfl)
  instantiation name inst := format_instantiation "d_latch_m" name inst

def et_flip_flop_m := [graphEnv|
    clk [type="io"];
    d [type="io"];
    q [type="io"];
    -- q_bar [type="io"];

    n1 [type="nand_m1", typeImp = $(⟨_, nand_sm "nand1"⟩)];
    n2 [type="nand_m2", typeImp = $(⟨_, nand_sm "nand2"⟩)];
    n3 [type="nand3_m", typeImp = $(⟨_, nand3_sm⟩)];
    n4 [type="nand_m4", typeImp = $(⟨_, nand_sm "nand4"⟩)];
    n5 [type="nand_m5", typeImp = $(⟨_, nand_sm "nand5"⟩)];
    n6 [type="nand_m6", typeImp = $(⟨_, nand_sm "nand6"⟩)];

    clkF [type="clkF", typeImp = $(⟨_, fork_sm "clkF"⟩)];
    n2F [type="fork3_m", typeImp = $(⟨_, fork3_sm⟩)];
    n3F [type="n3_f", typeImp = $(⟨_, fork_sm "n3_f"⟩)];
    n4F [type="n4_f", typeImp = $(⟨_, fork_sm "n4_f"⟩)];
    n5F [type="n5_f", typeImp = $(⟨_, fork_sm "n5_f"⟩)];
    n6F [type="n6_f", typeImp = $(⟨_, fork_sm "n6_f"⟩)];
    sink [type="sink", typeImp=$(⟨_, sink_sm⟩)];

    n2 -> n2F [from="out1", to="in1"];
    n3 -> n3F [from="out1", to="in1"];
    n4 -> n4F [from="out1", to="in1"];

    n5 -> n5F [from="out1", to="in1"];
    n6 -> n6F [from="out1", to="in1"];

    clk -> clkF [to="in1"];

    d -> n4 [to="in2"];
    clkF -> n2 [from="out1", to="in2"];
    clkF -> n3 [from="out2", to="in2"];

    n1 -> n2 [from="out1", to="in1"];

    n2F -> n1 [from="out1", to="in2"];
    n2F -> n5 [from="out2", to="in1"];
    n2F -> n3 [from="out3", to="in1"];

    n3F -> n4 [from="out2", to="in1"];
    n3F -> n6 [from="out1", to="in2"];

    n4F -> n3 [from="out2", to="in3"];
    n4F -> n1 [from="out1", to="in1"];

    n5F -> n6 [from="out2", to="in1"];
    n6F -> n5 [from="out1", to="in2"];

    n5F -> q [from="out1"];
    -- Disabled for now
    n6F -> sink [from="out2", to="in1"];
  ]

def env' := env.cons "d_latch_m" d_latch_m_template

def dff_step (st : Bool × Bool) (pair : Bool × Bool) : Bool × Bool :=
  let (q, prev_c) := st
  let (c, x) := pair
  (if c && !prev_c then x else q, c)

def dff_raw (d clk : D) : D :=
  (scanl_drop dff_step (false, false) (List.zip clk d)).map (·.1)

theorem length_dff_raw (d clk : D) : (dff_raw d clk).length = min clk.length d.length
  := by unfold dff_raw; rw [List.length_map, List.length_scanl_drop, List.length_zip]

theorem dff_raw_take (d clk : D) (a b i : ℕ) (h: i < min (min a clk.length) (min b d.length)) :
  (dff_raw (List.take b d) (List.take a clk))[i]'(by simp only [length_dff_raw, List.length_take]; assumption) = (dff_raw d clk)[i]'(by rw [length_dff_raw]; omega)
  := by
  unfold dff_raw scanl_drop
  rw [List.getElem_map, List.getElem_map]
  rw [List.getElem_drop, List.getElem_drop]
  rw [List.getElem_scanl, List.getElem_scanl]
  rw [List.zip_take, List.take_take]
  congr
  omega

-- Not sure about this. Can we make some other kind of delay filter?
-- With a map or something?
-- It's hard to state what it "means", but other stuff is iffier :/
def delay_filter_step (delay : Nat) (state : (Bool × Nat)) (c : Bool) : (Bool × Nat) :=
  let (prev_c, countdown) := state
  (c,
    if c && !prev_c then delay
    else if countdown = 0 then 0
    else countdown - 1
  )

-- Becomes false for 4 ticks after a rising edge, to let the implementation catch up.
def delay_filter (clk : D) : D :=
  (scanl_drop (delay_filter_step 4) (false, 4) clk).map (·.2 == 0)


def error_filter_step (time : Nat) (state : (Bool × Option Nat)) (c : Bool) : (Bool × Option Nat) :=
  let (prev_c, timer) := state
  (c, match timer with
  | some timer =>
      if c == prev_c then some (timer - 1)
      else if timer = 0 then some (time - 1)
      else none
  | none => none)

-- If the clock switches from 0 to 1 or back without at least 3 steps of the previous value,
-- error out forever (we could probably reset at the next legal step, but this works too).
-- This is to prevent strange internal states. We need enough space before the falling edge too,
-- because that's still important to one of the loops.
def error_filter (clk : D) : D :=
  (scanl_drop (error_filter_step 3) (false, some 0) clk).map (·.2.isSome)

-- def setup_hold_filter_step (hold : Nat) (filtered_d : D) (state : (Bool × Bool × Nat)) (clk : Bool) : (Bool × Bool × Nat) :=
--  let (clean, prev_c, last_rising) := state
--
-- Since our hold is 1, we can simplify our stuff a bit!

def setup_hold_filter_step (state : (Bool × Bool)) (c_fd : (Bool × Bool)) : (Bool × Bool) :=
  let (prev_c, allowed) := state
  let (c, fd) := c_fd
  (c, if c && !prev_c then fd else allowed)

-- Setup/hold filter:
-- Whenever a clock rises, N ticks later, we check if there is a setup/hold time on the data.
-- If not, latch to error until the next clock rise.
-- We latch after the end of the hold, under the assumption that it will be blocked by the delay filter otherwise
-- This is because it's simpler to implement, though harder to state...
def setup_hold_filter (d clk : D) : D :=
  -- 3 = 2 + 1 of setup/hold
  (scanl_drop setup_hold_filter_step (false, false) (clk.zip (filter_window 3 d))).map (·.2)

def dff_filter (d clk : D) : D :=
  List.and3 (delay_filter clk) (error_filter clk) (setup_hold_filter d clk)

theorem length_dff_filter (d clk : D) : (dff_filter d clk).length = min clk.length d.length
  := by
  unfold dff_filter delay_filter error_filter and3 setup_hold_filter
  simp only [List.length_zipWith, List.length_map, List.length_scanl_drop, List.length_zip, List.length_filter_window]
  simp only [inf_le_left, inf_of_le_right]

theorem dff_filter_take (d clk : D) (a b i : ℕ) (h : i < min (min a clk.length) (min b d.length))
  : (dff_filter (List.take b d) (List.take a clk))[i]'(by simp only [length_dff_filter, List.length_take]; assumption) = (dff_filter d clk)[i]'(by rw [length_dff_filter]; omega)
  := by
  unfold dff_filter and3
  repeat rw [List.getElem_zipWith]
  apply congrArg₂ Bool.and
  <;> try apply congrArg₂ Bool.and

  all_goals (
    unfold delay_filter error_filter setup_hold_filter scanl_drop
    simp only [
      List.getElem_map, List.getElem_drop, List.getElem_scanl,
      List.filter_window_take, List.zip_take,
      List.take_take
    ]
    congr
    omega
  )

def et_flip_flop_spec : StringModule (D × D) :=
  { inputs := [ (↑"clk", ⟨ D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s.2 = s'.2 ⟩)
              , (↑"d", ⟨ D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s.1 = s'.1 ⟩)].toAssocList,
    outputs := [ (↑"q", ⟨ D, λ s tt s' => filtered_eq (dff_filter s.1 s.2) (dff_raw s.1 s.2) tt ∧ s = s' ⟩)
               , (↑"q_bar", ⟨ D, λ s tt s' => filtered_eq (dff_filter s.1 s.2) (List.not (dff_raw s.1 s.2)) tt ∧ s = s' ⟩)].toAssocList,
    init_state := λ s => s = default
  }

def future_sight_m (s : String := "") (n : Nat) : StringModule (Named s D) :=
  {
    inputs := [(↑"in", ⟨ Named s!"{s}.in" D, λ s tt s' => s <<: tt ∧ s' = tt⟩)].toAssocList,
    outputs := [(↑"out", ⟨ Named s!"{s}.out" D, λ s tt s' => s = s' ∧ (∃x, x.length <= n ∧ s ++ x = tt)⟩)].toAssocList,
    init_state := λ s => s = default
  }

def buffer_spec_m (s : String := "") : StringModule (Named s (D × D)) :=
  {
    inputs := [(↑"in", ⟨ Named s!"{s}.in" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)].toAssocList,
    outputs := [(↑"out", ⟨ Named s!"{s}.out" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ tt <+: s.1 ∧ s'.1 = s.1⟩)].toAssocList,
    init_state := λ s => s = default
  }

def et_ff_buffered_s := [graphEnv|
  clk [type="io"];
  d [type="io"];
  q [type="io"];

  b_clk [type="b_clk", typeImp=$(⟨_, buffer_spec_m "b_clk"⟩)];
  b_d [type="b_d", typeImp=$(⟨_, buffer_spec_m "b_d"⟩)];
  dff [type="dff", typeImp=$(⟨_, et_flip_flop_spec⟩)];
  fs [type="fs", typeImp=$(⟨_, future_sight_m "fs" 3⟩)];
  sink [type="sink", typeImp=$(⟨_, sink_sm⟩)];

  clk -> b_clk [to="in"];
  d -> b_d [to="in"];

  b_clk -> dff [from="out", to="clk"];
  b_d -> dff [from="out", to="d"];

  dff -> fs [from="q", to="in"];
  fs -> q [from="out"];
  -- Disconnected for proof simplicity; we'd need to divide
  -- The DFF into 2 modules, or have another buffer, to prove outputting on this.
  dff -> sink [from="q_bar", to="in1"];
 ]

def et_ms_flip_flop_m := [graphEnv|
    clk [type="io"];
    d [type="io"];
    q [type="io"];
    q_bar [type="io"];

    latch1 [type="d_latch_m", typeImp=$(ExprHigh.build_module d_latch_m.2.find? d_latch_m.1)];
    latch2 [type="d_latch_m", typeImp=$(ExprHigh.build_module d_latch_m.2.find? d_latch_m.1)];
    sink [type="sink_m", typeImp=$(⟨_, sink_sm⟩)];

    n1 [type="not_m", typeImp=$(⟨_, not_sm⟩)];
    n1F [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n2 [type="not_m", typeImp=$(⟨_, not_sm⟩)];

    d -> latch1 [to="d"];
    clk -> n1 [to="in1"];

    n1 -> n1F [from="out1", to="in1"];
    n1F -> latch1 [from="out1", to="clk"];
    n1F -> latch2 [from="out2", to="clk"];

    latch1 -> latch2 [from="q", to="d"];
    latch1 -> sink [from="q_bar", to="in1"];

    latch2 -> q [from="q"];
    latch2 -> q_bar [from="q_bar"];
  ]

namespace Refinement

def et_flip_flop_m_lowered := et_flip_flop_m.1.lower_TR |>.get rfl
def et_ff_buffered_s_lowered := et_ff_buffered_s.1.lower_TR |>.get rfl

def env := (et_flip_flop_m).2

@[drenv] theorem find?_nand1_m : (Batteries.AssocList.find? "nand_m1" env) = .some ⟨_, nand_sm "nand1"⟩ := rfl
@[drenv] theorem find?_nand2_m : (Batteries.AssocList.find? "nand_m2" env) = .some ⟨_, nand_sm "nand2"⟩ := rfl
@[drenv] theorem find?_nand3_m : (Batteries.AssocList.find? "nand_m4" env) = .some ⟨_, nand_sm "nand4"⟩ := rfl
@[drenv] theorem find?_nand4_m : (Batteries.AssocList.find? "nand_m5" env) = .some ⟨_, nand_sm "nand5"⟩ := rfl
@[drenv] theorem find?_nand5_m : (Batteries.AssocList.find? "nand_m6" env) = .some ⟨_, nand_sm "nand6"⟩ := rfl
@[drenv] theorem find?_nand_3_m : (Batteries.AssocList.find? "nand3_m" env) = .some ⟨_, nand3_sm⟩ := rfl
@[drenv] theorem find?_clkF_m : (Batteries.AssocList.find? "clkF" env) = .some ⟨_, fork_sm "clkF"⟩ := rfl
@[drenv] theorem find?_n3_f_m : (Batteries.AssocList.find? "n3_f" env) = .some ⟨_, fork_sm "n3_f"⟩ := rfl
@[drenv] theorem find?_n4_f_m : (Batteries.AssocList.find? "n4_f" env) = .some ⟨_, fork_sm "n4_f"⟩ := rfl
@[drenv] theorem find?_n5_f_m : (Batteries.AssocList.find? "n5_f" env) = .some ⟨_, fork_sm "n5_f"⟩ := rfl
@[drenv] theorem find?_n6_f_m : (Batteries.AssocList.find? "n6_f" env) = .some ⟨_, fork_sm "n6_f"⟩ := rfl
-- @[drenv] theorem find?_fork_m : (Batteries.AssocList.find? "fork_m" env) = .some ⟨_, fork_sm⟩ := rfl
@[drenv] theorem find?_fork3_m : (Batteries.AssocList.find? "fork3_m" env) = .some ⟨_, fork3_sm⟩ := rfl
@[drenv] theorem find?_sink_m : (Batteries.AssocList.find? "sink" env) = .some ⟨_, sink_sm⟩ := rfl

seal env in
def_module lhsModuleType : Type :=
  [T| et_flip_flop_m_lowered, env.find? ]
reduction_by
  dsimp [et_flip_flop_m_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env in
def_module lhsModule : StringModule lhsModuleType :=
  [e| et_flip_flop_m_lowered, env.find? ]
reduction_by
       dsimp [et_flip_flop_m_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )
        /- dsimp [Module.liftL, Module.liftR, drcomponents]) -/


def env_s := (et_ff_buffered_s).2

@[drenv] theorem find?_bclk_s : (Batteries.AssocList.find? "b_clk" env_s) = .some ⟨_, buffer_spec_m "b_clk"⟩ := rfl
@[drenv] theorem find?_bd_s : (Batteries.AssocList.find? "b_d" env_s) = .some ⟨_, buffer_spec_m "b_d"⟩ := rfl
@[drenv] theorem find?_sink_s : (Batteries.AssocList.find? "sink" env_s) = .some ⟨_, sink_sm⟩ := rfl
@[drenv] theorem find?_fs_s : (Batteries.AssocList.find? "fs" env_s) = .some ⟨_, future_sight_m "fs" 3⟩ := rfl
@[drenv] theorem find?_dff_s : (Batteries.AssocList.find? "dff" env_s) = .some ⟨_, et_flip_flop_spec⟩ := rfl

seal env_s in
def_module rhsModuleType : Type :=
  [T| et_ff_buffered_s_lowered, env_s.find? ]
reduction_by
  dsimp [et_ff_buffered_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env_s in
def_module rhsModule : StringModule rhsModuleType :=
  [e| et_ff_buffered_s_lowered, env_s.find? ]
reduction_by
       dsimp [et_ff_buffered_s_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )
        /- dsimp [Module.liftL, Module.liftR, drcomponents]) -/

macro "destruct_ands_eqs" : tactic =>
  `(tactic| with_reducible (repeat cases ‹_ ∧ _›); subst_vars; with_reducible (repeat cases ‹_ = _›))


theorem existSR_zero_single_step {S : Type _} (rules : List (S → S → Prop)):
  ∀ s s', ∀ rule ∈ rules, s = s' ∨ rule s s' → existSR rules s s' := by
  intros s s' rule Hin H
  rcases H with h | h
  . subst h
    exact existSR_reflexive
  . exact (existSR_single_step _ _ _ _ Hin h)

macro "indexed_rule_or_rfl" n:num t:term : tactic =>
  `(tactic| (apply existSR_zero_single_step
             apply @List.getElem_mem _ _ $n
              (by unfold rhsModule Module.internals; dsimp; omega)

             unfold rhsModule Module.internals Module.liftR Module.liftL Named; dsimp

             by_cases Hneq: $t
             (left; subst Hneq; rfl)
             right
            ))

def lhs_wf (lhs: lhsModuleType) : Prop :=
  let (n2, n2f, n6, n5, n4f, n3f, n4, n6f, clkf, n3, n1, (), n5f) := lhs
  -- Outputs
  n2.1 <+: (delay false (nand n1.1 n1.2)) ∧ n2f <+: (delay false (nand n2.1 n2.2)) ∧
  n3f <+: (delay false (nand3 n3.1 n3.2.1 n3.2.2)) ∧ n4f <+: (delay false (nand n4.1 n4.2)) ∧
  n5f <+: (delay false (nand n5.1 n5.2)) ∧ n6f <+: (delay false (nand n6.1 n6.2)) ∧
  -- Inputs
  n1.1 <+: n4f ∧ n1.2 <+: n2f ∧
  n2.2 <+: clkf ∧
  n3.1 <+: n2f ∧ n3.2.1 <+: clkf ∧ n3.2.2 <+: n4f ∧
  n4.1 <+: n3f ∧
  n5.1 <+: n2f ∧ n5.2 <+: n6f ∧
  n6.1 <+: n5f ∧ n6.2 <+: n3f

@[reducible] def d_from_lhs (lhs: lhsModuleType) : D := lhs.2.2.2.2.2.2.1.2
@[reducible] def clk_from_lhs (lhs: lhsModuleType) : D := lhs.2.2.2.2.2.2.2.2.1
@[reducible] def out_from_lhs (lhs: lhsModuleType) : D := lhs.2.2.2.2.2.2.2.2.2.2.2.2

theorem lhs_wf_eq (lhs: lhsModuleType) (h_wf: lhs_wf lhs) (i: ℕ)
  (h_clk: i < (clk_from_lhs lhs).length)
  (h_d: i < (d_from_lhs lhs).length)
  (h_out: i < (out_from_lhs lhs).length)
  : (dff_filter (clk_from_lhs lhs) (d_from_lhs lhs))[i]'(by rw [length_dff_filter]; omega) → (dff_raw (clk_from_lhs lhs) (d_from_lhs lhs))[i]'(by rw [length_dff_raw]; omega) = (out_from_lhs lhs)[i]
  := by
  sorry

theorem lhs_wf_len (lhs: lhsModuleType) (h_wf: lhs_wf lhs)
  : min (List.length (d_from_lhs lhs)) (List.length (clk_from_lhs lhs)) + 3 ≥ List.length (out_from_lhs lhs)
  := by
  sorry

lemma extension_length {α : Type _}
  (l: List α) (n: Nat)
  : n + 3 >= l.length → ∃x, x.length <= 3 ∧ (List.take n l) ++ x = l
  := by
  intro H
  use (List.drop n l)
  apply And.intro
  . rw [List.length_drop]
    omega
  . apply List.take_append_drop


instance : MatchInterface lhsModule rhsModule := by
  dsimp [lhsModule, et_ff_buffered_s]
  solve_match_interface
def φ (lhs: lhsModuleType) (rhs: rhsModuleType) : Prop :=
  let (n2, n2f, n6, n5, n4f, n3f, n4, n6f, clkf, n3, n1, (), n5f) := lhs
  let ((bd_in, bd_out), (bclk_in, bclk_out), (), fs, (rhsClk, rhsD)) := rhs
  -- The inputs of lhs and rhs must match
  clkf = bclk_in ∧ bd_in = n4.2 ∧
  -- The internal state of lhs must be sensical
  lhs_wf lhs ∧
  -- Main state invariant
  fs <+: n5f ∧
  -- Our spec doesn't move ahead of the impl
  rhsD.length <= n5f.length ∧ rhsClk.length <= n5f.length ∧
  -- The internal state of rhs must be sensical
  bd_out = rhsD ∧ bclk_out = rhsClk ∧
  bd_out <+: bd_in ∧ bclk_out <+: bclk_in ∧
  -- Follows from filtered eq, but is much simpler and is all we need.
  fs.length = min rhsClk.length rhsD.length

  -- Outdated
  --λ (_, _, _, _, (_, dataL), _, _, _, _, clkL, _) (clk, data) =>
    -- First, extract the state
    --dataL = data /\ clkL = clk
    -- Second, invariants
    -- Non-mathematically, our current ideas are the following two invariants:
    -- 1: the output state is at most the length of the input + delay
    -- 2: the function defined by the input is more defined than the output

lemma nand_no_int (s: String) : (nand_sm s).internals = []
  := by
  unfold nand_sm nand_m NatModule.stringify Module.mapIdent
  dsimp

-- TODO: some interesting tactics/lemmas could be simplifiers for length calculations
-- basically: simp with length_take, length_zip, length_* theorems, then
-- canonicalize the mins using commutativity and associativity and such (dunno how easy that is)
-- there's a lot of that stuff where I use grind.
theorem refines' :
  lhsModule ⊑_{φ} rhsModule := by
    intro lhsModule rhsModule inv
    unfold φ at inv
    obtain ⟨n2, n2f, n6, n5, n4f, n3f, ⟨n4_1, n4_2⟩, n6f, clkf, n3, n1, ⟨⟩, n5f⟩ := lhsModule
    obtain ⟨⟨bd_in, bd_out⟩, ⟨bclk_in, bclk_out⟩, ⟨⟩, fs, ⟨rhsClk, rhsD⟩⟩ := rhsModule
    dsimp at inv
    obtain ⟨HclkEq, HdEq, HlWF, HφFS, HφD, HφClk, HrDeq, HrClkEq, HrBD, HrBClk, HrFS⟩ := inv

    unfold Named at *
    apply Module.comp_refines.mk
    . -- Inputs
      intro ident ⟨on2, on2f, on6, on5, on4f, on3f, ⟨on4_1, on4_2⟩, on6f, oclkf, orest⟩ v h
      by_cases HContains: (lhsModule.inputs.contains ident)
      . -- Split by cases on the port
        unfold lhsModule at HContains; simp at HContains
        rcases HContains with h | h
        <;> subst_vars <;> dsimp <;> rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at h <;> simp [Module.liftL, Module.liftR] at h
        . -- data line
          destruct_ands_eqs
          rename_i Hstrict_less
          use ⟨(v, rhsD), (oclkf, rhsClk), (), fs, (rhsClk, rhsD)⟩
          use ⟨(v, rhsD), (oclkf, rhsClk), (), fs, (rhsClk, rhsD)⟩
          unfold Named at *
          with_reducible split_ands
          . -- Our new transition is valid
            rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
            trivial
          . -- Trivial transition
            exact existSR_reflexive
          . -- φ is still valid
            unfold φ
            dsimp

            -- Unwrap the basic consistency stuff
            unfold lhs_wf at ⊢ HlWF
            destruct_ands_eqs

            with_reducible split_ands
            <;> try trivial

            -- lhs is still consistent
            . apply List.IsPrefix.trans
              assumption

              unfold delay
              rw [List.prefix_cons_inj]
              apply List.nand_prefix
              . apply List.prefix_rfl
              . apply (List.strict_prefix_is_prefix _ _ Hstrict_less)
            -- rhs is still consistent
            . apply List.strict_prefix_is_prefix at Hstrict_less
              apply List.IsPrefix.trans <;> assumption
        . -- clock line
          destruct_ands_eqs
          rename_i Hstrict_less
          use ⟨(on4_2, rhsD), (v, rhsClk), (), fs, (rhsClk, rhsD)⟩
          use ⟨(on4_2, rhsD), (v, rhsClk), (), fs, (rhsClk, rhsD)⟩
          with_reducible split_ands
          . -- Our new transition is valid
            rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
            trivial
          . -- Trivial transition
            exact existSR_reflexive
          . -- φ is still valid
            unfold φ
            dsimp

            -- Unwrap the basic consistency stuff
            unfold lhs_wf at ⊢ HlWF
            destruct_ands_eqs

            with_reducible split_ands
            <;> try trivial
            -- lhs is still valid
            . apply List.strict_prefix_is_prefix at Hstrict_less
              apply List.IsPrefix.trans <;> assumption
            . apply List.IsPrefix.trans
              assumption
              apply (List.strict_prefix_is_prefix _ _ Hstrict_less)
            -- rhs is still valid
            . apply List.strict_prefix_is_prefix at Hstrict_less
              apply List.IsPrefix.trans <;> assumption
      . exfalso; exact (PortMap.getIO_not_contained_false h HContains)
    . -- Outputs
      intro ident ⟨on2, on2f, on6, on5, on4f, on3f, ⟨on4_1, on4_2⟩, on6f, oclkf, on3, on1, ⟨⟩, on5f⟩ v h
      unfold Named at *
      by_cases HContains: (lhsModule.outputs.contains ident)
      . unfold lhsModule at HContains; simp at HContains
        rcases HContains with h | h
        <;> subst_vars <;> dsimp <;> rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at h <;> simp [Module.liftL, Module.liftR] at h
        . -- the output q
          -- Little trick to get rid of v in the right direction
          -- v = n5f because forks always output themselves
          have Hvs : n5f = v := by destruct_ands_eqs; rfl
          subst Hvs
          destruct_ands_eqs
          -- on5f = v, easier intuition
          rename D => v
          let tlen := v.length
          let nD := List.take tlen on4_2
          let nClk := List.take tlen oclkf
          let nFs := List.take (min on4_2.length oclkf.length) v
          use ⟨(on4_2, nD), (oclkf, nClk), (), nFs, (nClk, nD)⟩
          use ⟨(on4_2, nD), (oclkf, nClk), (), nFs, (nClk, nD)⟩
          with_reducible split_ands
          . -- We can go from our old state to our new state
            apply (existSR_transitive _ _ ((on4_2, nD), (oclkf, nClk), (), fs, (nClk, nD)))
            apply (existSR_transitive _ _ ((on4_2, rhsD), (oclkf, nClk), (), fs, (nClk, rhsD)))
            . -- Update the clock line
              indexed_rule_or_rfl 0 (rhsClk = nClk)
              rename_i Hneq
              simp
              rw [and_comm, and_self_left]
              -- TODO: extract to lemma
              apply And.intro
              . rw [List.strict_prefix_iff_prefix_neq]
                apply And.intro _ Hneq

                rw [List.prefix_iff_eq_take] at HrBClk
                rw [List.prefix_iff_eq_take, List.take_take, HrBClk]
                congr
                grind only [= min_def]
              . apply List.take_prefix
            . -- Update the data line
              indexed_rule_or_rfl 1 (rhsD = nD)
              rename_i Hneq
              simp
              rw [and_comm, and_self_left]
              -- TODO: extract to lemma
              apply And.intro
              . rw [List.strict_prefix_iff_prefix_neq]
                apply And.intro _ Hneq

                rw [List.prefix_iff_eq_take] at HrBD
                rw [List.prefix_iff_eq_take, List.take_take, HrBD]
                congr
                grind only [= min_def]
              . apply List.take_prefix
            . -- Update the future-sight line
              indexed_rule_or_rfl 2 (fs = nFs)
              rename_i Hneq
              simp
              unfold filtered_eq
              with_reducible split_ands
              . rw [length_dff_raw]
                repeat rw [List.length_take]
                omega
              . rw [length_dff_filter, length_dff_raw]
              . intro i
                intro H
                apply List.getElem_of_getElem? at H
                obtain ⟨Hi, H⟩ := H
                rw [length_dff_filter] at Hi
                rw [List.getElem?_eq_getElem (by rw [length_dff_raw]; exact Hi)]
                rw [List.getElem?_eq_getElem (by grind only [List.length_take])]
                unfold nFs nClk nD
                rw [Option.some_inj, List.getElem_take]
                rw [dff_raw_take _ _ _ _ _ (by grind only [= List.length_take])]
                apply lhs_wf_eq _ HlWF _
                  (by grind only [= List.length_take, = min_def])
                  (by grind only [= List.length_take, = min_def])
                  (by grind only [= List.length_take, = min_def])

                dsimp [clk_from_lhs, d_from_lhs]
                rw [←H]
                rw [dff_filter_take]
                grind only [= List.length_take]
              . rw [List.strict_prefix_iff_prefix_neq]
                apply And.intro _ Hneq
                unfold nFs

                rw [List.prefix_iff_eq_take] at HφFS
                rw [List.prefix_iff_eq_take, List.take_take, HφFS]
                apply List.IsPrefix.length_le at HrBD
                apply List.IsPrefix.length_le at HrBClk
                congr
                grind only [= min_def]
          . -- Our output is valid (in practice: nFs is behind by a certain amount at most)
            rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
            dsimp [Module.liftL, Module.liftR]
            split_ands <;> try rfl
            apply extension_length
            apply lhs_wf_len _ HlWF
          . -- Our phi is still true after
            unfold nD nClk tlen
            unfold φ; with_reducible split_ands
            <;> try trivial
            all_goals try (repeat rw [List.length_take]); omega
            all_goals try apply List.take_prefix
      . exfalso; exact (PortMap.getIO_not_contained_false h HContains)
    . -- Internals
      intro rule ⟨(on2_1, on2_2), on2f, (on6_1, on6_2), (on5_1, on5_2), on4f, on3f, ⟨on4_1, on4_2⟩, on6f, oclkf, (on3_1, on3_2, on3_3), (on1_1, on1_2), (), on5f⟩ Hin Ha
      rw [List.mem_iff_getElem] at Hin
      obtain ⟨i, Hidx, Hin⟩ := Hin
      dsimp [lhsModule, nand_sm, nand_m, nand3_sm, nand3_m, fork_sm, fork_m, fork3_sm, fork3_m, sink_sm, sink_m,
        NatModule.stringify, Module.mapIdent] at Hidx

      obtain ⟨n2_1, n2_2⟩ := n2; obtain ⟨n6_1, n6_2⟩ := n6;
      obtain ⟨n5_1, n5_2⟩ := n5; obtain ⟨n3_1, n3_2, n3_3⟩ := n3
      obtain ⟨n1_1, n1_2⟩ := n1
      use ((bd_in, bd_out), (bclk_in, bclk_out), PUnit.unit, fs, rhsClk, rhsD)

      sorry -- 18 internal rules; prove that well-formedness holds
      -- Can mostly be grinded away, but we gotta split all the cases and that's annoying

theorem refines :
  lhsModule ⊑ et_flip_flop_spec := by sorry

end Refinement

end FlipFlop

/- Disabled for speed when working above.
namespace FullAdder

-- TODO maybe: move monotonicity directly to the outputs of the impl module
def monotonic_output (s s' tt goal : D) : Prop := s <<: s' ∧ s' = tt ∧ tt = goal

def half_adder_m (s : String := "") : StringModule (Named s (D × D)) :=
  { inputs := [(↑"a", ⟨ Named s!"{s}.a" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ Named s!"{s}.b" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [ (↑"s", ⟨ Named s!"{s}.s" D, λ s tt s' => s = s' ∧ tt = (delay false (xor s.1 s.2)) ⟩)
               , (↑"c", ⟨ Named s!"{s}.c" D, λ s tt s' => s = s' ∧ tt = (delay false (and s.1 s.2)) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def or_m (s : String := "") : StringModule (D × D) :=
  { inputs := [(↑"a", ⟨ D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(↑"c", ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (or s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def adcb (a b c : D) : D × D :=
  (List.map (fun x => (BitVec.adcb x.1 x.2.1 x.2.2).1) (List.zip a (List.zip b c)), List.map (fun x => (BitVec.adcb x.1 x.2.1 x.2.2).2) (List.zip a (List.zip b c)))

theorem length_adcb_1 :
  ∀ a b c, List.length (adcb a b c).1 = min a.length (min b.length c.length)
  := by
  unfold adcb
  intros
  rw [List.length_map, List.length_zip, List.length_zip]

theorem length_adcb_2 :
  ∀ a b c, List.length (adcb a b c).2 = min a.length (min b.length c.length)
  := by
  unfold adcb
  intros
  rw [List.length_map, List.length_zip, List.length_zip]

def full_adder_spec_m (s : String := "") : StringModule (Named s (D × D × D)) :=
  { inputs := [(↑"a", ⟨ Named s!"{s}.a" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ Named s!"{s}.b" D, λ s tt s' => s.2.1 <<: tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
               (↑"cin", ⟨ Named s!"{s}.c" D, λ s tt s' => s.2.2 <<: tt ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
    outputs := [ (↑"s", ⟨ Named s!"{s}.s" D, λ s tt s' => s = s' ∧ filtered_eq (filter_window3 3 s.1 s.2.1 s.2.2) (adcb s.1 s.2.1 s.2.2).2 tt ⟩)
               , (↑"cout", ⟨ Named s!"{s}.c" D, λ s tt s' => s = s' ∧ filtered_eq (filter_window3 3 s.1 s.2.1 s.2.2) (adcb s.1 s.2.1 s.2.2).1 tt ⟩)].toAssocList
    init_state := λ s => s = default
  }

def future_sight_m (s : String := "") (n : Nat) : StringModule (Named s D) :=
  {
    inputs := [(↑"in", ⟨ Named s!"{s}.in" D, λ s tt s' => s <<: tt ∧ s' = tt⟩)].toAssocList,
    outputs := [(↑"out", ⟨ Named s!"{s}.out" D, λ s tt s' => s = s' ∧ (∃x, x.length <= n ∧ s ++ x = tt)⟩)].toAssocList,
    init_state := λ s => s = default
  }

def buffer_spec_m (s : String := "") : StringModule (Named s (D × D)) :=
 {
  inputs := [(↑"in", ⟨ Named s!"{s}.in" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)].toAssocList,
  outputs := [(↑"out", ⟨ Named s!"{s}.out" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ tt <+: s.1 ∧ s'.1 = s.1⟩)].toAssocList,
  init_state := λ s => s = default
 }

def sink_m : StringModule Unit :=
  { inputs := [(↑"in", ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    outputs := ∅
    init_state := λ s => s = default
  }

 def buffered_full_adder_m := [graphEnv|
  a [type="io"];
  b [type="io"];
  cin [type="io"];
  s [type="io"];
  -- cout [type="io"];

  b_a [type="b_a", typeImp=$(⟨_, buffer_spec_m "b_a"⟩)];
  b_b [type="b_b", typeImp=$(⟨_, buffer_spec_m "b_b"⟩)];
  b_c [type="b_c", typeImp=$(⟨_, buffer_spec_m "b_c"⟩)];

  fa [type="fa", typeImp=$(⟨_, full_adder_spec_m "fa"⟩)];
  fs_1 [type="fs_1", typeImp=$(⟨_, future_sight_m "fs_1" 3⟩)];
  fs_2 [type="fs_2", typeImp=$(⟨_, future_sight_m "fs_2" 3⟩)];
  sink [type="sink", typeImp=$(⟨_, sink_m⟩)];

  a -> b_a [to="in"];
  b -> b_b [to="in"];
  cin -> b_c [to="in"];

  b_a -> fa [from="out", to="a"];
  b_b -> fa [from="out", to="b"];
  b_c -> fa [from="out", to="cin"];

  fa -> fs_1 [from="s", to="in"];
  fa -> fs_2 [from="cout", to="in"];
  fs_1 -> s [from="out"];
  -- Disconnected for proof simplicity; we'd need to divide
  -- The full adder into 2 to prove outputting on this.
  fs_2 -> sink [from="out", to="in"];
  -- fs_2 -> cout [from="out"];
 ]

def buffered_full_adder_m_lowered := buffered_full_adder_m.1.lower_TR |>.get rfl

def env_bfam := buffered_full_adder_m.2

@[drenv] theorem find?_fa_m : (Batteries.AssocList.find? "fa" env_bfam) = .some ⟨_, full_adder_spec_m "fa"⟩ := rfl
@[drenv] theorem find?_b_a_m : (Batteries.AssocList.find? "b_a" env_bfam) = .some ⟨_, buffer_spec_m "b_a"⟩ := rfl
@[drenv] theorem find?_b_b_m : (Batteries.AssocList.find? "b_b" env_bfam) = .some ⟨_, buffer_spec_m "b_b"⟩ := rfl
@[drenv] theorem find?_b_c_m : (Batteries.AssocList.find? "b_c" env_bfam) = .some ⟨_, buffer_spec_m "b_c"⟩ := rfl
@[drenv] theorem find?_fs1_m : (Batteries.AssocList.find? "fs_1" env_bfam) = .some ⟨_, future_sight_m "fs_1" 3⟩ := rfl
@[drenv] theorem find?_fs2_m : (Batteries.AssocList.find? "fs_2" env_bfam) = .some ⟨_, future_sight_m "fs_2" 3⟩ := rfl
@[drenv] theorem find?_sink_s_m : (Batteries.AssocList.find? "sink" env_bfam) = .some ⟨_, sink_m⟩ := rfl

seal env_bfam in
def_module full_adder_spec_t : Type :=
  [T| buffered_full_adder_m_lowered, env_bfam.find? ]
reduction_by
  dsimp [buffered_full_adder_m_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp


seal env_bfam in
def_module full_adder_spec : StringModule full_adder_spec_t :=
  [e| buffered_full_adder_m_lowered, env_bfam.find? ]
reduction_by
       dsimp [buffered_full_adder_m_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )

/--
Equivalent to just xor.
-/
def full_adder_s := [graphEnv|
    a [type="io"];
    b [type="io"];
    cin [type="io"];
    s [type="io"];
    -- cout [type="io"];

    ha1 [type="ha_1", typeImp=$(⟨_, half_adder_m "ha_1"⟩)];
    ha2 [type="ha_2", typeImp=$(⟨_, half_adder_m "ha_2"⟩)];
    or [type="or", typeImp=$(⟨_, or_m⟩)];
    sink [type="sink", typeImp=$(⟨_, sink_m⟩)];

    a -> ha1 [to="a"];
    b -> ha1 [to="b"];
    cin -> ha2 [to="a"];
    ha1 -> ha2 [from="s",to="b"];
    ha2 -> s [from="s"];
    ha2 -> or [from="c",to="a"];
    ha1 -> or [from="c",to="b"];
    or -> sink [from="c",to="in"];
    -- or -> cout [from="c"];
  ]

def full_adder_s_lowered := full_adder_s.1.lower_TR |>.get rfl

def env_fas := full_adder_s.2

@[drenv] theorem find?_ha1_m : (Batteries.AssocList.find? "ha_1" env_fas) = .some ⟨_, half_adder_m "ha_1"⟩ := rfl
@[drenv] theorem find?_ha2_m : (Batteries.AssocList.find? "ha_2" env_fas) = .some ⟨_, half_adder_m "ha_2"⟩ := rfl
@[drenv] theorem find?_or_m : (Batteries.AssocList.find? "or" env_fas) = .some ⟨_, or_m⟩ := rfl
@[drenv] theorem find?_sink_i_m : (Batteries.AssocList.find? "sink" env_fas) = .some ⟨_, sink_m⟩ := rfl

seal env_fas in
def_module full_adder_imp_t : Type :=
  [T| full_adder_s_lowered, env_fas.find? ]
reduction_by
  dsimp [full_adder_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env_fas in
def_module full_adder_imp : StringModule full_adder_imp_t :=
  [e| full_adder_s_lowered, env_fas.find? ]
reduction_by
       dsimp [full_adder_s_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )

instance : MatchInterface full_adder_imp full_adder_spec := by
  dsimp [full_adder_imp,full_adder_spec]
  solve_match_interface


def φ (lhs: full_adder_imp_t) (rhs : full_adder_spec_t) : Prop :=
  /- Naming conventions:
  - lA/lB/lCin are the left A B and Cin inputs
  - ha?? are the half-adders' outputs as fed into another module

  Similarly, for the right module
  - b?_in/b?_out are the input/output buffers for the buffer modules
  - fs_? are the future-sight modules
  - aA/aB/aC are the right A B and Cin inputs into the spec calculator
  -/
  -- Unit added for sink on both
  let ((lA, lB), (), (lCin, ha1s), (ha1c, ha2c)) := lhs
  let (fs_s, (aA, aB, aC), (), (ba_in, ba_out), (bb_in, bb_out), (bc_in, bc_out), fs_c) := rhs
  let lenS := (delay false (xor lCin ha1s)).length
  let filter := (filter_window3 3 aA aB aC)
  -- Input states must be equivalent
  lA = ba_in ∧ lB = bb_in ∧ lCin = bc_in ∧
  -- Internal state of the impl is logical.
  ha1s <+: (delay false (xor lA lB)) ∧
  -- Internal state of the spec is logical.
  aA = ba_out ∧ aB = bb_out ∧ aC = bc_out ∧
  ba_out <+: ba_in ∧ bb_out <+: bb_in ∧ bc_out <+: bc_in ∧
  filtered_eq filter (adcb aA aB aC).2 fs_s ∧ -- Could be reduced to a simple length match
  -- Our spec doesn't move ahead of the impl
  aA.length <= lenS ∧ aB.length <= lenS ∧ aC.length <= lenS ∧
  fs_s <+: (delay false (xor lCin ha1s))


-- === BEGIN REFINEMENT LEMMAS ===

-- From here on, we make a bunch of lemmas that are true
-- but potentially structured a bit strangely
-- this is because they really only exist as tools to prove refinement

/-
Extracts the componentwise conjunction from `filter_window3`.
-/
-- Maybe we could simplify those length proofs?
lemma filter_window3_getElem_and (a b c : List Bool) (i : Nat)
    (hi : i < (filter_window3 3 a b c).length) :
    (filter_window3 3 a b c)[i] = true ↔
    (filter_window 3 a)[i]'(by simp only [filter_window3, List.length_zipWith, length_filter_window, lt_inf_iff] at hi; rw [length_filter_window]; omega) = true ∧
    (filter_window 3 b)[i]'(by simp only [filter_window3, List.length_zipWith, length_filter_window, lt_inf_iff] at hi; rw [length_filter_window]; omega) = true ∧
    (filter_window 3 c)[i]'(by simp only [filter_window3, List.length_zipWith, length_filter_window, lt_inf_iff] at hi; rw [length_filter_window]; omega) = true := by
      unfold filter_window3;
      grind only [= List.getElem_zipWith]

-- This def was given by Aristotle. It works and makes sense, but jeez.
/-
If `filter_window 3 a` is `true` at index `i` (with `i < a.length`), then `i ≥ 3`
    and elements at indices `i-1` and `i-2` equal the element at index `i`.
-/
lemma filter_window_3_stable (a : List Bool) (i : Nat) (hi : i < a.length) :
    (filter_window 3 a)[i]'(by rw [length_filter_window]; exact hi) = true →
    i ≥ 3 ∧ a[i - 1]'(by omega) = a[i] ∧ a[i - 2]'(by omega) = a[i] := by
      unfold filter_window
      rcases i with ( _ | _ | _ | i )
      <;> try (grind only [= List.getElem_map, = List.getElem_range])
      by_cases H : a[i + 1 + 1 + 1] <;>
      (
        simp_all;
        repeat rw [
          List.drop_eq_getElem_cons (by rw [List.length_take]; omega),
          List.getElem_take
        ];
        repeat rw [List.mem_cons];
        grind only
      )
/-
At filter-true positions of `filter_window3 3 a b cin`, the carry (adcb sum)
    agrees with the delayed XOR computation.
-/
lemma sum_pad_agree_at_stable (a b cin : List Bool)
    (i : Nat)
    (hi_f : i < (filter_window3 3 a b cin).length)
    (hi_c : i < ((adcb a b cin).2).length)
    (hi_p : i < (delay false (xor cin (delay false (xor a b)))).length)
    (hfilter : (filter_window3 3 a b cin)[i] = true) :
    ((adcb a b cin).2)[i] = (delay false (xor cin (delay false (xor a b))))[i] := by
      -- Extract the stability conditions from `filter_window3_getElem_and` and `filter_window_3_stable`.
      obtain ⟨ha_w, hb_w, hc_w⟩ := (filter_window3_getElem_and a b cin i hi_f).mp hfilter
      unfold adcb at hi_c
      simp at hi_c
      unfold delay List.xor at hi_p
      simp at hi_p

      obtain ⟨hi_m, ha_1, ha_2⟩ := filter_window_3_stable a i (by grind only) ha_w
      obtain ⟨-, hb_1, hb_2⟩ := filter_window_3_stable b i (by grind only) hb_w
      obtain ⟨-, hc_1, hc_2⟩ := filter_window_3_stable cin i (by grind only) hc_w
      destruct_ands_eqs
      clear ha_w hb_w hc_w hfilter hi_f

      unfold adcb delay List.xor BitVec.adcb
      rw [List.getElem_map, List.getElem_zip, List.getElem_zip]
      grind only [= List.getElem_cons, = List.getElem_zipWith]

lemma adcb_snd_agrees (a b c a' b' c' : D) (i: Nat)
  (h_a: a <+: a') (h_b: b <+: b') (h_c: c <+: c')
  (h_lhs : i < (adcb a b c).2.length)
  : (adcb a b c).2[i] = (adcb a' b' c').2[i]'(by rw [length_adcb_2] at *; grind only [= min_def, usr List.IsPrefix.length_le])
  := by
  unfold adcb
  simp only [List.getElem_map, List.getElem_zip]
  unfold BitVec.adcb
  grind only [List.IsPrefix.getElem]


lemma getElem_delay_xor_agrees_r (a b l : D) (i: Nat)
  (h_mid : a <+: b)
  (h_lhs : i < (delay false (List.xor l a)).length)
  : (delay false (List.xor l a))[i] = (delay false (List.xor l b))[i]'
    (by
      unfold List.xor delay at *
      grind only [= List.length_cons, = List.length_zipWith, usr List.IsPrefix.length_le, = min_def]
    )
  := by
  unfold delay List.xor
  cases i with
  | zero => rfl
  | succ i =>
      dsimp
      rw [List.getElem_zipWith, List.getElem_zipWith]
      rw [Bool.xor_right_inj]
      apply List.IsPrefix.getElem h_mid


lemma delay_xor_prefix_l (l l' r : D)
  : l <+: l' → (delay false (List.xor l r)) <+: (delay false (List.xor l' r))
  := by
  intro H
  unfold List.xor delay
  rw [List.prefix_cons_inj]
  apply List.zipWith_prefix
  assumption; apply List.prefix_rfl

lemma delay_xor_prefix_r (l r r' : D)
  : r <+: r' → (delay false (List.xor l r)) <+: (delay false (List.xor l r'))
  := by
  intro H
  unfold List.xor delay
  rw [List.prefix_cons_inj]
  apply List.zipWith_prefix
  apply List.prefix_rfl; assumption

lemma filtered_eq_impl_out (a b c a' b' c' h h' : D)
  (Ha: a' <+: a) (Hb: b' <+: b) (Hc: c' <+: c)
  (Hmid: h <+: delay false (List.xor a b))
  (Hend: h' <+: (delay false (List.xor c h)))
  (Hlen_end: List.length (adcb a' b' c').2 = List.length h')
  : filtered_eq (filter_window3 3 a' b' c') (adcb a' b' c').2 h'
  := by
  split_ands
  . exact Hlen_end
  . rw [List.length_filter_window3, length_adcb_2]
  . intros i Hf
    rw [getElem?_eq_some_iff] at Hf
    obtain ⟨Hi, Hf⟩ := Hf

    -- Simplify our i bounds
    simp only [List.length_filter_window3, List.length_take, Nat.lt_min] at Hi
    obtain ⟨Hia, Hib, Hic⟩ := Hi
    rw [length_adcb_2] at Hlen_end

    -- Go from [i]? to [i]
    rw [
      (getElem?_pos _ _ (by grind only [length_adcb_2, min_def])),
      (getElem?_pos _ _ (by grind only [min_def]))
    ]
    rw [Option.some.injEq]

    rw [List.IsPrefix.getElem Hend]

    -- Generalize arguments to their longest form
    -- We're accessing a single value, so who cares about lengths
    rw [getElem_delay_xor_agrees_r _ _ _ _ Hmid]
    rw [
      adcb_snd_agrees _ _ _
        a b c _
        (by assumption) (by assumption) (by assumption)
    ]

    -- Actually prove they match!
    apply (sum_pad_agree_at_stable _ _ _ _ (by rw [length_filter_window3]; grind only [= min_def, usr List.IsPrefix.length_le]))

    -- Last condition: the filter must be true here for them to agree
    -- Just gotta prove our previous filter hypothesis transfers over!
    -- Could be lemma'd if slow?
    obtain ⟨Hfa, Hfb, Hfc⟩ := (filter_window3_getElem_and _ _ _ _ _).mp Hf
    rw [filter_window3_getElem_and]

    split_ands
    <;> grind only [List.IsPrefix.getElem, filter_window_prefix, usr List.take_prefix]

theorem move_buffer_forward_legal :
  ∀ old max : D, ∀ n,
    old <+: max →
    old.length <= n →
    ¬(old = (List.take n max)) →
    old <<: (List.take n max)
  := by
  intros old max n Hp Hlen Hneq
  rw [List.strict_prefix_iff_prefix_neq]
  split_ands
  . eapply List.prefix_of_prefix_length_le
    . assumption
    . apply List.take_prefix
    . rw [List.length_take]
      -- These next lines could just be a grind.
      rw [Nat.le_min]
      split_ands
      . assumption
      . apply List.IsPrefix.length_le
        assumption
  . assumption

theorem refines' :
  full_adder_imp ⊑_{φ} full_adder_spec := by
    unfold Module.refines_φ
    intro init_i init_s Hφ
    -- Sinks added everywhere for sink module
    obtain ⟨⟨lA, lB⟩, ⟨⟩, ⟨lCin, ha1s⟩, ⟨ha1c, ha2c⟩⟩ := init_i
    obtain ⟨fs_s, ⟨aA, aB, aC⟩, ⟨⟩, ⟨ba_in, ba_out⟩, ⟨bb_in, bb_out⟩, ⟨bc_in, bc_out⟩, fs_c⟩ := init_s
    obtain ⟨HlLA, HlLB, HlLCin, Hl1s, HrLA, HrLB, HrLC, HφBA, HφBB, HφBC, HφFSE, HφAF, HφBF, HφCF, HφFSD⟩ := Hφ
    subst HlLA HlLB HlLCin HrLA HrLB HrLC

    apply Module.comp_refines.mk
    . -- Inputs
      intro ident ⟨⟨oA, oB⟩, ⟨⟩, ⟨oCin, oha1s⟩, ⟨oha1c, oha2c⟩⟩ s a

      -- The ident has to resolve to something
      by_cases HContains: (full_adder_imp.inputs.contains ident)
      . -- Unpack initial states for both modules
        -- Split by cases on the port
        unfold full_adder_imp at HContains; simp at HContains
        rcases HContains with h | h | h
        <;> subst_vars <;> simp <;> rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at a <;> simp [Module.liftL, Module.liftR] at a
        . -- Input accepted: a.
          destruct_ands_eqs
          rename_i accept
          -- Swap out rA in our previous state's definition
          use ⟨fs_s, ⟨aA, aB, aC⟩, ⟨⟩, ⟨s, aA⟩, ⟨oB, aB⟩, ⟨oCin, aC⟩, fs_c⟩
          apply And.intro
          . -- Our new transition is valid
            rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
            trivial
          . -- Our new state maintains φ
            -- We use the same state with no internal rules
            use ⟨fs_s, ⟨aA, aB, aC⟩, ⟨⟩, ⟨s, aA⟩, ⟨oB, aB⟩, ⟨oCin, aC⟩, fs_c⟩
            apply And.intro
            . exact existSR_reflexive
            . unfold φ
              with_reducible split_ands <;> try rfl
              all_goals try solve
              | assumption
              . apply List.IsPrefix.trans Hl1s
                  (delay_xor_prefix_l _ _ _
                    (List.strict_prefix_is_prefix _ _ accept)
                  )
              . exact List.IsPrefix.trans HφBA (strict_prefix_is_prefix _ _ accept)
        . -- Input accepted: b.
          destruct_ands_eqs
          rename_i accept
          -- Swap out rB in our previous state's definition
          use ⟨fs_s, ⟨aA, aB, aC⟩, ⟨⟩, ⟨oA, aA⟩, ⟨s, aB⟩, ⟨oCin, aC⟩, fs_c⟩
          apply And.intro
          . -- Our new transition is valid
            rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
            trivial
          . -- Our new state maintains φ
            -- We use the same state with no internal rules
            use ⟨fs_s, ⟨aA, aB, aC⟩, ⟨⟩, ⟨oA, aA⟩, ⟨s, aB⟩, ⟨oCin, aC⟩, fs_c⟩
            apply And.intro
            . exact existSR_reflexive
            . unfold φ
              with_reducible split_ands <;> try rfl
              all_goals try solve
              | assumption
              . apply List.IsPrefix.trans Hl1s
                  (delay_xor_prefix_r _ _ _
                    (List.strict_prefix_is_prefix _ _ accept)
                  )
              . exact List.IsPrefix.trans HφBB (strict_prefix_is_prefix _ _ accept)
        . -- Input accepted: cin
          destruct_ands_eqs
          rename_i accept
          -- Swap out rB in our previous state's definition
          use ⟨fs_s, ⟨aA, aB, aC⟩, ⟨⟩, ⟨oA, aA⟩, ⟨oB, aB⟩, ⟨s, aC⟩, fs_c⟩
          apply And.intro
          . -- Our new transition is valid
            rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
            dsimp [Module.liftR, Module.liftL]
            trivial
          . -- Our new state maintains φ
            -- We use the same state with no internal rules
            use ⟨fs_s, ⟨aA, aB, aC⟩, ⟨⟩, ⟨oA, aA⟩, ⟨oB, aB⟩, ⟨s, aC⟩, fs_c⟩
            apply And.intro
            . exact existSR_reflexive
            . unfold φ
              unfold delay List.xor at HφAF HφBF HφCF
              rw [List.length_cons, List.length_zipWith] at HφAF HφBF HφCF
              have Hlen := ((strict_prefix_iff_prefix_length _ _).mp accept).right

              with_reducible split_ands <;> try rfl
              all_goals try solve
              | assumption
              | unfold delay List.xor; rw [List.length_cons, List.length_zipWith]; omega

              apply List.IsPrefix.trans HφBC
                (strict_prefix_is_prefix _ _ accept)
              apply List.IsPrefix.trans HφFSD
                  (delay_xor_prefix_l _ _ _
                    (List.strict_prefix_is_prefix _ _ accept)
                  )
      . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
    . -- Outputs
      intro ident ⟨⟨oA, oB⟩, ⟨⟩, ⟨oCin, oha1s⟩, ⟨oha1c, oha2c⟩⟩ s a
      -- The ident has to resolve to something
      by_cases HContains: (full_adder_imp.outputs.contains ident)
      . -- Unpack initial states for both modules
        -- Split by cases on the port
        unfold full_adder_imp at HContains; simp at HContains
        rcases HContains with h | h | h
        <;> subst_vars <;> simp <;> rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at a <;> simp at a
        . -- Extracting sum
          dsimp [Module.liftL, Module.liftR] at a
          destruct_ands_eqs
          -- Compute the new state
          -- 1. All of the inputs to the FA module need to be caught up
          --    The FA module outputs the same length as the min of its inputs
          --    So we take the same length as the desired output (the future module is only used if needed)
          -- 2. The future sight module needs to be caught up as well.
          --    It simply takes `adcb` on all max inputs truncated to the right length
          --    (easily proven to be the same as the buffered version)
          let tlen := (delay false (xor lCin ha1s)).length
          let naA := List.take tlen oA
          let naB := List.take tlen oB
          let naC := List.take tlen lCin
          let new_fs_s := (List.take (min oA.length (min oB.length lCin.length)) (delay false (xor lCin ha1s)))
          let intermediate_states : D → D → D → D → full_adder_spec_t :=
            fun a b c fs => ⟨fs, ⟨a, b, c⟩, ⟨⟩, ⟨oA, a⟩, ⟨oB, b⟩, ⟨lCin, c⟩, fs_c⟩
          use (intermediate_states naA naB naC new_fs_s)
          have Hfs_feq : filtered_eq (filter_window3 3 naA naB naC) (adcb naA naB naC).2 new_fs_s
          := by
            apply filtered_eq_impl_out
            all_goals try solve |apply List.take_prefix |assumption

            subst new_fs_s tlen naA naB naC
            unfold delay List.xor
            simp only [List.length_filter_window3, List.length_cons, length_adcb_2, List.length_take, List.length_zipWith, List.length_zip]
            grind only

          apply And.intro
          . -- There are 3 buffer -> FA transitions, and 1 FA -> fs transition
            -- Therefore, there are 4 intermediate states.
            apply (existSR_transitive _ _
              (intermediate_states naA naB naC fs_s)
            _)
            . -- 3 buffer -> FA transitions
              apply (existSR_transitive _ _
                (intermediate_states naA naB aC fs_s)
              _)
              apply (existSR_transitive _ _
                (intermediate_states naA aB aC fs_s)
              _)
              -- These are kinda slow :(
              all_goals subst intermediate_states; dsimp
              . indexed_rule_or_rfl 0 (aA = naA)
                simp
                rw [and_comm, and_self_left]
                grind only [move_buffer_forward_legal, List.take_prefix]
              . indexed_rule_or_rfl 1 (aB = naB)
                simp
                rw [and_comm, and_self_left]
                grind only [move_buffer_forward_legal, List.take_prefix]
              . indexed_rule_or_rfl 2 (aC = naC)
                simp
                rw [and_comm, and_self_left]
                grind only [move_buffer_forward_legal, List.take_prefix]
            . -- FA -> fs transition
              subst intermediate_states; dsimp
              -- We need to add that the future sight's input is always the result of the FA's computation.
              -- Also that the input of the FA is always a sublist of the full input?
              indexed_rule_or_rfl 3 (fs_s = new_fs_s)
              simp
              apply And.intro
              . assumption
              . rw [List.strict_prefix_iff_prefix_neq]
                apply And.intro
                . subst new_fs_s
                  rw [List.prefix_take_iff]
                  apply And.intro
                  assumption
                  obtain ⟨Hlfs, -⟩ := HφFSE
                  rw [←Hlfs, length_adcb_2]
                  grind only [usr List.IsPrefix.length_le, = min_def]
                . assumption
          . -- Do the output step. No state changes.
            use (intermediate_states naA naB naC new_fs_s)
            apply And.intro
            . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
              dsimp [intermediate_states]
              simp only [true_and, and_true]
              subst new_fs_s
              apply extension_length

              have Hl1s := (List.IsPrefix.length_le Hl1s)
              unfold List.xor delay at ⊢ Hl1s
              rw [List.length_cons, List.length_zipWith] at ⊢ Hl1s
              omega
            . unfold φ
              with_reducible split_ands <;> try rfl

              all_goals try solve
                |assumption
                |apply List.take_prefix
                |rw [List.length_take]; apply Nat.min_le_left
      . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
    . -- Internals
      intro rule ⟨⟨oA, oB⟩, ⟨⟩, ⟨oCin, oha1s⟩, ⟨oha1c, oha2c⟩⟩ Hin Ha
      rw [List.mem_iff_getElem] at Hin
      obtain ⟨i, Hidx, Hin⟩ := Hin
      dsimp [full_adder_imp, half_adder_m, or_m] at Hidx
      rcases i with z | o | t | sink | i
      rotate_right; contradiction

      all_goals (
        dsimp [full_adder_imp] at Hin
        subst Hin
        dsimp [Module.liftL, Module.liftR, Named] at Ha
        simp at Ha
        destruct_ands_eqs
      )

      . -- Rule 0
        use (fs_s, (aA, aB, aC), (), (oA, aA), (oB, aB), (oCin, aC), fs_c)
        apply And.intro; apply existSR_reflexive

        -- Length stuff for easier proofs later
        have Hlen1s := List.IsPrefix.length_le Hl1s
        unfold List.xor delay at HφAF HφBF HφCF Hlen1s
        rw [List.length_cons, List.length_zipWith] at HφAF HφBF HφCF Hlen1s

        unfold φ
        dsimp
        with_reducible split_ands <;> try solve
          | rfl
          | assumption
          | apply List.prefix_rfl

        -- The hard case
        rotate_right
        apply List.IsPrefix.trans
        exact HφFSD
        apply delay_xor_prefix_r
        assumption

        all_goals (
          unfold List.xor delay
          rw [List.length_cons, List.length_zipWith]
          rw [List.length_cons, List.length_zipWith]
          omega
        )
      . -- Rule 1
        use (fs_s, (aA, aB, aC), (), (oA, aA), (oB, aB), (oCin, aC), fs_c)
        apply And.intro; apply existSR_reflexive

        unfold φ
        dsimp
        with_reducible split_ands <;> try solve
          | rfl
          | assumption
          | apply List.prefix_rfl
      . -- Rule 2
        use (fs_s, (aA, aB, aC), (), (oA, aA), (oB, aB), (oCin, aC), fs_c)
        apply And.intro; apply existSR_reflexive

        unfold φ
        dsimp
        with_reducible split_ands <;> try solve
          | rfl
          | assumption
          | apply List.prefix_rfl
      . -- Rule 3 (due to sink)
        use (fs_s, (aA, aB, aC), (), (oA, aA), (oB, aB), (oCin, aC), fs_c)
        apply And.intro; apply existSR_reflexive
        unfold φ
        dsimp
        with_reducible split_ands <;> try solve
        | rfl
        | assumption

theorem refines_init :
  Module.refines_initial full_adder_imp full_adder_spec φ := by
  unfold Module.refines_initial; intro i hi
  obtain ⟨⟨a, b⟩, ⟨⟩, ⟨c, d⟩, ⟨e, f⟩⟩ := i
  unfold full_adder_imp half_adder_m or_m sink_m at hi
  dsimp at hi
  obtain ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩ := hi
  use ⟨default, default⟩
  apply And.intro
  . unfold full_adder_spec buffer_spec_m future_sight_m full_adder_spec_m
    dsimp
    trivial
  . unfold φ
    dsimp
    with_reducible split_ands

    all_goals try solve
    | rfl
    | apply List.nil_prefix
    | unfold default instInhabitedList; dsimp; omega
    -- We could use some lemmas but this is fine too
    unfold default instInhabitedList adcb
    dsimp
    split_ands
    . omega
    . unfold filter_window3 filter_window
      dsimp
    . intros
      rfl

theorem refines :
  full_adder_imp ⊑ full_adder_spec := ⟨inferInstance, φ, refines', refines_init⟩

end FullAdder
-/

end Graphiti.CombModule
