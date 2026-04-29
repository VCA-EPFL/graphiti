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
variable {α : Type _}

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
    (filter_window delay a)[i]? = some (Bool.and (i >= delay) (((a.take (i + 1)).drop (i + 1 - delay)).all
      (fun v => some v == a[i]?))) := by
        unfold filter_window; grind;

theorem filter_window_get_prefix [BEq α] (delay : Nat) (s1 s2 : List α)
    (h : s1 <+: s2) (i : Nat) (hi : i < s1.length) :
    (filter_window delay s1)[i]? = (filter_window delay s2)[i]? := by
      obtain ⟨t, ht⟩ := h;
      rw [ ← ht, filter_window_get, filter_window_get ];
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

def not (s : List Bool) : List Bool := s.map Bool.not
def and (s1 s2 : List Bool) : List Bool := List.zipWith Bool.and s1 s2
def or (s1 s2 : List Bool) : List Bool := List.zipWith Bool.or s1 s2
def xor (s1 s2 : List Bool) : List Bool := List.zipWith Bool.xor s1 s2
def nand (s1 s2 : List Bool) : List Bool := not <| and s1 s2

def and3 (s1 s2 s3 : List Bool) : List Bool := List.zipWith Bool.and s1 (List.zipWith Bool.and s2 s3)
def xor3 (s1 s2 s3 : List Bool) : List Bool := List.zipWith Bool.xor s1 (List.zipWith Bool.xor s2 s3)
def nand3 (s1 s2 s3 : List Bool) : List Bool := not <| and3 s1 s2 s3

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
/-
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
    q_bar [type="io"];

    n1 [type="nand_m1", typeImp = $(⟨_, nand_sm "nand1"⟩)];
    n2 [type="nand_m2", typeImp = $(⟨_, nand_sm "nand2"⟩)];
    n3 [type="nand3_m", typeImp = $(⟨_, nand3_sm⟩)];
    n4 [type="nand_m3", typeImp = $(⟨_, nand_sm "nand3"⟩)];
    n5 [type="nand_m4", typeImp = $(⟨_, nand_sm "nand4"⟩)];
    n6 [type="nand_m5", typeImp = $(⟨_, nand_sm "nand5"⟩)];

    clkF [type="clkF", typeImp = $(⟨_, fork_sm "clkF"⟩)];
    n2F [type="fork3_m", typeImp = $(⟨_, fork3_sm⟩)];
    n3F [type="n3_f", typeImp = $(⟨_, fork_sm "n3_f"⟩)];
    n4F [type="n4_f", typeImp = $(⟨_, fork_sm "n4_f"⟩)];
    n5F [type="n5_f", typeImp = $(⟨_, fork_sm "n5_f"⟩)];
    n6F [type="n6_f", typeImp = $(⟨_, fork_sm "n6_f"⟩)];

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
    n6F -> q_bar [from="out2"];
  ]

#check ExprHigh
#eval repr <| et_flip_flop_m.1
#eval repr <| et_flip_flop_m.2.toList.map Prod.fst

def env' := env.cons "d_latch_m" d_latch_m_template

def et_flip_flop_spec : StringModule (D × D) :=
  { inputs := [ (↑"clk", ⟨ D, λ s tt s' => True ⟩)
              , (↑"d", ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    outputs := [ (↑"q", ⟨ D, λ s tt s' => True ⟩)
               , (↑"q_bar", ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    init_state := λ s => s = default
  }

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

#eval IO.print <| build_verilog_module "d_latch_m" env d_latch_m.1 (simple_interface ["d", "clk"] ["q", "q_bar"])
-- #guard_msgs (drop info) in
#eval IO.print <| build_verilog_module "et_flip_flop_m" env et_flip_flop_m.1 (simple_interface ["d", "clk"] ["q", "q_bar"])
#guard_msgs (drop info) in
#eval IO.print <| build_verilog_module "et_ms_flip_flop_m" env' et_ms_flip_flop_m.1 (simple_interface ["d", "clk"] ["q", "q_bar"])

namespace Refinement

def et_flip_flop_m_lowered := et_flip_flop_m.1.lower_TR |>.get rfl

#eval et_flip_flop_m_lowered
#check ExprLow

def env := (et_flip_flop_m).2

@[drenv] theorem find?_nand1_m : (Batteries.AssocList.find? "nand_m1" env) = .some ⟨_, nand_sm "nand1"⟩ := rfl
@[drenv] theorem find?_nand2_m : (Batteries.AssocList.find? "nand_m2" env) = .some ⟨_, nand_sm "nand2"⟩ := rfl
@[drenv] theorem find?_nand3_m : (Batteries.AssocList.find? "nand_m3" env) = .some ⟨_, nand_sm "nand3"⟩ := rfl
@[drenv] theorem find?_nand4_m : (Batteries.AssocList.find? "nand_m4" env) = .some ⟨_, nand_sm "nand4"⟩ := rfl
@[drenv] theorem find?_nand5_m : (Batteries.AssocList.find? "nand_m5" env) = .some ⟨_, nand_sm "nand5"⟩ := rfl
@[drenv] theorem find?_nand_3_m : (Batteries.AssocList.find? "nand3_m" env) = .some ⟨_, nand3_sm⟩ := rfl
@[drenv] theorem find?_clkF_m : (Batteries.AssocList.find? "clkF" env) = .some ⟨_, fork_sm "clkF"⟩ := rfl
@[drenv] theorem find?_n3_f_m : (Batteries.AssocList.find? "n3_f" env) = .some ⟨_, fork_sm "n3_f"⟩ := rfl
@[drenv] theorem find?_n4_f_m : (Batteries.AssocList.find? "n4_f" env) = .some ⟨_, fork_sm "n4_f"⟩ := rfl
@[drenv] theorem find?_n5_f_m : (Batteries.AssocList.find? "n5_f" env) = .some ⟨_, fork_sm "n5_f"⟩ := rfl
@[drenv] theorem find?_n6_f_m : (Batteries.AssocList.find? "n6_f" env) = .some ⟨_, fork_sm "n6_f"⟩ := rfl
-- @[drenv] theorem find?_fork_m : (Batteries.AssocList.find? "fork_m" env) = .some ⟨_, fork_sm⟩ := rfl
@[drenv] theorem find?_fork3_m : (Batteries.AssocList.find? "fork3_m" env) = .some ⟨_, fork3_sm⟩ := rfl

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

instance : MatchInterface lhsModule et_flip_flop_spec := by
  dsimp [lhsModule, et_flip_flop_spec]
  solve_match_interface
def φ : lhsModuleType → (D × D) → Prop :=
  λ (_, _, _, _, (_, dataL), _, _, _, _, clkL, _) (clk, data) =>
    -- First, extract the state
    dataL = data /\ clkL = clk
    -- Second, invariants
    -- Non-mathematically, our current ideas are the following two invariants:
    -- 1: the output state is at most the length of the input + delay
    -- 2: the function defined by the input is more defined than the output

theorem refines' :
  lhsModule ⊑_{φ} et_flip_flop_spec := by
    intro lhsModule rhsModule inv
    unfold φ at inv
    let (n2, n4, n5, n4_f, (n3i1, dataL), n3_f, n6_f, n1, n3_1, clkL, n5_f) := lhsModule
    let (clk, data) := rhsModule
    clear lhsModule rhsModule
    simp at inv
    apply Module.comp_refines.mk
    . -- Inputs
      intros inport targetLhs invalue h
      -- unfold lhsModuleType at lhsState
      sorry
    . -- Outputs
      sorry
    . -- Internals
      sorry

theorem refines :
  lhsModule ⊑ et_flip_flop_spec := by sorry

end Refinement

end FlipFlop
-/

namespace HalfAdder

open List

/--
Equivalent to just xor.
-/
def half_adder_s := [graphEnv|
    a [type="io"];
    b [type="io"];
    s [type="io"];

    n1 [type="nand_m_1", typeImp=$(⟨_, nand_sm "nand_1"⟩)];
    n2 [type="nand_m_2", typeImp=$(⟨_, nand_sm "nand_2"⟩)];
    n3 [type="nand_m_3", typeImp=$(⟨_, nand_sm "nand_3"⟩)];
    n4 [type="nand_m_4", typeImp=$(⟨_, nand_sm "nand_4"⟩)];

    a_f [type="fork_m_1", typeImp=$(⟨_, fork_sm "a_f"⟩)];
    b_f [type="fork_m_2", typeImp=$(⟨_, fork_sm "b_f"⟩)];
    n1_f [type="fork_m_3", typeImp=$(⟨_, fork_sm "n1_f"⟩)];

    a -> a_f [to="in1"];
    b -> b_f [to="in1"];
    n1 -> n1_f [from="out1",to="in1"];

    a_f -> n1 [from="out2",to="in1"];
    b_f -> n1 [from="out1",to="in2"];
    a_f -> n2 [from="out1",to="in1"];
    b_f -> n3 [from="out2",to="in2"];

    n1_f -> n2 [from="out1",to="in2"];
    n1_f -> n3 [from="out2",to="in1"];

    n2 -> n4 [from="out1",to="in1"];
    n3 -> n4 [from="out1",to="in2"];

    n4 -> s [from="out1"];
  ]

def half_adder_s_lowered := half_adder_s.1.lower_TR |>.get rfl

def xor_with_delay : StringModule (D × D) where
  inputs := [ (↑"a", ⟨ D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)
            , (↑"b", ⟨ D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)
            ].toAssocList
  outputs := [ (↑"s", ⟨ D, λ s tt s' => tt = delayN 4 false (List.xor s.1 s.2) ∧ s = s' ⟩)].toAssocList
  internals := []
  init_state s := s = ([], [])

def env := half_adder_s.2

@[drenv] theorem find?_nand1_m : (Batteries.AssocList.find? "nand_m_1" env) = .some ⟨_, nand_sm "nand_1"⟩ := rfl
@[drenv] theorem find?_nand2_m : (Batteries.AssocList.find? "nand_m_2" env) = .some ⟨_, nand_sm "nand_2"⟩ := rfl
@[drenv] theorem find?_nand3_m : (Batteries.AssocList.find? "nand_m_3" env) = .some ⟨_, nand_sm "nand_3"⟩ := rfl
@[drenv] theorem find?_nand4_m : (Batteries.AssocList.find? "nand_m_4" env) = .some ⟨_, nand_sm "nand_4"⟩ := rfl
@[drenv] theorem find?_fork1_m : (Batteries.AssocList.find? "fork_m_1" env) = .some ⟨_, fork_sm "a_f"⟩ := rfl
@[drenv] theorem find?_fork2_m : (Batteries.AssocList.find? "fork_m_2" env) = .some ⟨_, fork_sm "b_f"⟩ := rfl
@[drenv] theorem find?_fork3_m : (Batteries.AssocList.find? "fork_m_3" env) = .some ⟨_, fork_sm "n1_f"⟩ := rfl

seal env in
def_module half_adder_m_t : Type :=
  [T| half_adder_s_lowered, env.find? ]
reduction_by
  dsimp [half_adder_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env in
def_module half_adder_m : StringModule half_adder_m_t :=
  [e| half_adder_s_lowered, env.find? ]
reduction_by
       dsimp [half_adder_s_lowered]
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

instance : MatchInterface half_adder_m xor_with_delay := by
  dsimp [half_adder_m, xor_with_delay]
  solve_match_interface

axiom φ : half_adder_m_t → (D × D) → Prop

theorem refines' :
  half_adder_m ⊑_{φ} xor_with_delay := by sorry

theorem refines :
  half_adder_m ⊑ xor_with_delay := by sorry

end HalfAdder

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

macro "destruct_ands_eqs" : tactic =>
  `(tactic| with_reducible repeat cases ‹_ ∧ _›; subst_vars; with_reducible repeat cases ‹_ = _›)


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
              (by unfold full_adder_spec Module.internals; dsimp; omega)

             unfold full_adder_spec Module.internals Module.liftR Module.liftL Named; dsimp

             by_cases Hneq: $t
             (left; subst Hneq; rfl)
             right
            ))

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

end Graphiti.CombModule
