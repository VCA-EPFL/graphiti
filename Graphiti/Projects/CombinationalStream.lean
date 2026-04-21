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
    (fun i => ((a.take (i + 1)).drop (i + 1 - delay)).all (fun v => some v == a[i]?))

theorem filter_window_length [BEq α] (delay : Nat) (a : List α) :
    (filter_window delay a).length = a.length := by
      simp [List.length_range, filter_window]

theorem filter_window_nil [BEq α] (delay : Nat) :
    filter_window delay ([] : List α) = [] := by
      rfl

theorem filter_window_get [BEq α] (delay : Nat) (a : List α) (i : Nat)
    (hi : i < a.length) :
    (filter_window delay a)[i]? = some (((a.take (i + 1)).drop (i + 1 - delay)).all
      (fun v => some v == a[i]?)) := by
        unfold filter_window; aesop;

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
        · rw [ List.length_take, filter_window_length, filter_window_length ];
          rw [ min_eq_left ( hs1s2.length_le ) ];
        · intro n hn hn';
          convert filter_window_get_prefix delay s1 s2 hs1s2 n _;
          · grind;
          · exact hn.trans_le ( by simp +decide [ filter_window_length ] );
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

lemma zipWith_prefix.{u, v, w} {α : Type u} {β : Type v} {γ : Type w} :
  ∀f: α → β → γ, ∀ a a': List α, ∀ b : List β,
  a <+: a' → List.zipWith f a b <+: List.zipWith f a' b
  := by
  intros f a a' b H
  revert a' b
  induction a with
  | nil => simp
  | cons hd tl iH =>
    intro a' b H
    rw [List.cons_prefix_iff] at H
    obtain ⟨tl', Ha', H⟩ := H
    subst_vars
    unfold List.zipWith
    cases b
    . simp
    . rename_i bHd bTl
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
  . intro Hzip
    obtain ⟨H, Hneq⟩ := (strict_prefix_iff_prefix_length a a').mp H
    have H : (List.zipWith f a b).length = (List.zipWith f a' b).length := by rw [Hzip]
    rw [List.length_zipWith, List.length_zipWith] at H
    grind

theorem prefix_filter_window_prefix [BEq α] :
  ∀ delay: Nat, ∀ a a' : List α,
  a <+: a' →
  filter_window delay a <+: filter_window delay a'
  := by
  sorry

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

theorem filter_prefix_strict_filtered_prefix :
  ∀ f1 f2, ∀ s1 s2 : List α,
    s1 <<:{f1} s2 →
    f1 <+: f2 →
    s1 <<:{f2} s2
  := by
  sorry

def filtered_eq (filter : List Bool) (s1 s2 : List α) : Prop :=
  s1.length = s2.length ∧ filter.length = s1.length ∧
      (∀ i : Nat, filter[i]? = some true → s1[i]? = s2[i]?)

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

namespace ClkExample

def clk_s := [graphEnv|
    a [type="io"];

]

end ClkExample

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

def half_adder_m (s : String := "") : StringModule (Named s (D × D)) :=
  { inputs := [(↑"a", ⟨ Named s!"{s}.a" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ Named s!"{s}.b" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [ (↑"s", ⟨ Named s!"{s}.s" D, λ s tt s' => s = s' ∧ tt = delay false (xor s.1 s.2) ⟩)
               , (↑"c", ⟨ Named s!"{s}.c" D, λ s tt s' => s = s' ∧ tt = delay false (and s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def or_m (s : String := "") : StringModule (D × D) :=
  { inputs := [(↑"a", ⟨ D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(↑"c", ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (and s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def adcb (a b c : D) : D × D :=
  (List.zipWith3 (fun x y z => (BitVec.adcb x y z).1) a b c, List.zipWith3 (fun x y z => (BitVec.adcb x y z).2) a b c)

def full_adder_spec_m (s : String := "") : StringModule (Named s (D × D × D)) :=
  { inputs := [(↑"a", ⟨ Named s!"{s}.a" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ Named s!"{s}.b" D, λ s tt s' => s.2.1 <<: tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
               (↑"cin", ⟨ Named s!"{s}.c" D, λ s tt s' => s.2.2 <<: tt ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
    outputs := [ (↑"s", ⟨ Named s!"{s}.s" D, λ s tt s' => s = s' ∧ filtered_eq (filter_window3 3 s.1 s.2.1 s.2.2) (adcb s.1 s.2.1 s.2.2).2 tt ⟩)
               , (↑"cout", ⟨ Named s!"{s}.c" D, λ s tt s' => s = s' ∧ filtered_eq (filter_window3 3 s.1 s.2.1 s.2.2) (adcb s.1 s.2.1 s.2.2).1 tt ⟩)].toAssocList
    init_state := λ s => s = default
  }

def buffer_spec_m (s : String := "") : StringModule (Named s (D × D)) :=
 {
  inputs := [(↑"in", ⟨ Named s!"{s}.in" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)].toAssocList,
  outputs := [(↑"out", ⟨ Named s!"{s}.out" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1⟩)].toAssocList,
  init_state := λ s => s = default
 }

 def buffered_full_adder_m := [graphEnv|
  a [type="io"];
  b [type="io"];
  cin [type="io"];
  s [type="io"];
  cout [type="io"];

  fa [type="fa", typeImp=$(⟨_, full_adder_spec_m "fa"⟩)];
  b_1 [type="b_1", typeImp=$(⟨_, buffer_spec_m "b_1"⟩)];
  b_2 [type="b_2", typeImp=$(⟨_, buffer_spec_m "b_2"⟩)];

  a -> fa [to="a"];
  b -> fa [to="b"];
  cin -> fa [to="cin"];

  fa -> b_1 [from="s", to="in"];
  fa -> b_2 [from="cout", to="in"];
  b_1 -> s [from="out"];
  b_2 -> cout [from="out"];
 ]

def buffered_full_adder_m_lowered := buffered_full_adder_m.1.lower_TR |>.get rfl

def env_bfam := buffered_full_adder_m.2

@[drenv] theorem find?_fa_m : (Batteries.AssocList.find? "fa" env_bfam) = .some ⟨_, full_adder_spec_m "fa"⟩ := rfl
@[drenv] theorem find?_b1_m : (Batteries.AssocList.find? "b_1" env_bfam) = .some ⟨_, buffer_spec_m "b_1"⟩ := rfl
@[drenv] theorem find?_b2_m : (Batteries.AssocList.find? "b_2" env_bfam) = .some ⟨_, buffer_spec_m "b_2"⟩ := rfl

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
    cout [type="io"];

    ha1 [type="ha_1", typeImp=$(⟨_, half_adder_m "ha_1"⟩)];
    ha2 [type="ha_2", typeImp=$(⟨_, half_adder_m "ha_2"⟩)];
    or [type="or", typeImp=$(⟨_, or_m⟩)];

    a -> ha1 [to="a"];
    b -> ha1 [to="b"];
    cin -> ha2 [to="a"];
    ha1 -> ha2 [from="s",to="b"];
    ha2 -> s [from="s"];
    ha2 -> or [from="c",to="a"];
    ha1 -> or [from="c",to="b"];
    or -> cout [from="c"];
  ]

def full_adder_s_lowered := full_adder_s.1.lower_TR |>.get rfl

def env_fas := full_adder_s.2

@[drenv] theorem find?_nand1_m : (Batteries.AssocList.find? "ha_1" env_fas) = .some ⟨_, half_adder_m "ha_1"⟩ := rfl
@[drenv] theorem find?_nand2_m : (Batteries.AssocList.find? "ha_2" env_fas) = .some ⟨_, half_adder_m "ha_2"⟩ := rfl
@[drenv] theorem find?_nand3_m : (Batteries.AssocList.find? "or" env_fas) = .some ⟨_, or_m⟩ := rfl

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
  let ((lA, lB), (lCin, ha1s), ha2c, ha1c) := lhs
  let ((bs_in, bs_out), (bc_in, bc_out), (rA, rB, rCin)) := rhs
  let filter := filter_window3 3 rA rB rCin
  -- Input states must be equivalent
  lA = rA ∧ lB = rB ∧ lCin = rCin ∧
  -- Internal connections of the implementation are monotonic (less defined than each other). TODO.
  -- Buffer inputs are more defined, when filtered by rA, rB, rCin.
  is_filtered_strict_prefix filter (delay false (or ha2c ha1c)) bc_in ∧
    is_filtered_strict_prefix filter (delay false (xor lCin ha1s)) bs_in ∧
  -- Outputs are more defined, when filtered by rA, rB, rCin.
  is_filtered_strict_prefix filter bc_out (delay false (or ha2c ha1c)) ∧
    is_filtered_strict_prefix filter bs_out (delay false (xor lCin ha1s))

theorem refines' :
  full_adder_imp ⊑_{φ} full_adder_spec := by
    unfold Module.refines_φ
    intro init_i init_s Hφ
    obtain ⟨⟨lA, lB⟩, ⟨lCin, ha1s⟩, ha2c, ha1c⟩ := init_i
    obtain ⟨⟨bs_in, bs_out⟩, ⟨bc_in, bc_out⟩, ⟨rA, rB, rCin⟩⟩ := init_s
    obtain ⟨HφA, HφB, HφCin, HφBufferInC, HφBufferInS, HφBufferOutC, HφBufferOutS⟩ := Hφ
    subst_vars
    -- TODO: force all of the Streams to be Some (for those that require it)
    -- TODO: rewrite functions that are specific to streams to be wrappers around List ones

    apply Module.comp_refines.mk
    . -- Inputs
      intro ident lhs_out s a

      -- The ident has to resolve to something
      by_cases HContains: (full_adder_imp.inputs.contains ident)
      . -- Unpack initial states for both modules
        -- Split by cases on the port
        unfold full_adder_imp at HContains; simp at HContains
        rcases HContains with h | h | h
        <;> subst_vars <;> simp <;> rw [PortMap.rw_rule_execution] at a <;> simp at a
        . -- Input accepted: a.
          -- Unpack the impact of setting a.
          obtain ⟨⟨a_moredef, ⟨out_has_s, a_ident1⟩⟩, a_ident2⟩ := a
          simp at a_moredef
          simp at a_ident1
          -- Swap out rA in our previous state's definition
          use ⟨⟨bs_in, bs_out⟩, ⟨bc_in, bc_out⟩, ⟨s, rB, rCin⟩⟩
          apply And.intro
          . -- Our new state is valid
            rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
            simp
            constructor
            . simp
              assumption
            . rfl
          . -- Our new state maintains φ
            -- We use the same state with no internal rules
            use ⟨⟨bs_in, bs_out⟩, ⟨bc_in, bc_out⟩, ⟨s, rB, rCin⟩⟩
            apply And.intro
            . exact existSR_reflexive
            . unfold φ
              grind only [filter_prefix_strict_filtered_prefix, filter_window3_prefix_1, prefix_filter_window_prefix, strict_prefix_iff_prefix_length]
        . sorry
        . sorry
      . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
    . -- Outputs
      sorry
    . -- Internals
      sorry

theorem refines :
  full_adder_imp ⊑ full_adder_spec_m := by sorry

end FullAdder

end Graphiti.CombModule
