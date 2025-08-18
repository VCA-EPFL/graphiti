/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import Graphiti.Core.Simp
import Graphiti.Core.Module
import Graphiti.Core.ModuleReduction
import Graphiti.Core.ExprLow
import Graphiti.Core.Component
import Graphiti.Core.KernelRefl
import Graphiti.Core.Reduce
import Graphiti.Core.List
import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Tactic
import Graphiti.Core.Rewrites.JoinRewrite
import Mathlib.Tactic
import Graphiti.Core.Environment
import Graphiti.Core.WellTyped

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace Graphiti.JoinRewrite2

open StringModule

class Environment (lhs : Vector Nat 2 → ExprLow String (String × Nat)) where
  ε : FinEnv String (String × Nat)
  h_wf : ∀ s, Env.well_formed ε.find? s
  types : Vector Nat 2
  h_wt : (lhs types).well_typed ε.find?
  max_type : Nat

@[drunfold_defs]
def lhs (types : Vector Nat 2) : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join1 [type = "join", arg = $(types[0])];
    join2 [type = "join", arg = $(types[1])];

    i_0 -> join1 [to = "in1"];
    i_1 -> join1 [to = "in2"];
    i_2 -> join2 [to = "in2"];

    join1 -> join2 [from = "out1", to = "in1"];

    join2 -> o_out [from = "out1"];
  ]

@[drunfold_defs]
def lhs_extract types := (lhs types).extract ["join1", "join2"] |>.get rfl

@[drunfold_defs]
def lhsLower types := (lhs_extract types).fst.lower_TR.get rfl

variable [e : Environment lhsLower]

@[drunfold_defs]
def rhs (max_type : Nat) : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join1 [type = "join", arg = $(max_type+3)];
    join2 [type = "join", arg = $(max_type+2)];
    pure [type = "pure", arg = $(max_type+1)];

    i_1 -> join1 [to = "in1"];
    i_2 -> join1 [to = "in2"];
    i_0 -> join2 [to = "in1"];

    join1 -> join2 [from = "out1", to = "in2"];
    join2 -> pure [from = "out1", to = "in1"];

    pure -> o_out [from = "out1"];
  ]

example : True := by grind

theorem join_s1 : ∃ (T : Type _ × Type _), e.ε.find? ("join", e.types[0]) = some (⟨_, join T.1 T.2⟩) := by
  have h_wf := e.h_wf "join"
  have h_wt := e.h_wt
  dsimp [Env.well_formed] at h_wf
  simp only at h_wf
  dsimp -failIfUnchanged [drunfold_defs, ExprHigh.well_typed, toString, reduceAssocListfind?, reduceListPartition] at h_wt
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wt
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wt
  obtain ⟨hl1, hsome, hwt⟩ := h_wt; cases hsome
  dsimp [ExprLow.well_typed, ExprHigh.uncurry, ExprLow.build_module_interface] at hwt
  -- obtain ⟨-, mi, T, hsome, hfind1, hfind2⟩ := hwt
  simp only [Option.bind_eq_some,Option.map_eq_some] at hwt

  obtain ⟨int, hsome1, hsome2⟩ := hsome
  split at hsome1 <;> try contradiction
  cases hsome1; clear hsome2
  specialize h_wf _ _ ‹_›
  rename_i mod heq
  obtain ⟨T, hmod⟩ := h_wf
  exists T; rw [heq, hmod]

include h_wf h_wt in
theorem join_s2 : ∃ (T : Type _ × Type _), ε.find? ("join", types[1]) = some (⟨_, join T.1 T.2⟩) := by
  specialize h_wf "join"
  dsimp [Env.well_formed] at h_wf
  simp only at h_wf
  dsimp -failIfUnchanged [drunfold_defs, ExprHigh.well_typed, toString, reduceAssocListfind?, reduceListPartition] at h_wt
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wt
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wt
  obtain ⟨hl1, hsome, hwt⟩ := h_wt; cases hsome
  dsimp [ExprLow.well_typed, ExprHigh.uncurry, ExprLow.build_module_interface] at hwt
  obtain ⟨-, mi, T, hsome, hfind1, hfind2⟩ := hwt
  rw [Option.bind_eq_some] at hsome
  obtain ⟨int, hsome1, hsome2⟩ := hsome
  split at hsome1 <;> try contradiction
  cases hsome1
  rw [Option.bind_eq_some] at hsome2
  obtain ⟨int', hsome1', hsome2'⟩ := hsome2
  cases hsome2'
  split at hsome1' <;> try contradiction
  specialize h_wf _ _ ‹_›
  rename_i mod heq
  obtain ⟨T, hmod⟩ := h_wf
  exists T; rw [heq, hmod]

noncomputable def T1 : Type _ × Type _ := Exists.choose (join_s1 ε h_wf S1 S2 h_wt)
noncomputable def T2 : Type _ × Type _ := Exists.choose (join_s2 ε h_wf S1 S2 h_wt)

@[drenv]
theorem join_s1_ex : ε.find? ("join", S1) = some (⟨_, join (T1 ε h_wf S1 S2 h_wt).1 (T1 ε h_wf S1 S2 h_wt).2⟩) :=
  Exists.choose_spec (join_s1 ε h_wf S1 S2 h_wt)

theorem join_s2_ex : ε.find? ("join", S2) = some (⟨_, join (T2 ε h_wf S1 S2 h_wt).1 (T2 ε h_wf S1 S2 h_wt).2⟩) :=
  Exists.choose_spec (join_s2 ε h_wf S1 S2 h_wt)

include h_wf h_wt in
theorem types_unify : ((T1 ε h_wf S1 S2 h_wt).1 × (T1 ε h_wf S1 S2 h_wt).2) = (T2 ε h_wf S1 S2 h_wt).1 := by
  have h_wt' := h_wt
  dsimp -failIfUnchanged [drunfold_defs, ExprHigh.well_typed, toString, reduceAssocListfind?, reduceListPartition] at h_wt
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wt
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wt
  obtain ⟨hl1, hsome, hwt⟩ := h_wt; cases hsome
  dsimp [ExprLow.well_typed, ExprHigh.uncurry, ExprLow.build_module_interface] at hwt
  rw [join_s1_ex ε h_wf S1 S2 h_wt', join_s2_ex ε h_wf S1 S2 h_wt'] at hwt; dsimp at hwt
  obtain ⟨-, mi, T, hsome, hfind1, hfind2⟩ := hwt
  cases hsome
  dsimp [drcomponents] at hfind1 hfind2
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?] at hfind1 hfind2
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert] at hfind1 hfind2
  cases hfind1; rwa [_root_.Option.some_inj] at hfind2

@[drenv]
theorem join_s2_ex' : ε.find? ("join", S2) = some (⟨_, join ((T1 ε h_wf S1 S2 h_wt).1 × (T1 ε h_wf S1 S2 h_wt).2) (T2 ε h_wf S1 S2 h_wt).2⟩) := by
  rw [join_s2_ex ε h_wf S1 S2 h_wt]
  rw [types_unify]

def ε_rhs : FinEnv String (String × Nat) :=
  ([ (("pure", ε.max_type+1), ⟨_, pure (λ ((a, b, c) : ((T1 ε h_wf S1 S2 h_wt).1 × ((T1 ε h_wf S1 S2 h_wt).2 × (T2 ε h_wf S1 S2 h_wt).2))) => ((a, b), c))⟩)
   , (("join", ε.max_type+3), ⟨_, join (T1 ε h_wf S1 S2 h_wt).2 (T2 ε h_wf S1 S2 h_wt).2⟩)
   , (("join", ε.max_type+2), ⟨_, join (T1 ε h_wf S1 S2 h_wt).1 ((T1 ε h_wf S1 S2 h_wt).2 × (T2 ε h_wf S1 S2 h_wt).2)⟩)
   ].toAssocList)

def ε_total : FinEnv String (String × Nat) := ε ++ (ε_rhs ε h_wf S1 S2 h_wt)

@[drunfold_defs]
def rhs_extract := (rhs max_type).extract ["pure", "join1", "join2"] |>.get rfl

@[drunfold_defs]
def rhsLower := (rhs_extract max_type).fst.lower_TR.get rfl

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    pattern := sorry,
    rewrite := λ | [S1, S2] => do
      let n ← get
      return ⟨lhsLower S1.2 S2.2, rhsLower n.fresh_type ⟩ | _ => throw (.error "incorrect number of parameters")
    fresh_types := 3
  }

def_module lhsModuleType : Type :=
  [T| lhsLower S1 S2, ε.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  rw [join_s1_ex ε h_wf S1 S2 h_wt, join_s2_ex' ε h_wf S1 S2 h_wt]
  dsimp

def_module lhsModule : StringModule (lhsModuleType ε h_wf S1 S2 h_wt) :=
  [e| lhsLower S1 S2, ε.find? ]
reduction_by
  (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
   dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
   dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
   rw [rw_opaque (by rw [join_s1_ex ε h_wf S1 S2 h_wt, join_s2_ex' ε h_wf S1 S2 h_wt])]; dsimp
   dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
   simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
   dsimp [Module.product]
   dsimp only [reduceModuleconnect'2]
   dsimp only [reduceEraseAll]
   dsimp; dsimp [reduceAssocListfind?]

   unfold Module.connect''
   dsimp [Module.liftL, Module.liftR, drcomponents])

theorem lhsModule_eq : (⟨_, [e| lhsLower S1 S2, ε.find? ]⟩ : TModule1 String) = ⟨_, lhsModule ε h_wf S1 S2 h_wt⟩ := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  rw [join_s1_ex ε h_wf S1 S2 h_wt, join_s2_ex' ε h_wf S1 S2 h_wt]
  rfl

def env := (ε_rhs ε h_wf S1 S2 h_wt).find?

@[drenv]
theorem env1 : env ε h_wf S1 S2 h_wt ("pure", ε.max_type+1) =
  some ⟨_, pure (λ ((a, b, c) : ((T1 ε h_wf S1 S2 h_wt).1 × ((T1 ε h_wf S1 S2 h_wt).2 × (T2 ε h_wf S1 S2 h_wt).2))) => ((a, b), c))⟩ := by
  unfold env ε_rhs; simp

@[drenv]
theorem env2 : env ε h_wf S1 S2 h_wt ("join", ε.max_type+2) =
  some ⟨_, join (T1 ε h_wf S1 S2 h_wt).1 ((T1 ε h_wf S1 S2 h_wt).2 × (T2 ε h_wf S1 S2 h_wt).2)⟩ := by
  unfold env ε_rhs; simp

@[drenv]
theorem env3 : env ε h_wf S1 S2 h_wt ("join", ε.max_type+3) =
  some ⟨_, join (T1 ε h_wf S1 S2 h_wt).2 (T2 ε h_wf S1 S2 h_wt).2⟩ := by
  unfold env ε_rhs; simp

def_module rhsModuleType : Type :=
  [T| rhsLower ε.max_type, env ε h_wf S1 S2 h_wt ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

def_module rhsModule : StringModule (rhsModuleType ε h_wf S1 S2 h_wt) :=
  [e| rhsLower ε.max_type, env ε h_wf S1 S2 h_wt ]

theorem rhsModule_eq : (⟨_, [e| rhsLower ε.max_type, env ε h_wf S1 S2 h_wt ]⟩ : TModule1 String) = ⟨_, rhsModule ε h_wf S1 S2 h_wt⟩ := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  rw [env1,env2,env3]
  rfl

instance : MatchInterface (rhsModule ε h_wf S1 S2 h_wt) (lhsModule ε h_wf S1 S2 h_wt) := by
  dsimp [rhsModule, lhsModule]; solve_match_interface

@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

theorem sigma_rw_simp {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by simp [drunfold,drcompute,seval]; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

inductive partially

inductive partially_flushed: lhsModuleType ε h_wf S1 S2 h_wt -> Prop where
| lhs: ∀ lower arb, partially_flushed ⟨lower, [], arb⟩
| rhs: ∀ lower arb, partially_flushed ⟨lower, arb, []⟩

def ψ (rhs : rhsModuleType ε h_wf S1 S2 h_wt) (lhs : lhsModuleType ε h_wf S1 S2 h_wt) : Prop :=
  let ⟨⟨j2l, j2r⟩, ⟨j1l, j1r⟩⟩ := lhs
  let ⟨⟨j2l', j2r'⟩, ⟨⟨j1l', j1r'⟩, p⟩⟩ := rhs
  (j2l.map Prod.fst ++ j1l = p.map (Prod.fst ∘ Prod.fst) ++ j2l') ∧
  (j2l.map Prod.snd ++ j1r = p.map ((Prod.snd ∘ Prod.fst)) ++ j2r'.map Prod.fst ++ j1l') ∧
  (j2r = p.map Prod.snd ++ j2r'.map Prod.snd ++ j1r')

-- TODO: Can I write differently the lambda that extract the element from p's queue
def φ (rhs : rhsModuleType ε h_wf S1 S2 h_wt) (lhs : lhsModuleType ε h_wf S1 S2 h_wt) : Prop :=
  (ψ ε h_wf S1 S2 h_wt rhs lhs) ∧ (partially_flushed ε h_wf S1 S2 h_wt lhs)

theorem something':
  ∀ s, ∃ s', existSR (lhsModule ε h_wf S1 S2 h_wt).internals s s' ∧ partially_flushed ε h_wf S1 S2 h_wt s' := by
  intro ⟨⟨l1, l2⟩, ⟨l3, l4⟩⟩
  induction l3 generalizing l1 l2 l4 with
  | nil =>
    apply Exists.intro
    and_intros
    . apply existSR_reflexive
    . constructor
  | cons x xs ih =>
    cases l4
    . apply Exists.intro
      and_intros
      . apply existSR_reflexive
      . constructor
    . rename_i head tail
      specialize ih (l1 ++ [(x, head)]) l2 tail
      obtain ⟨ ⟨⟨_, _⟩, ⟨_, _⟩⟩, HExists, HPartiallyFlushed⟩ := ih
      apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
      and_intros
      . apply existSR.step _ ⟨ ⟨ _, _ ⟩, _, _ ⟩ _
        . unfold lhsModule; simp
          rfl
        . repeat apply Exists.intro
          and_intros <;> rfl
        . apply HExists
      . assumption

theorem something:
  ∀ i s s', ψ ε h_wf S1 S2 h_wt i s → existSR (lhsModule ε h_wf S1 S2 h_wt).internals s s' → ψ ε h_wf S1 S2 h_wt i s' := by
  intro ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ s s' Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold lhsModule at Hrule; simp at Hrule
    subst_vars
    obtain ⟨_, _, _, _, _, _, _, _⟩ := c
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
    rename_i a _ _ _ _ _ b; simp at a b
    obtain ⟨ ⟨_, _⟩, ⟨_, _⟩⟩ := a
    obtain ⟨ ⟨_, _⟩ , ⟨_, _⟩⟩ := b
    unfold ψ at *; simp at *
    subst_vars
    obtain ⟨ _, ⟨_, _⟩ ⟩ := Hψ
    simp; and_intros <;> assumption

theorem something'':
  ∀ i i' s, ψ ε h_wf S1 S2 h_wt i s → existSR (rhsModule ε h_wf S1 S2 h_wt).internals i i' → ψ ε h_wf S1 S2 h_wt i' s := by
  intro i i' ⟨⟨_, _⟩, ⟨_, _⟩⟩ Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold rhsModule at Hrule; simp at Hrule
    cases Hrule <;> subst_vars
    . obtain ⟨_, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨_, _⟩, _⟩ := c
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _⟩ := synth2
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> try simp
      . assumption
      . rename_i synth1 _ _ _ _ _ _
        rw [<- synth1]; subst_vars
        assumption
      . assumption
    . obtain ⟨_, _, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩ := c
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _⟩ := synth2
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> simp
      . assumption
      . assumption

theorem s' (i i': rhsModuleType ε h_wf S1 S2 h_wt) :
  ∀ rule, rule ∈ (rhsModule ε h_wf S1 S2 h_wt).internals ∧ rule i i' → existSR (rhsModule ε h_wf S1 S2 h_wt).internals i i' := by
    intro rule ⟨_, _⟩
    apply existSR.step i i' i' rule
    . assumption
    . assumption
    . exact existSR_reflexive

theorem lengthify {T₁: Type _} (a b: List T₁): a = b → a.length = b.length := by
  intro heq; rw [heq]

theorem takify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.take l l₁ = List.take l l₂ := by
  intro heq; rw [heq]

theorem dropify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.drop l l₁ = List.drop l l₂ := by
  intro heq; rw [heq]

theorem product_is_list_zip {T₁ T₂: Type _} (x: List (T₁ × T₂)): x = List.zip (List.map Prod.fst x) (List.map Prod.snd x) := by
  induction x with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.zip_cons_cons, <- ih]

theorem append_iff {α} {a b c d : List α} : a.length = c.length → (a ++ b = c ++ d ↔ a = c ∧ b = d) := by
  intro lengths
  constructor
  . intro h
    and_intros
    . replace h := congrArg (List.take a.length) h
      rw [List.take_left, lengths, List.take_left] at h
      assumption
    . apply dropify a.length at h
      rw [List.drop_left, lengths, List.drop_left] at h
      assumption
  . intro ⟨_, _⟩; subst_vars; rfl

seal T1 T2 in
theorem refines {T: Type _} [DecidableEq T]: rhsModule ε h_wf S1 S2 h_wt ⊑_{φ ε h_wf S1 S2 h_wt} lhsModule ε h_wf S1 S2 h_wt := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule ε h_wf S1 S2 h_wt).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i
      unfold rhsModule at HContains; simp at HContains

      rcases HContains with h | h | h
        <;> subst_vars <;> simp <;> rw [PortMap.rw_rule_execution] at a <;> simp at a
      . obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        have_hole heq : ((rhsModule ε h_wf S1 S2 h_wt).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp
        . -- verify that the invariant holds when we flush the system
          obtain ⟨s', ⟨_, _⟩⟩ := something' ε h_wf S1 S2 h_wt ((sj2l, sj2r), sj1l ++ [heq.mp s], sj1r) -- We flush the system to reach s'
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something ε h_wf S1 S2 h_wt _ (⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . simp only [<- List.append_assoc, List.append_left_inj]
                  assumption
                . assumption
                . rfl
              . assumption
            . assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := something' ε h_wf S1 S2 h_wt ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something ε h_wf S1 S2 h_wt _ (⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
                  assumption
                . rfl
              . assumption
            . assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r ++ [s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := something' ε h_wf S1 S2 h_wt ⟨⟨sj2l, sj2r ++ [s]⟩, sj1l, sj1r⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something ε h_wf S1 S2 h_wt _ (⟨sj2l, sj2r  ++ [s]⟩, sj1l, sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
              . assumption
            . assumption
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule ε h_wf S1 S2 h_wt).outputs.contains ident)
    · obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨ij2l, ij2r⟩, ⟨ij1l, ij1r⟩, ip⟩ := init_i
      obtain ⟨⟨ij2l', ij2r'⟩, ⟨ij1l', ij1r'⟩, ip'⟩ := i
      unfold rhsModule at HContains; simp at HContains
      rcases HContains with h <;> subst_vars
      <;> simp <;>
      rw [PortMap.rw_rule_execution (by simp [PortMap.getIO]; rfl)] at hrule <;>
      simp at hrule
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := hrule
      repeat cases ‹_∧_›
      subst_vars
      rename_i hlval hrval hpf
      dsimp at *
      rename_i htmp; cases htmp
      cases hpf
      · simp at hlval; simp at *
        rw [<- List.take_append_drop ij2l.length (List.map Prod.fst ij2r ++ ij1l)] at hrval
        --rw [<- List.append_assoc (List.map (Prod.snd ∘ Prod.fst) ip')] at hrval
        --rw [<- List.append.eq_2 _ _ ((List.map (Prod.snd ∘ Prod.fst) ip' ++ List.take ij2l.length (List.map Prod.fst ij2r' ++ ij1l'))] at hrval
        rw [show v.1.2 ::
            (List.map (Prod.snd ∘ Prod.fst) ip' ++
              (List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l) ++
                List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l))) = v.1.2 ::
            (List.map (Prod.snd ∘ Prod.fst) ip' ++
              List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l)) ++
                List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l) by simp] at hrval
        rw [append_iff] at hrval
        obtain ⟨hrvall, _⟩ := hrval
        . subst_vars
          apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
          and_intros <;> dsimp
          · apply existSR.done
          · apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩; and_intros <;> dsimp
            · rewrite [product_is_list_zip sj2l, hlval, hrvall]; rfl
            · apply lengthify at hlval; simp at hlval
              apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
              rw [List.append_nil, <- List.zip_eq_zipWith, List.map_fst_zip]
              simp [hrvall] -- lia + assumption in context
            · apply lengthify at hlval; simp at hlval
              apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
              rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
              . simp only [List.append_assoc, List.take_append_drop]
              . simp only [List.length_append, List.length_map, List.length_take, add_le_add_iff_left, inf_le_left]
            · rewrite [List.append_assoc]; rfl
            · constructor
        . apply lengthify at hlval; simp at hlval
          apply lengthify at hrval; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrval
          simp only [hlval, List.length_map, List.length_cons, List.length_append, List.length_take,
            add_left_inj, add_right_inj, left_eq_inf] -- lengthify the goal
          simp only [le_iff_exists_add, <- hrval, add_right_inj, exists_eq'] -- lia
      . simp at hrval; simp at *
        rw [<- List.take_append_drop (ij2r.length + ij1l.length) ij2l] at hlval
        rw [show v.1.1 ::
            (List.map (Prod.fst ∘ Prod.fst) ip' ++
              (List.take (ij2r.length + ij1l.length) ij2l ++
                List.drop (ij2r.length + ij1l.length) ij2l)) = v.1.1 ::
            (List.map (Prod.fst ∘ Prod.fst) ip' ++
              List.take (ij2r.length + ij1l.length) ij2l) ++
                List.drop (ij2r.length + ij1l.length) ij2l by simp] at hlval
        rw [append_iff] at hlval
        obtain ⟨hlvall, hlvalr⟩ := hlval
        . subst_vars
          apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
          . and_intros <;> dsimp
            · apply existSR.done
            · apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩; and_intros <;> dsimp
              . rewrite [product_is_list_zip sj2l, hrval, hlvall]; rfl
              . apply lengthify at hrval; simp at hrval
                apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
                simp [<- List.zip_eq_zipWith, List.map_fst_zip, hlvall]
              . apply lengthify at hrval; simp at hrval
                apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
                rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
                . simp
                . simp [hlvall]
              . simp
              . constructor
        . apply lengthify at hrval; simp [add_comm _ 1, add_right_inj, add_assoc] at hrval
          apply lengthify at hlval; simp [hrval, add_comm _ 1, add_left_inj, add_assoc] at hlval
          simp only [hrval, List.length_map, List.length_cons, add_comm _ 1, add_right_inj, List.length_append, List.length_take, left_eq_inf] -- lengthify the goal
          simp only [le_iff_exists_add, <- hlval, add_right_inj, exists_eq', add_assoc] -- lia
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros rule mid_i _ _
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . unfold φ at *
      obtain ⟨_, _⟩ := Hφ
      apply And.intro
      . apply (something'' ε h_wf S1 S2 h_wt init_i)
        . assumption
        . apply s' ε h_wf S1 S2 h_wt init_i mid_i rule
          and_intros <;> assumption
      . assumption

/--
info: 'Graphiti.JoinRewrite2.refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refines

end Graphiti.JoinRewrite2
