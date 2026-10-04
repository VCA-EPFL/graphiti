/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Dataflow.Component
public import Graphiti.Core.Graph.ExprLowLemmas
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Graph.ModuleReduction
public import Graphiti.Core.RewriterLemmas

@[expose] public section

namespace Graphiti.LoopRewrite

open Batteries (AssocList)
open StringModule

open Lean hiding AssocList
open Meta Elab

section Proof

@[drunfold_defs]
def lhs (types : Vector Nat 8) : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [type = "mux", arg = $(types[0])];
    condition_fork [type = "fork2", arg = $(types[1])];
    branch [type = "branch", arg = $(types[2])];
    tag_split [type = "split", arg = $(types[3])];
    mod [type = "pure", arg = $(types[4])];
    loop_init [type = "initBool", arg = $(types[5])];
    queue [type = "queue", arg = $(types[6])];
    queue_out [type = "queue", arg = $(types[7])];

    i_in -> mux [to="in2"];
    queue_out -> o_out [from="out1"];

    branch -> queue_out [from="out2", to="in1"];
    queue -> mux [from="out1", to="in3"];
    branch -> queue [from="out1", to="in1"];
    mux -> mod [from="out1", to="in1"];
    tag_split -> condition_fork [from="out2", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    mod -> tag_split [from="out1", to="in1"];
    condition_fork -> branch [from="out1", to="in2"];
    condition_fork -> loop_init [from="out2", to="in1"];
    loop_init -> mux [from="out1", to="in1"];
  ]

@[drunfold_defs]
def lhs_extract types := (lhs types).extract ["queue_out", "queue", "loop_init", "mod", "tag_split", "branch", "condition_fork", "mux"] |>.get rfl

@[drunfold_defs]
def lhsLower types := (lhs_extract types).fst.lower_TR.get rfl

theorem lhsLower_locally_wf {types} : (lhsLower types).locally_wf := rfl

@[drunfold_defs]
def liftF {α β γ δ} (f : α -> β × δ) : γ × α -> (γ × β) × δ | (g, a) => ((g, f a |>.fst), f a |>.snd)

def liftF2 {α β γ δ} (f : α -> β × δ) : α × (Nat × γ) -> (β × (Nat × γ)) × δ
| (a, g) =>
  let b := f a
  ((b.1, (g.1 + 1, g.2)), b.2)

@[drunfold_defs]
def ghost_rhs (max_type : Nat)
    : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [type = $("tagger_untagger_val_ghost"), arg = $(max_type+1)];
    merge [type = $("merge2"), arg = $(max_type+2)];
    branch [type = $("branch"), arg = $(max_type+3)];
    tag_split [type = $("split"), arg = $(max_type+4)];
    mod [type = "pure", arg = $(max_type+5)];

    i_in -> tagger [to="in2"];
    tagger -> o_out [from="out2"];

    branch -> tagger [from="out2", to="in1"];
    branch -> merge [from="out1", to="in1"];
    tag_split -> branch [from="out2", to="in2"];
    tag_split -> branch [from="out1", to="in1"];
    mod -> tag_split [from="out1", to="in1"];
    merge -> mod [from="out1", to="in1"];
    tagger -> merge [from="out1",to="in2"];
  ]

@[drunfold_defs]
def ghost_rhs_extract max_type := ghost_rhs max_type
  |>.extract ["mod", "branch", "merge", "tagger", "tag_split"]
  |>.get rfl

@[drunfold_defs]
def rhsGhostLower max_type := (ghost_rhs_extract max_type |>.1).lower_TR.get rfl

variable [e : Environment Env.well_formed lhsLower]

local instance : BEq (String × Nat) := instBEqOfDecidableEq

/-! ### Left-hand side -/

/--
The environment is arbitrary, but its well-formedness fixes which component each node of the lhs is, and the
well-typedness of the lhs then forces their data types to agree.  The lhs is therefore determined by a data type `T` and
the loop body `f`.
-/
theorem env_types : ∃ (T : Type) (f : T → T × Bool),
    e.ε.find? ("mux", e.types[0]) = some ⟨_, mux T⟩
    ∧ e.ε.find? ("fork2", e.types[1]) = some ⟨_, fork2 Bool⟩
    ∧ e.ε.find? ("branch", e.types[2]) = some ⟨_, branch T⟩
    ∧ e.ε.find? ("split", e.types[3]) = some ⟨_, split T Bool⟩
    ∧ e.ε.find? ("pure", e.types[4]) = some ⟨_, pure f⟩
    ∧ e.ε.find? ("initBool", e.types[5]) = some ⟨_, init Bool false⟩
    ∧ e.ε.find? ("queue", e.types[6]) = some ⟨_, queue T⟩
    ∧ e.ε.find? ("queue", e.types[7]) = some ⟨_, queue T⟩ := by
  -- Elaborating an application `whnf`s its type, which would evaluate `lhsLower` without sharing; the simprocs below
  -- reduce it much faster, so the hypotheses are introduced at reducible transparency.
  with_reducible have hwf := ExprLow.well_formed_wrt_from_well_typed e.h_lhs_wf e.h_wf.h_wf
  dsimp [drunfold_defs, reduceAssocListfind?, reduceExprHighLower, reduceExprHighLowerProdTR,
    reduceExprHighLowerConnTR, ExprHigh.uncurry, ExprLow.well_formed_wrt, Env.well_formed'] at hwf
  simp only at hwf
  obtain ⟨⟨T, h7⟩, ⟨T6, h6⟩, h5, ⟨⟨A, B, g⟩, h4⟩, ⟨⟨S1, S2⟩, h3⟩, ⟨Br, h2⟩, ⟨F, h1⟩, ⟨M, h0⟩⟩ := hwf
  with_reducible have hwt := e.h_lhs_wt
  dsimp [drunfold_defs, reduceAssocListfind?, reduceExprHighLower, reduceExprHighLowerProdTR,
    reduceExprHighLowerConnTR, ExprHigh.uncurry, ExprLow.well_typed, ExprLow.build_module_interface] at hwt
  simp (disch := decide) only [h0, h1, h2, h3, h4, h5, h6, h7, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_and_left, exists_eq_left', AssocList.find?_eraseAll_neq] at hwt
  simp only [reduceAssocListfind?, Option.some.injEq, exists_eq_left', true_and] at hwt
  casesm* _ ∧ _; subst_vars
  exists _, g

def T := env_types.choose
noncomputable def f : T → T × Bool := env_types.choose_spec.choose

@[drenv] theorem lhs_ε_find :
    e.ε.find? ("mux", e.types[0]) = some ⟨_, mux T⟩
    ∧ e.ε.find? ("fork2", e.types[1]) = some ⟨_, fork2 Bool⟩
    ∧ e.ε.find? ("branch", e.types[2]) = some ⟨_, branch T⟩
    ∧ e.ε.find? ("split", e.types[3]) = some ⟨_, split T Bool⟩
    ∧ e.ε.find? ("pure", e.types[4]) = some ⟨_, pure f⟩
    ∧ e.ε.find? ("initBool", e.types[5]) = some ⟨_, init Bool false⟩
    ∧ e.ε.find? ("queue", e.types[6]) = some ⟨_, queue T⟩
    ∧ e.ε.find? ("queue", e.types[7]) = some ⟨_, queue T⟩ :=
  env_types.choose_spec.choose_spec

seal T f in
@[reducible] def_module lhsType : Type :=
  [T| (lhsLower e.types), e.ε.find? ]

seal T f in
noncomputable def_module lhsEvaled : StringModule lhsType :=
  [e| (lhsLower e.types), e.ε.find? ]

seal T f in
theorem lhs_evaled_eq :
    (⟨_, lhsEvaled⟩ : TModule1 String) = ⟨_, [e| (lhsLower e.types), e.ε.toEnv ]⟩ := by
  dr_reduce_module; rfl

/-! ### Right-hand side

The rhs uses fresh types above `e.max_type`, so its environment `ε_rhs_ghost` is independent of `e.ε`.
-/

abbrev TagT := Nat

noncomputable def ε_rhs_ghost : FinEnv String (String × Nat) :=
  ([ (("tagger_untagger_val_ghost", e.max_type+1), ⟨_, StringModule.tagger_untagger_val_ghost TagT T⟩)
   , (("merge2", e.max_type+2), ⟨_, merge ((TagT × T) × (Nat × T)) 2⟩)
   , (("branch", e.max_type+3), ⟨_, branch ((TagT × T) × (Nat × T))⟩)
   , (("split", e.max_type+4), ⟨_, split ((TagT × T) × (Nat × T)) Bool⟩)
   , (("pure", e.max_type+5), ⟨_, StringModule.pure (liftF2 (γ := T) (liftF (γ := TagT) f))⟩)
   ].toAssocList)

@[drenv] theorem ε_rhs_ghost_find :
    ε_rhs_ghost.find? ("tagger_untagger_val_ghost", e.max_type+1) = some ⟨_, StringModule.tagger_untagger_val_ghost TagT T⟩
    ∧ ε_rhs_ghost.find? ("merge2", e.max_type+2) = some ⟨_, merge ((TagT × T) × (Nat × T)) 2⟩
    ∧ ε_rhs_ghost.find? ("branch", e.max_type+3) = some ⟨_, branch ((TagT × T) × (Nat × T))⟩
    ∧ ε_rhs_ghost.find? ("split", e.max_type+4) = some ⟨_, split ((TagT × T) × (Nat × T)) Bool⟩
    ∧ ε_rhs_ghost.find? ("pure", e.max_type+5) = some ⟨_, StringModule.pure (liftF2 (γ := T) (liftF (γ := TagT) f))⟩ := by
  simp [ε_rhs_ghost]

theorem ε_rhs_ghost_wf : ε_rhs_ghost.toEnv.well_formed := by
  rw [Env.well_formed_alt_correct]
  simp [Env.well_formed_alt, Env.well_formed'', ε_rhs_ghost]
  grind

theorem ε_rhs_ghost_independent : e.ε.toEnv.independent ε_rhs_ghost.toEnv := by
  intro n m hfind
  have := FinEnv.max_typeD_none (n := n) e.h_wf.max_is_max
  simp [ε_rhs_ghost]
  grind [FinEnv.toEnv]

seal T f ε_rhs_ghost in
theorem ghost_rhs_wf : (rhsGhostLower e.max_type).well_formed ε_rhs_ghost.toEnv := by
  dsimp [drunfold_defs, reduceAssocListfind?, reduceExprHighLower, reduceExprHighLowerProdTR,
    reduceExprHighLowerConnTR, ExprHigh.uncurry, ExprLow.well_formed]
  simp only [drenv]
  simp [drcomponents, AssocList.keysList, List.range, List.range.loop]
  decide

seal T f ε_rhs_ghost in
theorem ghost_rhs_wt : (rhsGhostLower e.max_type).well_typed ε_rhs_ghost.toEnv := by
  dsimp [drunfold_defs, reduceAssocListfind?, reduceExprHighLower, reduceExprHighLowerProdTR,
    reduceExprHighLowerConnTR, ExprHigh.uncurry, ExprLow.well_typed, ExprLow.build_module_interface]
  simp (disch := decide) only [drenv, Option.map_some, Option.bind_some, Option.some.injEq, exists_and_left,
    exists_eq_left', AssocList.find?_eraseAll_neq]
  simp only [reduceAssocListfind?, Option.some.injEq, exists_eq_left', true_and]

seal T f ε_rhs_ghost in
@[reducible] def_module rhsGhostType : Type :=
  [T| (rhsGhostLower e.max_type), ε_rhs_ghost.toEnv ]

seal T f ε_rhs_ghost in
noncomputable def_module rhsGhostEvaled : StringModule rhsGhostType :=
  [e| (rhsGhostLower e.max_type), ε_rhs_ghost.toEnv ]

seal T f ε_rhs_ghost in
theorem rhs_ghost_evaled_eq :
    (⟨_, rhsGhostEvaled⟩ : TModule1 String) = ⟨_, [e| (rhsGhostLower e.max_type), (e.ε ++ ε_rhs_ghost).toEnv ]⟩ := by
  rw [← ExprLow.build_module'_build_module_eq <| ExprLow.subset_build_module_isSome
    (FinEnv.independent_subset_of_union ε_rhs_ghost_independent) (ExprLow.well_formed_builds_module ghost_rhs_wf)]
  dr_reduce_module; rfl

def rewrite : Rewrite String (String × Nat) where
  params := 8
  pattern := default
  rewrite := fun types n => ⟨lhsLower (types.map (·.2)), rhsGhostLower n.2⟩
  fresh_types := fun x => (x.1, x.2+5)
  name := "loop-rewrite"

end Proof

end Graphiti.LoopRewrite
