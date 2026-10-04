/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Graphiti.Core.Dataflow.Component
public import Graphiti.Core.Graph.ExprLowLemmas
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Graph.ModuleReduction
public import Graphiti.Core.RewriterLemmas
public import Graphiti.Core.Dataflow.Rewrites.JoinComm

@[expose] public section

open Batteries (AssocList)

namespace Graphiti.JoinComm

open StringModule

section Proof

theorem lhsLower_locally_wf {types} : (lhsLower types).locally_wf := rfl

variable [e : Environment Env.well_formed lhsLower]

local instance : BEq (String × Nat) := instBEqOfDecidableEq

/-! ### Left-hand side -/

/--
The well-formedness of the environment fixes the single node of the lhs to be a `join`, which is therefore determined by
the data types `T1` and `T2` of its two inputs.
-/
theorem env_types : ∃ (T1 T2 : Type), e.ε.find? ("join", e.types[0]) = some ⟨_, join T1 T2⟩ := by
  with_reducible have hwf := ExprLow.well_formed_wrt_from_well_typed e.h_lhs_wf e.h_wf.h_wf
  dsimp [drunfold_defs, reduceAssocListfind?, reduceExprHighLower, reduceExprHighLowerProdTR,
    reduceExprHighLowerConnTR, ExprHigh.uncurry, ExprLow.well_formed_wrt, Env.well_formed'] at hwf
  obtain ⟨⟨T1, T2⟩, h⟩ := hwf
  exists T1, T2

def T1 := env_types.choose
def T2 := env_types.choose_spec.choose

@[drenv] theorem lhs_ε_find : e.ε.find? ("join", e.types[0]) = some ⟨_, join T1 T2⟩ :=
  env_types.choose_spec.choose_spec

seal T1 T2 in
@[reducible] def_module lhsType : Type :=
  [T| (lhsLower e.types), e.ε.find? ]

seal T1 T2 in
noncomputable def_module lhsEvaled : StringModule lhsType :=
  [e| (lhsLower e.types), e.ε.find? ]

seal T1 T2 in
theorem lhs_evaled_eq :
    (⟨_, lhsEvaled⟩ : TModule1 String) = ⟨_, [e| (lhsLower e.types), e.ε.toEnv ]⟩ := by
  dr_reduce_module; rfl

/-! ### Right-hand side

The rhs uses fresh types above `e.max_type`, so its environment `ε_rhs` is independent of `e.ε`.
-/

noncomputable def ε_rhs : FinEnv String (String × Nat) :=
  ([ (("join", e.max_type+1), ⟨_, join T2 T1⟩)
   , (("pure", e.max_type+2), ⟨_, pure (@Prod.swap T2 T1)⟩)
   ].toAssocList)

@[drenv] theorem ε_rhs_find :
    ε_rhs.find? ("join", e.max_type+1) = some ⟨_, join T2 T1⟩
    ∧ ε_rhs.find? ("pure", e.max_type+2) = some ⟨_, pure (@Prod.swap T2 T1)⟩ := by
  simp [ε_rhs]

theorem ε_rhs_wf : ε_rhs.toEnv.well_formed := by
  rw [Env.well_formed_alt_correct]
  simp [Env.well_formed_alt, Env.well_formed'', ε_rhs]
  grind

theorem ε_rhs_independent : e.ε.toEnv.independent ε_rhs.toEnv := by
  intro n m hfind
  have := FinEnv.max_typeD_none (n := n) e.h_wf.max_is_max
  simp [ε_rhs]
  grind [FinEnv.toEnv]

seal T1 T2 ε_rhs in
theorem rhs_wf : (rhsLower e.max_type).well_formed ε_rhs.toEnv := by
  dsimp [drunfold_defs, reduceAssocListfind?, reduceExprHighLower, reduceExprHighLowerProdTR,
    reduceExprHighLowerConnTR, ExprHigh.uncurry, ExprLow.well_formed]
  simp only [drenv]
  simp [drcomponents, AssocList.keysList]
  decide

seal T1 T2 ε_rhs in
theorem rhs_wt : (rhsLower e.max_type).well_typed ε_rhs.toEnv := by
  dsimp [drunfold_defs, reduceAssocListfind?, reduceExprHighLower, reduceExprHighLowerProdTR,
    reduceExprHighLowerConnTR, ExprHigh.uncurry, ExprLow.well_typed, ExprLow.build_module_interface]
  simp only [drenv, Option.map_some, Option.bind_some, Option.some.injEq, exists_and_left, exists_eq_left']
  simp only [reduceAssocListfind?, Option.some.injEq, exists_eq_left', true_and]

seal T1 T2 ε_rhs in
@[reducible] def_module rhsType : Type :=
  [T| (rhsLower e.max_type), ε_rhs.toEnv ]

seal T1 T2 ε_rhs in
noncomputable def_module rhsEvaled : StringModule rhsType :=
  [e| (rhsLower e.max_type), ε_rhs.toEnv ]

seal T1 T2 ε_rhs in
theorem rhs_evaled_eq :
    (⟨_, rhsEvaled⟩ : TModule1 String) = ⟨_, [e| (rhsLower e.max_type), (e.ε ++ ε_rhs).toEnv ]⟩ := by
  rw [← ExprLow.build_module'_build_module_eq <| ExprLow.subset_build_module_isSome
    (FinEnv.independent_subset_of_union ε_rhs_independent) (ExprLow.well_formed_builds_module rhs_wf)]
  dr_reduce_module; rfl

/-! ### Refinement

The rhs `join` holds the inputs that have not been joined yet, and the `pure` node holds the joined (and swapped)
pairs.  The lhs `join` therefore holds the pairs in `pure` followed by the inputs still waiting in the rhs `join`.
-/

def φ (i : rhsType) (s : lhsType) : Prop :=
  s.1 = i.2.map Prod.fst ++ i.1.2 ∧ s.2 = i.2.map Prod.snd ++ i.1.1

instance : MatchInterface rhsEvaled lhsEvaled := by
  unfold rhsEvaled lhsEvaled
  solve_match_interface

theorem refine : rhsEvaled ⊑_{φ} lhsEvaled := by
  intro ⟨⟨l2, l1⟩, p⟩ ⟨k1, k2⟩ ⟨hk1, hk2⟩
  dsimp at hk1 hk2; subst k1 k2
  constructor
  · intro ident ⟨⟨l2', l1'⟩, p'⟩ v h
    obtain rfl | rfl : ⟨.top, "i_1"⟩ = ident ∨ ⟨.top, "i_0"⟩ = ident := by
      simpa [rhsEvaled] using PortMap.rule_contains h
    all_goals
      dsimp [rhsEvaled, lhsEvaled, PortMap.getIO, reduceAssocListfind?, Module.liftL] at v h ⊢
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨(_, _), _, ⟨rfl, rfl⟩, .done _, ?_⟩
      simp [φ]; rfl
  · intro ident ⟨⟨l2', l1'⟩, p'⟩ v h
    obtain rfl : ⟨.top, "o_out"⟩ = ident := by
      simpa [rhsEvaled] using PortMap.rule_contains h
    dsimp [rhsEvaled, lhsEvaled, PortMap.getIO, reduceAssocListfind?, Module.liftR] at h ⊢
    obtain ⟨rfl, ⟨⟩⟩ := h
    refine ⟨_, (p'.map Prod.fst ++ l1, p'.map Prod.snd ++ l2), .done _, ?_, by simp [φ]⟩
    simp; and_intros <;> rfl
  · intro rule ⟨⟨l2', l1'⟩, p'⟩ hrule h
    dsimp [rhsEvaled, Module.liftL, Module.liftR] at hrule
    simp at hrule; subst rule
    simp at h; obtain ⟨_, _, ⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨_, .done _, ?_⟩
    simp [φ]

theorem refines_init : Module.refines_initial rhsEvaled lhsEvaled φ := by
  intro _ h
  refine ⟨([], []), rfl, ?_⟩
  simp_all [φ, rhsEvaled]

theorem refines : rhsEvaled ⊑ lhsEvaled := ⟨inferInstance, φ, refine, refines_init⟩

noncomputable def verified_rewrite : VerifiedRewrite Env.well_formed rewrite.pattern (rewrite.rewrite (e.types.map ("", ·)) ("", e.max_type)) e.ε where
  ε_ext := ε_rhs
  ε_ext_wf := ε_rhs_wf
  ε_compatible := FinEnv.independent_subset_of_union ε_rhs_independent
  rhs_wf := rhs_wf
  rhs_wt := rhs_wt
  lhs_locally_wf := by dsimp [rewrite]; apply lhsLower_locally_wf
  refinement := by
    intros
    apply Module.refines_eq_relax
    apply rhs_evaled_eq.symm
    rotate_left
    apply refines
    dsimp [rewrite]; rw [Vector.map_map]; dsimp; rw [Vector.map_id]
    apply lhs_evaled_eq.symm

/--
info: 'Graphiti.JoinComm.verified_rewrite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms verified_rewrite

end Proof

end Graphiti.JoinComm
