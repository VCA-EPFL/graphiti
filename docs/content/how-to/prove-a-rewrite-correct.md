+++
title = "Prove a rewrite correct"
description = "Show that the right-hand side of a rewrite refines its left-hand side and package the result for run'_refines."
weight = 30
[menus.main]
  parent = "how-to"
  weight = 30
+++

A rewrite is proven once you can build a `VerifiedRewrite` for it. The general theorem `run'_refines` in
`Graphiti/Core/RewriterLemmas.lean` then tells you that applying the rewrite to any well-formed, well-typed graph gives
a graph that refines the original.

The steps below follow `Graphiti/Core/Dataflow/Rewrites/JoinCommCorrect.lean`, which has every step in place but
leaves the refinement itself as `sorry`. `Graphiti/Core/Dataflow/Rewrites/LoopImplementationProof.lean` is the complete
example to copy from once you reach the refinement.

Before writing tactics, read `AGENTS.md` at the repository root. It asks for short proofs that lean on `grind` and
`simp`, and it forbids removing or changing `#print axioms` checks.

## Create the proof file

Put the proof next to the rewrite, in a file named after it with a `Correct` suffix. Proof files use plain imports
rather than the `module` system:

```lean
import Graphiti.Core.Dataflow.Component
import Graphiti.Core.Graph.ExprLowLemmas
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.RewriterLemmas
import Graphiti.Core.Dataflow.Rewrites.JoinComm

namespace Graphiti.JoinComm
```

## Assume an environment

The proof has to hold for every environment the rewriter might run in, so take the environment as a variable:

```lean
variable [e : Environment Env.well_formed lhsLower]
```

`Environment` gives you the environment `e.ε`, the matched type numbers `e.types`, an upper bound `e.max_type` on the
type numbers in use, and proofs that the environment is well formed and that the left-hand side is well formed and
well typed under it.

## Pin down the components

`Env.well_formed` says that a type named `"join"` maps to `StringModule.join T₁ T₂` for some `T₁` and `T₂`. Get those
types out and tag the lookup with `drenv`, so that module reduction can use it later:

```lean
theorem env_types :
    ∃ (T : _ × _), e.ε.find? ("join", e.types[0]) = some ⟨_, StringModule.join T.1 T.2⟩ := by
  have h5 := ExprLow.well_formed_wrt_from_well_typed e.6 e.4.1
  assumption

def T1 := env_types.choose.1
def T2 := env_types.choose.2

@[drenv] theorem lhs_ε_find1 : e.ε.find? ("join", e.types[0]) = some ⟨_, StringModule.join T1 T2⟩ := by
  rewrite [env_types.choose_spec]; rfl
```

## Give the right-hand side an environment

The right-hand nodes use fresh type numbers above `e.max_type`. Build a small environment that assigns them modules,
and tag its lookups with `drenv` too:

```lean
noncomputable def ε_rhs : FinEnv String (String × Nat) :=
  ([ (("join", e.max_type+1), ⟨_, StringModule.join T2 T1⟩)
   , (("pure", e.max_type+2), ⟨_, @StringModule.pure (T2 × T1) (T1 × T2) λ (x, y) => (y, x) ⟩)
   ].toAssocList)

@[drenv] theorem rhs_ε_find1 : ε_rhs.find? ("join", e.max_type+1) = some ⟨_, StringModule.join T2 T1⟩ := by
  simp [ε_rhs]
```

## Reduce both sides to modules

`def_module` evaluates `[T| expr, env ]` and `[e| expr, env ]` during elaboration, so the definitions hold concrete
records instead of unevaluated `build_module` calls. `seal` keeps the chosen types opaque while that happens:

```lean
seal T1 T2 in
def_module lhsType : Type :=
  [T| (lhsLower e.types), e.ε.find? ]

seal T1 T2 in
noncomputable def_module lhsEvaled : StringModule lhsType :=
  [e| (lhsLower e.types), e.ε.find? ]
```

Do the same for `rhsType` and `rhsEvaled` with `rhsLower e.max_type` and `ε_rhs.toEnv`. Without a `reduction_by`
clause, `def_module` runs the `dr_reduce_module` tactic. `JoinCommCorrect.lean` spells the tactic steps out, which
helps when a reduction gets stuck.

## Prove the interfaces match

```lean
instance : MatchInterface rhsEvaled lhsEvaled := by
  unfold rhsEvaled lhsEvaled
  solve_match_interface
```

## Prove refinement

Choose a relation `φ` between right-hand and left-hand states and prove two things. The first is that `φ` is preserved
by every input, output and internal step of the right-hand module, which is `rhsEvaled ⊑_{φ} lhsEvaled`. The second is
that every initial right-hand state is related to some initial left-hand state. Then combine them:

```lean
def φ : rhsType → lhsType → Prop := sorry

theorem refines' : rhsEvaled ⊑_{φ} lhsEvaled := sorry

theorem refines_init : Module.refines_initial rhsEvaled lhsEvaled φ := sorry

theorem refines : rhsEvaled ⊑ lhsEvaled := ⟨inferInstance, φ, refines', refines_init⟩
```

Replace each `sorry`. The theorems `refine`, `refines_init` and `refines` near the end of `LoopImplementationProof.lean`
show a finished version.

## Package the result

Build a `VerifiedRewrite` for the rewrite, instantiated at the environment's types:

```lean
noncomputable def verified_rewrite :
    VerifiedRewrite Env.well_formed (rewrite.rewrite (e.types.map ("", ·)) ("", e.max_type)) e.ε where
  ε_ext := ε_rhs
  ε_ext_wf := sorry
  ε_independent := sorry
  rhs_wf := sorry
  rhs_wt := sorry
  lhs_locally_wf := sorry
  refinement := sorry
```

The fields ask that `ε_rhs` is well formed and disjoint from `e.ε`, that the right-hand expression is well formed and
well typed under `ε_rhs`, that every port renaming on the left-hand side is invertible, and that the right-hand module
under `e.ε ++ ε_rhs` refines the left-hand module under `e.ε`. `LoopImplementationProof.lean` proves `refinement`
by applying `Module.refines_eq_relax` to `refines` and to equations that relate the reduced modules to the
`[e| ... ]` terms.

## Guard against sorry

Add an axiom check below the definition. `#guard_msgs` fails the build if the list of axioms changes, and a leftover
`sorry` adds `sorryAx` to it:

```lean
/--
info: 'Graphiti.JoinComm.verified_rewrite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms verified_rewrite
```

## Build the proof

```shell
lake build Graphiti.Core.Dataflow.Rewrites.JoinCommCorrect
```

Once the build passes without warnings, pass `verified_rewrite` as the `vrw` argument of `run'_refines` to get the
graph-level statement for this rewrite.
