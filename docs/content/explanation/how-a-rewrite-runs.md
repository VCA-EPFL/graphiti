+++
title = "How a rewrite runs"
description = "What Rewrite.run' does to a graph, why its correctness proof ignores the pattern, and how undo works."
weight = 30
[menus.main]
  parent = "explanation"
  weight = 30
+++

`Rewrite.run'` in `Graphiti/Core/Rewriter.lean` is about a hundred lines long. Every rewrite the executable applies
goes through it, and the main correctness theorem is a statement about it. This page follows it step by step and then
explains why the proof can ignore most of what it does.

## The steps

Given a graph `g` and a rewrite, `Rewrite.run'` does this:

1. It runs the pattern on `g` and gets a list of node names and a vector of their types. If the pattern throws `done`,
   so does the rewrite, and nothing is logged.
2. It adds a debug entry to the log, calls `rewrite.rewrite` with the matched types and the current fresh type, and
   advances the counter. The result is a `DefiniteRewrite`: a left-hand `ExprLow` term and a right-hand one.
3. It extracts the matched nodes into a subgraph and lowers that subgraph to a term `e_sub`.
4. It lowers all of `g` and reorders the term with `comm_bases` and `comm_connections'`, so the matched nodes and
   their connections sit together in one subterm.
5. It compares the rewrite's left-hand side with `e_sub` using `weak_beq`. The shapes agree but the wire names do not,
   so the comparison returns a renaming.
6. It applies that renaming to both sides of the rewrite. The left-hand side now uses the graph's wire names, and the
   right-hand side is attached to the same external wires.
7. It gives the right-hand side's internal wires fresh names with the prefix `rw_N_`, and checks with
   `ensureIOUnmodified` that this renaming left the external wires alone.
8. It swaps the renamed left-hand side for the right-hand side inside the reordered term with `force_replace`. If no
   subterm matches, it fails with `subexpression not found in the graph`.
9. It converts the term back to a graph with `higher_correct`, which names every node after the hash of its ports.
10. It turns the debug entry into a rewrite entry listing renamed and added nodes, fails if two nodes share a name, and
    advances the name prefix.

## Why the proof ignores the pattern

`run'_refines` in `Graphiti/Core/RewriterLemmas.lean` states, in words:

> Suppose the pattern of `rw` matched `g`, `g` lowers to a term that is well formed and well typed in the environment
> `ε_global`, a `VerifiedRewrite` exists for the rewrite at the matched types, and `Rewrite.run' g rw` returns `g'`.
> Then `g'` read in `ε_global ++ vrw.ε_ext` refines `g` read in `ε_global`.

Nothing in that statement depends on which nodes the pattern chose. The pattern is untrusted. If it picks nodes that do
not fit the left-hand side, step 5 or step 8 fails and the rewrite returns an error. If it picks nodes that do fit, the
result is correct however the pattern found them.

The renaming and reordering steps get the same treatment. Steps 4 to 9 only rename wires and rearrange terms, and the
lemmas in `ExprLowLemmas.lean` show that those operations preserve refinement. The one step with real content is the
swap in step 8, and there the proof uses the rewrite's own `refinement` field together with the congruence lemmas for
product and connect.

This split is the design decision that matters most in Graphiti. Patterns can be hand-written per rewrite, generated
from a graph with `defaultMatcher`, or come from an external program, and none of that code has to be trusted.

## What a verified rewrite provides

`VerifiedRewrite env_well_formed pattern rewrite ε` bundles the facts `run'_refines` needs about one rewrite:

| Field | Meaning |
| --- | --- |
| `ε_ext` | Modules for the node types of the right-hand side. |
| `ε_ext_wf` | `ε_ext` satisfies `env_well_formed`. |
| `ε_compatible` | Every type in `ε_ext` keeps its module in `ε ++ ε_ext`, so adding `ε_ext` changes nothing already in `ε`. |
| `rhs_wf`, `rhs_wt` | The right-hand side is well formed and well typed in `ε_ext`. |
| `lhs_locally_wf` | Every port renaming on the left-hand side is invertible. |
| `refinement` | `[e| rewrite.output_expr, (ε ++ ε_ext).toEnv ] ⊑ [e| rewrite.input_expr, ε.toEnv ]`, whenever `pattern` matched a graph and the lowered match is weakly α-equivalent to `rewrite.input_expr`. |

The environment grows with each rewrite. That is how a fresh type number gets its meaning. If `ε_ext` only holds fresh
numbers, `ε_compatible` follows from `FinEnv.independent_subset_of_union`. A rewrite may also reuse types that `ε`
already contains, as long as `ε_ext` gives them the same modules. The CFG rewrites in `Graphiti/Projects/CFG` need
this, because their node types have no fresh number.

`run'_preserves_well_formed` and `run'_preserves_well_typed` show that the result satisfies the preconditions again in
the larger environment. Together with transitivity of refinement, the theorem extends to a sequence of verified
rewrites.

## Undo

Some stages of the pipeline turn a region into a form that is easy to transform but that nobody wants to build, and
then want the original components back. `withUndo` brackets such a stage with markers in the log. At the end,
`reverseRewrites` walks the bracketed entries from newest to oldest and applies each one backwards.

No rewrite needs a hand-written inverse. A log entry holds the input and output graphs, the matched nodes and their
types. From these, `reverse_rewrite` rebuilds both sides of the original rewrite, works out the renaming that maps them
onto the nodes now in the graph, and returns a rewrite with the sides swapped and a pattern that returns exactly
those nodes. That rewrite then goes through `Rewrite.run'` like any other.

A reversed rewrite needs the opposite proof. Swapping the sides turns `rhs ⊑ lhs` into a claim that `lhs ⊑ rhs`,
which a `VerifiedRewrite` for the forward direction does not give you.

## Abstraction and concretisation

`Abstraction.run` replaces a matched subgraph with a single node of a new type and returns a `Concretisation` holding
the subgraph. `Concretisation.run` puts the subgraph back in place of that node. Both reuse the renaming and
replacement steps above, and the docstring on `Abstraction.run` says they should need no proofs of their own. The
`--fast` pipeline uses them to cut a loop body out of the graph, process it separately and paste the result back.
