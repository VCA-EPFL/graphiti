+++
title = "What is verified"
description = "Which theorems carry Graphiti's guarantee, what they assume, and which parts of the tool sit outside the proofs."
weight = 50
[menus.main]
  parent = "explanation"
  weight = 50
+++

"Formally verified" covers a wide range of claims. This page lists what the Lean development in this repository
proves today, what those proofs assume, and which parts of the tool they do not reach.

## The theorems that carry the guarantee

Three theorems matter, and each has an axiom check that fails the build if its proof ever depends on `sorry`.

`Graphiti.run'_refines` in `Graphiti/Core/RewriterLemmas.lean` is the rewriting engine's correctness theorem. Applying
any rewrite that has a `VerifiedRewrite` yields a graph that refines the original. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

`Graphiti.LoopRewrite.verified_rewrite` in `Graphiti/Core/Dataflow/Rewrites/LoopImplementationProof.lean` is the
`VerifiedRewrite` for the loop rewrite, with the same three axioms.

`Graphiti.Module.refines_implies_trace_inclusion` in `Graphiti/Core/Trace.lean` connects refinement to observable
behaviour. It uses only `propext`, and its check lives in `GraphitiTest/Core/Trace.lean`.

These three axioms are the standard classical axioms of Lean, and mathlib uses them everywhere.

## Where sorry remains

Building `GraphitiCore` reports `sorry` in a handful of places:

- `FinEnv.exists_fresh` in `Graphiti/Core/Graph/Environment.lean`,
- one declaration in `Graphiti/Core/Graph/ModuleLemmas.lean`,
- two declarations in `Graphiti/Core/Graph/ExprLowLemmas.lean`, one of them `build_module_connect_foldr`,
- the simulation relation and refinement in `Graphiti/Core/Dataflow/Rewrites/JoinCommCorrect.lean`.

None of them sits under the three theorems above. If one did, the axiom list would include `sorryAx` and the check
would fail.

## What the proofs assume

The guarantee is conditional, and the conditions are part of the result:

- The environment is well formed. Every node type named `"join"`, `"pure"` and so on is read as the matching
  component, for any data types and functions.
- The input graph lowers, and is well formed and well typed in that environment.
- The fresh type counter starts above every type number in the environment.
- The definitions in `Component.lean` are the specification. If Lean's `branch` behaves differently from the branch
  Dynamatic generates, the proof is about Lean's.

## What the proofs do not reach

Some gaps follow from the approach and some from the current state of the code.

- Progress. Refinement rules out new behaviour, not lost behaviour. A rewrite that deadlocks a circuit can still be
  proved. [Modules and refinement]({{< relref "modules-and-refinement" >}}) explains why.
- The loop rewrite the executable applies. The proof covers `LoopRewrite.rewrite` from `LoopRewrite.lean`, whose
  left-hand side includes two `queue` nodes. `Dataflow.lean` applies `LoopRewrite2.rewrite`, a separate definition
  whose left-hand side has no queues.
- The other rewrites. In `Graphiti/Core`, only the loop rewrite has a complete `VerifiedRewrite`. Fork splitting, mux
  and branch combination, the pure rewrites and the oracle's join rewrites run without one. `Graphiti/Experimental`
  and `Graphiti/Projects/Flushability` contain proof attempts for join and merge rewrites, several with `sorry`.
- Undo. A reversed rewrite needs the opposite refinement, and no proof in the repository provides one.
- The pipeline in `Dataflow.lean`: which loops it picks, the order of stages, and the `--fast` path.
- Everything outside the Lean proofs: the Python conversion scripts, the oracle binary, the DOT parser and printers,
  the type inference used for printing, and Dynamatic itself.

That is a long list, and a research tool is expected to have one. The part that is proved, that the engine preserves
refinement for any verified rewrite whatever the pattern and the renaming do, is also the part that is hardest to get
right by testing.

## How the checks work

An axiom check wraps `#print axioms` in `#guard_msgs`, with the expected output in a docstring:

```lean
/--
info: 'Graphiti.LoopRewrite.verified_rewrite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms verified_rewrite
```

Lean implements `sorry` as the axiom `sorryAx`, so any `sorry` the theorem depends on changes the printed list and
breaks the build. The `named_sorry` tactic in `Tactic.lean` adds an axiom with its own name, and the check catches that
too. `AGENTS.md` tells contributors never to remove or edit these checks.

## Trust by directory

The repository follows the Research Codebase Manifesto, as the README describes. `Graphiti/Core` is built by
continuous integration and held to engineering standards. `Graphiti/Projects` is built by continuous integration too,
but its proofs may be unfinished. `Graphiti/Experimental` is built by nothing. Treat a result as established when it
lives in `Graphiti/Core` and has an axiom check.
