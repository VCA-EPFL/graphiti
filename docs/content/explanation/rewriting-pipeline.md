+++
title = "The rewriting pipeline"
description = "How Dataflow.lean turns a Dynamatic loop into one that runs iterations out of order."
weight = 40
[menus.main]
  parent = "explanation"
  weight = 40
+++

`Dataflow.lean` turns a Dynamatic circuit into one whose loops can hold several iterations at once. The change itself
is a single rewrite, `loop-rewrite`. Almost everything else in the file brings the circuit into the one shape that
rewrite can match. This page follows a circuit through the default pipeline.

## The goal

Dynamatic compiles a loop into a ring. A `mux` at the head chooses between a value entering the loop and a value
coming back from the previous iteration. The loop body computes a new value and a condition. A `branch` at the tail
sends the value round again or out of the loop, depending on the condition. An `init` node feeds the `mux` its select
signal, `false` for the first entry and the loop condition after that. One iteration occupies the ring at a time.

`LoopRewrite2.rewrite` matches that ring once the whole body is a single `pure` node that returns the value and the
condition as a pair. It removes the `mux` and the `init` and puts a `merge2` at the head, with a `tag_untagger_val` in
front of it. Each value entering the loop gets a tag, which travels with it through the body and back round. Values
from different iterations can pass each other inside the loop, and the untagger releases finished results in the order
their inputs arrived.

The hard part is getting the body into a single `pure` node, and that is what the stages below do.

## Preparing the input

`scripts/dynamatic-to-graphiti.py` rewires each loop named with `--mids` into the form Graphiti expects. The `Merge`
that drives the `mux` select becomes an `init Bool false` node, forks around the `branch` and `mux` are reordered so
their conditions come from predictable ports, and memory controllers are split. The DOT parser then maps Dynamatic
types to Graphiti types, and every node type gets its own number.

## Normalising the loop

The first subsection of the progress output starts with `normaliseLoop`:

- `forkRewrites` splits every wide fork into a chain of `fork2` nodes.
- `combineRewrites` merges `mux` nodes that share a select signal into one `mux` over pairs, with `join` and `split`
  around it, and does the same for `branch` nodes. A loop over several variables ends up with one `mux` and one
  `branch`.
- `loadRewrite` turns memory reads into `pure` nodes, under `withUndo` so the reads come back at the end.
- `reduceRewrites` removes a `split` followed by a `join`, leaving a `queue`, and absorbs queues in front of joins and
  muxes.

Still in that subsection, `pureGeneration` runs on the regions found by `BranchPureMuxLeft` and `BranchPureMuxRight`,
the two sides of each conditional inside the body. This also runs under `withUndo`.

## Turning components into pure nodes

`pureGeneration` converts a region in four passes, as its docstring in `Dataflow.lean` lists:

1. Turn every component except forks and sinks into a `pure` node, using the rewrites in `PureRewrites.lean`.
2. Push forks upward, move `pure` nodes across joins and below sinks, and remove sinks.
3. Turn the forks into `pure` nodes.
4. Push the `pure` nodes outward again. What remains is `pure`, `split` and `join` nodes.

A tangle of `pure`, `join` and `split` nodes can always be collapsed into one `pure` node, but the sequence of
associativity and commutativity steps that does it depends on the whole region. Graphiti's fixed rewrite lists cannot
find that sequence, so it asks the oracle.

## The oracle

`rewriteWithEgg` in `Graphiti/Core/Dataflow/JSLang.lean` reads the region between two nodes as a `JSLang` term, a
tree of `join`, `split1`, `split2` and `pure` nodes, and writes it as an S-expression to the standard input of
`bin/graphiti_oracle`. The oracle is a Rust program from
[OracleGraphiti](https://github.com/VCA-EPFL/OracleGraphiti). The comment at the top of `PureRewrites.lean` says the
pure form is there so it can be optimised externally by egg, an equality saturation library. The oracle replies with a
JSON list of steps. Each step associates to the left, associates to the right, commutes, or eliminates a split
followed by a join, at a named node.

`eggPureGenerator` maps each step to the targeted form of `JoinAssocL`, `JoinAssocR`, `JoinComm` or `JoinSplitElim`
and applies it with `Rewrite.run`. After each step it fuses neighbours with `pure-seq-comp` and renames the nodes in
the steps still to come. It asks the oracle again until the answer is empty.

The oracle sits outside the proof and does not need to be inside it. Its answers are suggestions. Each one goes through
`Rewrite.run'` and is checked against the graph like any hand-written pattern, so a wrong answer produces an error, not
a wrong circuit.

The second subsection of the progress output runs the oracle on both sides of each inner conditional, folds the
conditionals into the body with `branch-pure-mux-left`, `branch-pure-mux-right` and `branch-mux-to-pure`, and then runs
`pureGeneration` and the oracle once more on the whole loop body. All of it runs under `withUndo`.

## The loop rewrite

With the body reduced to one `pure` node, the third subsection applies `LoopRewrite2.rewrite` to the ring around the
current `initBool` node. It does not run under `withUndo`, so the tagged loop stays.

## Rebuilding the body

A `pure` node stands for a mathematical function, not for hardware Dynamatic can generate. The stage printed as
`Reconstructing graph from pure` runs `reverseRewrites`, which undoes every rewrite recorded under `withUndo`, newest
first. The body returns as the original components, now inside the tagged loop. Rewrites that ran outside `withUndo`
stay applied: the fork splitting, the combined muxes and branches, the queue reductions and the loop rewrite itself.

## Printing

The executable restores the original node names, infers a width for every port with `infer_equalities`, and prints
Dynamatic DOT. `scripts/graphiti-to-dynamatic.py` then reassembles memory controllers, expands the tagger with the tag
count from `--tag-nums`, and fixes port names for Dynamatic.

## The fast pipeline

`--fast` takes a different route through the same rewrites. `rewriteGraphAbs` normalises the loop and then uses an
`Abstraction` to replace the whole loop body with one placeholder node. It turns a copy of the body into a single
`pure` node on its own, swaps the placeholder for that node, applies the loop rewrite, and swaps the `pure` node back
for the original body with a `Concretisation`. Nothing needs to be undone at the end. The help text describes this
path as fast but unverified.
