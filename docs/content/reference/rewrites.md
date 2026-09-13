+++
title = "Rewrites"
description = "Every rewrite in Graphiti/Core/Dataflow/Rewrites, what it matches and where the pipeline uses it."
weight = 60
[menus.main]
  parent = "reference"
  weight = 60
+++

Each rewrite lives in its own file under `Graphiti/Core/Dataflow/Rewrites/` and namespace, and exposes a value named
`rewrite` of type `Rewrite String (String × Nat)`. The name column is the `name` field, which also appears in the log.

## Rewrites

| Name | Namespace | Left-hand node types | Right-hand node types |
| --- | --- | --- | --- |
| `fork-3` to `fork-10` | `Fork3Rewrite` to `Fork10Rewrite` | `forkN` | `fork2` feeding `fork(N-1)` |
| `combine-mux` | `CombineMux` | `mux`, `mux`, `fork2` | `join`, `join`, `mux`, `split` |
| `combine-branch` | `CombineBranch` | `branch`, `branch`, `fork2` | `join`, `branch`, `split`, `split` |
| `join-split-loop-cond` | `JoinSplitLoopCond` | `branch`, `fork2`, `initBool` | the same, plus `join` and `split` |
| `join-split-loop-cond-alt` | `JoinSplitLoopCondAlt` | `branch`, `fork2`, `initBool` | the same, plus `join` and `split` |
| `load-rewrite` | `LoadRewrite` | `load`, `mc` | `pure` |
| `reduce-split-join` | `ReduceSplitJoin` | `split`, `join` | `queue` |
| `join-queue-left` | `JoinQueueLeftRewrite` | `queue`, `join` | `join` |
| `join-queue-right` | `JoinQueueRightRewrite` | `queue`, `join` | `join` |
| `mux-queue-right` | `MuxQueueRightRewrite` | `queue`, `mux` | `mux` |
| `split-sink-left` | `SplitSinkLeft` | `split`, `sink` | `pure` |
| `split-sink-right` | `SplitSinkRight` | `split`, `sink` | `pure` |
| `pure-sink` | `PureSink` | `pure`, `sink` | `sink` |
| `pure-join-left` | `PureJoinLeft` | `pure`, `join` | `pure`, `join` |
| `pure-join-right` | `PureJoinRight` | `pure`, `join` | `pure`, `join` |
| `pure-split-left` | `PureSplitLeft` | `split`, `pure` | `split`, `pure` |
| `pure-split-right` | `PureSplitRight` | `split`, `pure` | `split`, `pure` |
| `pure-seq-comp` | `PureSeqComp` | `pure`, `pure` | `pure` |
| `fork-pure` | `ForkPure` | `pure`, `fork2` | `fork2`, `pure`, `pure` |
| `fork-join` | `ForkJoin` | `join`, `fork2` | `fork2`, `fork2`, `join`, `join` |
| `join-assoc-left` | `JoinAssocL` | `join`, `join` | `join`, `join`, `pure` |
| `join-assoc-right` | `JoinAssocR` | `join`, `join` | `join`, `join`, `pure` |
| `join-comm` | `JoinComm` | `join` | `join`, `pure` |
| `join-split-elim` | `JoinSplitElim` | `split`, `join` | `pure` |
| `branch-pure-mux-left` | `BranchPureMuxLeft` | a `branch`, `mux` and `fork2` with a region between them | the region replaced by `pure` nodes |
| `branch-pure-mux-right` | `BranchPureMuxRight` | as above, on the other side | as above |
| `branch-mux-to-pure` | `BranchMuxToPure` | `branch`, `mux`, `fork2`, `pure`, `pure` | `join`, `pure` |
| `loop-rewrite` | `LoopRewrite2` | `mux`, `fork2`, `branch`, `split`, `pure`, `initBool` | `tag_untagger_val`, `merge2`, `branch`, three `split`, two `join`, `pure` |

## Rewrites to pure nodes

`Graphiti/Core/Dataflow/Rewrites/PureRewrites.lean` turns single components into `pure` nodes, adding `join` and
`split` nodes where a component has several inputs or outputs. Each namespace has its own `rewrite`.

| Name | Namespace | Matches |
| --- | --- | --- |
| `pure-constant` | `PureRewrites.Constant` | `constant` |
| `pure-constant-nat` | `PureRewrites.ConstantNat` | `constantNat` |
| `pure-constant-bool` | `PureRewrites.ConstantBool` | `constantBool` |
| `pure-operator1` to `pure-operator3` | `PureRewrites.Operator1` to `Operator3` | `operator1` to `operator3` |
| `pure-cond_operator1`, `pure-cond_operator2` | `PureRewrites.CondOperator1`, `CondOperator2` | `cond_operator1`, `cond_operator2` |
| `pure-fork` | `PureRewrites.Fork` | `fork2` |

The `matcher` in every namespace of this file throws an error saying it is not implemented.
`PureRewrites.specialisedPureRewrites p` returns copies whose patterns take the first node found by `p`.

## Rewrites with a targeted pattern

`JoinComm.rewrite`, `JoinAssocL.rewrite`, `JoinAssocR.rewrite` and `JoinSplitElim.rewrite` have no working general
matcher. Use `targetedRewrite s`, which matches the node named `s`. The oracle pipeline creates them that way from
`JSLangRewrite.mapToRewrite`.

## Where the executable uses them

`Dataflow.lean` groups rewrites into lists:

| List | Rewrites |
| --- | --- |
| `forkRewrites` | `fork-10` down to `fork-3` |
| `combineRewrites` | `combine-mux`, `combine-branch`, `join-split-loop-cond`, `join-split-loop-cond-alt` |
| `loadRewrite` | `load-rewrite` |
| `reduceRewrites` | `reduce-split-join`, `join-queue-left`, `join-queue-right`, `mux-queue-right` |
| `reduceSink` | `split-sink-right`, `split-sink-left`, `pure-sink` |
| `movePureJoin` | `pure-join-left`, `pure-join-right`, `pure-split-right`, `pure-split-left` |

`normaliseLoop` applies `forkRewrites` with `rewrite_fix`, then `combineRewrites` and `loadRewrite` with
`rewrite_loop`, then `reduceRewrites` with `rewrite_fix`. `loadRewrite` runs inside `withUndo`. `pureGeneration` uses
the pure rewrites, `fork-pure`, `fork-join`, `pure-seq-comp`, `movePureJoin` and `reduceSink`. The oracle step applies
`join-assoc-left`, `join-assoc-right`, `join-comm` and `join-split-elim` to named nodes. The last step of each loop is
`loop-rewrite`.

## Undo index

`rewrite_index` in `Graphiti/Core/Dataflow/Rewrites.lean` maps names to rewrites so that `reverseRewrites` can find the
rewrite behind a log entry. It contains every rewrite on this page. For a duplicated name the first entry wins.

## Proofs

| File | Status |
| --- | --- |
| `LoopRewriteCorrect.lean`, `LoopImplementationProof.lean` | Complete proof, `LoopRewrite.verified_rewrite`, checked with `#print axioms`. It covers `LoopRewrite.rewrite` from `LoopRewrite.lean`, whose left-hand side includes two `queue` nodes. The executable applies `LoopRewrite2.rewrite`. |
| `JoinCommCorrect.lean` | Module reduction and interface matching done. The simulation relation and refinement are `sorry`. |
| `JoinRewrite.lean` | Contains `sorry` and is not imported by `Rewrites.lean`. |

The other rewrites on this page have no correctness proof in `Graphiti/Core`.
