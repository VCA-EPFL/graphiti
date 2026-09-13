+++
title = "Rewriter API"
description = "Types and functions for defining, running, combining and undoing rewrites."
weight = 70
[menus.main]
  parent = "reference"
  weight = 70
+++

Everything on this page is in namespace `Graphiti`. Unless stated otherwise it is defined in
`Graphiti/Core/Rewriter.lean`.

## Results and state

| Name | Definition |
| --- | --- |
| `RewriteError` | `error (s : String)` for a failure, `done` for "nothing matched". |
| `RewriteState Ident Typ` | `runtime_trace : RuntimeTrace Ident Typ`, `fresh_prefix : Nat`, `fresh_type : Typ`. |
| `RewriteResult Ident Typ α` | `EStateM RewriteError (RewriteState Ident Typ) α`. |
| `RewriteResult' Ident Typ T` | `RewriteResult Ident Typ (T Ident Typ)`, for example `RewriteResult' String Typ ExprHigh`. |
| `RewriteResultSL α` | `Except RewriteError α`. Patterns return this. |
| `RuntimeTrace Ident Typ` | `List (RuntimeEntry Ident Typ)`. |
| `RuntimeEntry Ident Typ` | One log entry. Fields are listed in [Log format]({{< relref "log-format" >}}). |
| `EntryType` | `rewrite`, `abstraction`, `concretisation`, `debug`, `marker (s : String)`. |

## Defining rewrites

| Name | Definition |
| --- | --- |
| `Pattern Ident Typ n` | `ExprHigh Ident Typ → RewriteResultSL (List Ident × Vector Typ n)`. Returns the matched node names and `n` types. |
| `DefiniteRewrite Ident Typ` | `input_expr` and `output_expr`, both `ExprLow Ident Typ`. |
| `Rewrite Ident Typ` | See the next table. |
| `Abstraction Ident Typ` | `pattern : Pattern Ident Typ 0` and `typ : Typ`. |
| `Concretisation Ident Typ` | `expr : ExprLow Ident Typ` and `typ : Typ`. |

Fields of `Rewrite Ident Typ`:

| Field | Type | Default | Meaning |
| --- | --- | --- | --- |
| `params` | `Nat` | | Number of types the pattern returns. |
| `pattern` | `Pattern Ident Typ params` | | Finds the nodes to replace. |
| `rewrite` | `Vector Typ params → Typ → DefiniteRewrite Ident Typ` | | Builds both sides from the matched types and the current fresh type. |
| `transformedNodes` | `List (Option (PortMapping Ident))` | `[]` | For each matched node, the port mapping of the node that replaces it, or `none`. |
| `addedNodes` | `List (PortMapping Ident)` | `[]` | Port mappings of new nodes. |
| `fresh_types` | `Typ → Typ` | `id` | Advances the fresh type counter after the rewrite. |
| `abstractions` | `List (Abstraction Ident Typ)` | `[]` | Not used by `Rewrite.run`. |
| `name` | `Option String` | `none` | Name in the log and in `rewrite_index`. |

## Running rewrites

| Name | Signature | Behaviour |
| --- | --- | --- |
| `Rewrite.run'` | `(g : ExprHigh String Typ) (rewrite : Rewrite String Typ) (norm : Bool := true) : RewriteResult' String Typ ExprHigh` | Applies the rewrite once. See [How a rewrite runs]({{< relref "/explanation/how-a-rewrite-runs" >}}). |
| `Rewrite.run` | `(g) (rewrite) : RewriteResult' String Typ ExprHigh` | `Rewrite.run'` with `norm := true`. |
| `rewrite_loop` | `(rewrites : List (Rewrite String Typ)) (g) (depth := 10000)` | Applies the first rewrite until it reports `done`, then the second on the result, and so on. Never returns to an earlier rewrite. Returns `g` if nothing matched. |
| `rewrite_fix` | `(rewrites) (g) (max_depth := 10000) (depth := 10000)` | Repeats `rewrite_loop` passes until a pass matches nothing. Fails with `ran out of fuel` after `depth` passes. |
| `rewrite_fix_rename` | `(g) (rewrites) (upd) (a) (max_depth) (depth)` | `rewrite_fix` that also updates a value `a` with the node renames of each step. |
| `update_state` | `(f) (a)` | Applies `f` to the renames of the last log entry and to `a`. |
| `withUndo` | `(rw : RewriteResult Ident Typ α)` | Runs `rw` between a `rev-stop` and a `rev-start` marker, so `reverseRewrites` undoes it. |
| `Abstraction.run` | `(g) (abstraction) (norm := false)` | Replaces the matched subgraph with one node of type `abstraction.typ` and returns the graph and a `Concretisation` that restores it. |
| `Concretisation.run` | `(g) (concretisation) (norm := false) (debug := false)` | Replaces the node of type `concretisation.typ` with `concretisation.expr`. Assumes that node is unique. |

## Undoing rewrites

| Name | Defined in | Behaviour |
| --- | --- | --- |
| `reverse_rewrite` | `Rewriter.lean` | Builds a rewrite that turns the output of a logged step back into its input. |
| `rewrite_index` | `Dataflow/Rewrites.lean` | Association list from rewrite names to rewrites. |
| `reverse_rewrite_with_index` | `Dataflow/Rewrites.lean` | `reverse_rewrite` for a log entry, looking the rewrite up by name. |
| `reverseRewrites` | `Dataflow/Rewrites.lean` | Undoes every step between `rev-stop` and `rev-start` markers in the current log. |

## Navigating graphs

| Name | Returns |
| --- | --- |
| `followOutput g inst output` | The `NextNode` reached from output port `output` of node `inst`, or `none`. |
| `followInput g inst input` | The `NextNode` that drives input port `input` of node `inst`, or `none`. |
| `followOutputFull`, `followInputFull` | The same, taking an `InternalPort` instead of a port name. |
| `findType g typ` | Names of the nodes with type `typ`. |
| `calcSucc g` | Map from each node to the `NextNode`s its outputs reach. |
| `fullCalcSucc g` | Successor map with an extra root node before the inputs and a leaf node after the outputs. |
| `findClosedRegion g start end` | All nodes between `start` and `end`, or `none` if a node in between reaches an external port or loops back to `start`. |
| `findDom fuel g`, `findPostDom fuel g` | Dominators and post-dominators, using the Lengauer and Tarjan algorithm. |

`NextNode` has the fields `inst`, `incomingPort`, `outgoingPort`, `portMap`, `typ` and `connection`. For
`followOutput`, `incomingPort` is the input port name on the next node.

## Building patterns

| Name | Behaviour |
| --- | --- |
| `defaultMatcher pat pred cmp` | A pattern that finds a subgraph shaped like the graph `pat`, comparing types with `cmp`. |
| `create_rewrite name lhs rhs pred cmp` | A `Rewrite` whose pattern is `defaultMatcher` on `lhs`. |
| `RewriteHigh`, `RewriteHigh.lower` | A rewrite given as two graphs. `lower` turns it into a `Rewrite` and needs a `FuzzyCompare` instance for the type. |
| `match_node extract_type name g` | Matches the single node `name` if `extract_type` accepts its type. |
| `toPattern f` | Turns a function returning node names into a `Pattern _ _ 0`. |
| `nullTypes p` | Drops the types from a pattern's result. |
| `nonPureMatcher p`, `nonPureForkMatcher p` | Keep only the nodes that are not `split`, `join`, `pure`, `sink`, `mux` or `branch`. The first also drops `fork`. |
| `Pattern.map f p` | Applies `f` to the node list. |
| `Pattern.nest a b` | Runs `b` on the subgraph of nodes matched by `a`. |
| `allPattern f` | Every node whose type name satisfies `f`. |

## Log helpers

| Name | Behaviour |
| --- | --- |
| `addRuntimeEntry e` | Appends `e` to the log. |
| `RuntimeEntry.debugEntry s` | A debug entry with text `s`. |
| `addRuntimeMarker s` | Appends a marker entry. |
| `updRuntimeEntry f` | Applies `f` to the last entry. |
| `rmRuntimeEntry` | Removes the last entry. |
| `incrFreshType f`, `updFreshPrefix` | Advance the counters in the state. |
| `errorIfDone s rw` | Turns a `done` from `rw` into `error s`. |
| `liftError` | Lifts an `Except String` into `RewriteResult`. |

## Oracle interface

Defined in `Graphiti/Core/Dataflow/JSLang.lean`.

| Name | Behaviour |
| --- | --- |
| `JSLang` | Terms `join s a b`, `split1 s a`, `split2 s a`, `pure s a` and `I`, each tagged with a node name. |
| `JSLang.construct` | Builds a term from the successor map between two nodes. |
| `JSLang.toSExpr` | Prints a term as an S-expression for the oracle. |
| `JSLangRewrite` | `assocL s dir`, `assocR s dir`, `comm s`, `elim s`. |
| `parseRewrites` | Reads the oracle's JSON array of objects with fields `rw` (`"L"`, `"R"`, `"C"` or `"E"`), `args` and `dir`. |
| `JSLangRewrite.mapToRewrite` | The targeted `JoinAssocL`, `JoinAssocR`, `JoinComm` or `JoinSplitElim` rewrite for a step. |
| `rewriteWithEgg eggCmd p g` | Runs the oracle on the region found by `p` and returns its steps. |
| `JSLang.upd` | Renames the node names in pending steps after a rewrite. |
