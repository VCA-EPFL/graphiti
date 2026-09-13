+++
title = "Rewrite your first graph in Lean"
description = "Build a small dataflow graph, look at how Graphiti stores it, and apply a rewrite to it."
weight = 10
[menus.main]
  parent = "tutorials"
  weight = 10
+++

In this tutorial we write a small dataflow graph in Lean, look at how Graphiti stores it, and apply one of the
library's rewrites to it. By the end you will have a Lean file that fuses a chain of `pure` nodes into a single node,
and you will have seen what a rewrite returns when it has nothing left to match.

You need `git`, a clone of the repository and [elan](https://github.com/leanprover/elan), the Lean toolchain manager.
Everything else comes from the repository.

## Build the library

From the root of the repository, download the prebuilt mathlib files and build the default target:

```shell
make setup
lake build
```

`make setup` runs `lake exe cache get`, which fetches compiled mathlib instead of building it from source. `lake build`
builds the `Graphiti` library, which holds the graph definitions and the dataflow rewrites. The first build takes a
while. Later builds only recompile what changed.

## Create a scratch file

Create `FirstRewrite.lean` at the root of the repository with these imports:

```lean
import Graphiti.Core.Rewriter
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.Dataflow.Rewrites

open Graphiti
```

Open the file in an editor with the Lean extension so you see results next to each command. You can also check the
whole file from a shell at any point:

```shell
lake env lean FirstRewrite.lean
```

Keep the `open Graphiti` line. The graph syntax in the next step is scoped to the `Graphiti` namespace and Lean will
not parse it without that line.

## Describe a graph

Add a graph with one input, one output and two `pure` nodes in a chain:

```lean
def twoPures : ExprHigh String (String × Nat) := [graph|
    src [type = "io"];
    snk [type = "io"];

    f [type = "pure", arg = $(0)];
    g [type = "pure", arg = $(1)];

    src -> f [to = "in1"];
    f -> g [from = "out1", to = "in1"];
    g -> snk [from = "out1"];
  ]
```

A `pure` node applies a function to every value that passes through it. The two `io` nodes are different. They are not
components at all, they name the ports of the whole graph, so the edge from `src` into `f` makes `src` the graph's
input. The `arg` attribute gives each node a number, which makes its type unique: `f` has type `("pure", 0)` and `g`
has type `("pure", 1)`.

Ask Lean which nodes the graph contains:

```lean
#eval twoPures.modules.keysList
```

The result is:

```text
["f", "g"]
```

Only `f` and `g` are listed. The `io` nodes turned into port names on those two nodes.

## Lower the graph

Graphiti keeps two forms of every graph. The `ExprHigh` value we just wrote is a list of nodes and a list of edges.
`ExprLow` is an inductive term built from single components, products and connections, and it is the form the proofs
work with. Check that our graph converts:

```lean
#eval twoPures.lower.isSome
```

```text
true
```

## Apply a rewrite

`PureSeqComp.rewrite` looks for a `pure` node whose output feeds another `pure` node, and replaces the pair with one
`pure` node. Rewrites run in a state monad that records each step and hands out fresh type numbers. Start the counter
above the numbers already used in the graph:

```lean
def initState : RewriteState String (String × Nat) :=
  { (default : RewriteState String (String × Nat)) with fresh_type := ("", 2) }
```

Run the rewrite and print the result:

```lean
#eval match (PureSeqComp.rewrite.run twoPures).run initState with
  | .ok g _ => IO.println g
  | .error e _ => IO.println e
```

The output is a graph in DOT syntax:

```text
digraph {

  "src" [type = "io", label = "src: io"];
  "snk" [type = "io", label = "snk: io"];
  "a6875d39" [type = "(pure, 3)", label = "a6875d39: (pure, 3)"];


  "src" -> "a6875d39" [to = "in1", headlabel = "in1"];
 "a6875d39" -> "snk" [from = "out1", taillabel = "out1"];

}
```

Look at the one remaining node. Its type is `(pure, 3)`, the first fresh number after the `2` we put in the state. Its
name, `a6875d39`, is a hash of its ports. The rewriter names every node this way so that a new node can never clash
with an old one.

## Run out of matches

Now apply the same rewrite twice in a row. Add this definition:

```lean
def twice : RewriteResult' String (String × Nat) ExprHigh := do
  let g ← PureSeqComp.rewrite.run twoPures
  PureSeqComp.rewrite.run g
```

Run it the same way:

```lean
#eval match twice.run initState with
  | .ok g _ => IO.println g
  | .error e _ => IO.println e
```

This prints:

```text
done
```

After the first run the graph has a single `pure` node, so the second run finds no pair to fuse. The rewriter reports
that with the error value `RewriteError.done`, which prints as `done`. A real failure uses `RewriteError.error` and
carries a message instead.

## Rewrite until nothing matches

`rewrite_fix` takes a list of rewrites and applies them until none of them matches, treating `done` as the signal to
stop. Add a graph with three `pure` nodes and a state whose counter starts at 3:

```lean
def threePures : ExprHigh String (String × Nat) := [graph|
    src [type = "io"];
    snk [type = "io"];

    f [type = "pure", arg = $(0)];
    g [type = "pure", arg = $(1)];
    h [type = "pure", arg = $(2)];

    src -> f [to = "in1"];
    f -> g [from = "out1", to = "in1"];
    g -> h [from = "out1", to = "in1"];
    h -> snk [from = "out1"];
  ]

def initState3 : RewriteState String (String × Nat) :=
  { (default : RewriteState String (String × Nat)) with fresh_type := ("", 3) }

#eval match (rewrite_fix [PureSeqComp.rewrite] threePures).run initState3 with
  | .ok g st => IO.println s!"{g}\n{st.runtime_trace.length} log entries"
  | .error e _ => IO.println e
```

The printed graph again has a single `pure` node between `src` and `snk`, this time with type `(pure, 5)`. The first
fusion created type 4, and the second fused that node with the one left over. The last line reads `2 log entries`, one
for each rewrite that matched.

## What you did

You wrote a graph in Graphiti's graph syntax and saw its `io` nodes become port names. You lowered it to the inductive
form, ran a rewrite once, ran it again until it reported `done`, and let `rewrite_fix` apply it until it stopped
matching. The `graphiti` command-line tool is built from the same pieces. It chains dozens of rewrites over circuits
that come from Dynamatic.

From here you can:

- run the full tool on a benchmark in [Rewrite a Dynamatic benchmark]({{< relref "rewrite-a-dynamatic-benchmark" >}}),
- write your own rewrite with [Add a rewrite]({{< relref "/how-to/add-a-rewrite" >}}),
- read [How a rewrite runs]({{< relref "/explanation/how-a-rewrite-runs" >}}) to see what `Rewrite.run` did to
  your graph.
