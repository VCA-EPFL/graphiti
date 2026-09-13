+++
title = "Two graph forms"
description = "Why Graphiti keeps both ExprHigh and ExprLow, and how names, ports and types connect them to the semantics."
weight = 20
[menus.main]
  parent = "explanation"
  weight = 20
+++

Graphiti stores a circuit in two forms and converts between them all the time. It looks like duplication until you try
to make one form do both jobs.

## ExprHigh is for finding things

`ExprHigh Ident Typ` is a record with two fields. `modules` maps node names to a port mapping and a type, and
`connections` lists pairs of an output port and an input port.

This is the form you write with `[graph| ... ]`, the form the DOT parser returns, and the form patterns search. Nodes
have names. You can look one up, follow its outputs with `followOutput`, and replace it by updating a map.

It is a poor form for proofs. A list of nodes has no structure to induct on, and the meaning of the graph depends on
names that every lemma would have to track.

## ExprLow is for proofs

`ExprLow Ident Typ` is an inductive type with three constructors. `base map typ` is one component of type `typ` with
its ports renamed by `map`. `product l r` puts two expressions side by side. `connect c e` wires together the output
and input named by `c` inside `e`.

The constructors match `Module.renamePorts`, `Module.product` and `Module.connect'` one for one, and
`ExprLow.build_module'` is exactly that translation. A proof about a term goes by induction on the three cases, and
the congruence lemmas for product and connect handle the two that combine subterms.

`ExprHigh.lower` converts a graph by nesting its nodes into products and wrapping the result in one `connect` per
connection. `ExprLow.higher_correct` converts back.

## Ports are names for wires

A port mapping on a node sends each of the component's own ports to the name of a wire. After
`f -> g [from = "out1", to = "in1"]`, node `f` maps its `out1` to the wire `⟨.internal "f", "out1"⟩`, node `g` maps its
`in1` to `⟨.internal "g", "in1"⟩`, and the connection joins those two wires. A port mapped to a `.top` wire is an
external port of the whole graph.

Because meaning depends only on how wires connect, two terms that differ in wire names describe the same circuit.
`ExprLow.weak_beq` walks two terms of the same shape and returns the renaming between them. That is how the rewriter
lines up a rewrite's left-hand side, written with the author's wire names, with the part of your graph it matched.

## Types are pairs

In the executable a node type is a pair such as `("pure", 12)`, a component name and a number no other node uses. The
name alone would not do. Two `pure` nodes compute different functions, and two `join` nodes can carry different data,
so each node needs its own entry in the environment.

An environment, `Env Ident Typ` in `Graphiti/Core/Graph/Environment.lean`, is a function from node types to Lean
modules, and `build_module'` looks every `base` node up in it. The graph says `("join", 7)`. The environment says which
`StringModule.join T T'` that is.

Proofs never fix an environment. They assume `Env.well_formed`, which only asks that a type named `"join"` maps to
some `join T T'`, a type named `"pure"` maps to some `pure f`, and so on. A rewrite proved under that assumption holds
for every choice of data types and functions. That is why `pure` and the operator nodes can stay opaque, and why one
proof covers every loop body.

Rewrites that add nodes need type numbers nobody uses yet. `RewriteState.fresh_type` holds the counter, and the proofs
require it to start above `FinEnv.max_typeD` of the environment. Each verified rewrite then extends the environment
with modules for the numbers it handed out.

## Names are hashes

The rewriter names each node after a hash of its port mapping, eight hex digits from
`PortMapping.hashPortMapping`. The name then follows from the wiring. Rebuilding a graph from a term gives the same
nodes the same names, with no counter to keep in sync, and `Rewrite.run'` checks afterwards that no two nodes share a
name. The parser uses the same scheme for input files and keeps a mapping back to the original names, which the
executable applies before printing.

## Reordering costs nothing

One graph lowers to many terms. Products can be regrouped and swapped, and connections can be listed in any order. To
replace a subgraph, the rewriter needs a term in which that subgraph is a single subterm. `ExprLow.comm_bases` moves
chosen nodes to the front of the product chain, and `ExprLow.comm_connections'` pushes chosen connections down next to
the nodes they join.

`Graphiti/Core/Graph/ExprLowLemmas.lean` proves that these reorderings preserve refinement, in lemmas such as
`refines_comm_bases` and `refines_comm_connections'`. The rewriter can shuffle a term as much as it likes and the
shuffle adds no proof obligation. That is most of the reason the low-level form exists.
