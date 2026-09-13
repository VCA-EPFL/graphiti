+++
title = "Modules and refinement"
description = "How Graphiti describes what a circuit may do, and what it means for one circuit to refine another."
weight = 10
[menus.main]
  parent = "explanation"
  weight = 10
+++

Graphiti never simulates a circuit. It describes what a circuit is allowed to do, as a set of relations, and proves
that one description allows nothing the other does not. This page covers the description and the comparison.

## A module is a set of rules

A `Module Ident S` from `Graphiti/Core/Graph/Module.lean` has a state type `S` and four fields:

- `inputs` gives each input port a relation between a state, a value arriving on the port, and the state afterwards.
- `outputs` does the same for values leaving a port.
- `internals` lists steps that change the state without any value crossing the boundary.
- `init_state` says which states the module may start in.

Rules are relations, not functions, and that choice does a lot of work. A module can be nondeterministic: `merge` may
output any value it holds, and its output relation allows all of them. A module can also refuse. If the input
relation has no successor for some value in the current state, the port does not accept that value now. Nothing
models ready or valid signals. Blocking is the absence of a transition.

Each port rule also carries the Lean type of its values. Two modules can therefore pass different data types on
their ports, and connecting a pair of ports only makes sense when those types are equal.

## Every channel is a buffer

Read through `Graphiti/Core/Dataflow/Component.lean` and nearly every component keeps lists. `pure f` appends `f v` on
input and takes from the front on output. `join` keeps one list per input and pairs their heads. In this semantics a
wire behaves like an unbounded buffer.

That abstraction removes time. When a value moves is invisible, and only the order of values on each port counts.
The proofs therefore say nothing about latency, clock cycles or buffer sizes, and they do not try to. A circuit with
small buffers can do less than the module that describes it, which is the direction refinement allows.

## Building bigger modules

Two operations assemble circuits from components.

`Module.product` places two modules side by side. The state is a pair, and each rule acts on its own half.

`Module.connect'` wires an output port of a module to one of its input ports. Both ports leave the interface. In
their place comes one internal rule that fires the output and the input together, passing the same value, and only
when the two ports carry the same type.

Every graph Graphiti handles is a tree of these two operations over renamed components. `ExprLow` is that tree, and
[Two graph forms]({{< relref "two-graph-forms" >}}) describes how it relates to the graphs you write.

## Why inputs and outputs are separate

Inputs and outputs have the same shape, so a single field could hold both. They are kept apart because refinement
treats them differently. When a specification matches an input, it may take internal steps after it. When it matches
an output, it may take internal steps before it. Never the other way round.

That asymmetry is what makes `connect'` compositional. Wiring an output to an input fuses two rules into one step. If
the specification needed internal steps between the output and the input, the fused step would leave no room for
them. With the rule as it is, the output side finishes its internal work before the output and the input side does
its work after the input, so the fused step always has a matching sequence. The docstring on `Module` gives the same
reason.

## Refinement

`imp ⊑ spec` in `Graphiti/Core/Graph/ModuleLemmas.lean` says that `imp` refines `spec`. It needs three things:

- a `MatchInterface imp spec` instance, meaning both modules have the same ports with the same value types,
- a relation `φ` between their states with `imp ⊑_{φ} spec`,
- a proof that every initial state of `imp` is related by `φ` to some initial state of `spec`.

`imp ⊑_{φ} spec` is a simulation. Whenever `φ i s` holds and `imp` takes a step from `i`, `spec` can answer from `s`
and end in a state related to where `imp` ended. An input step is answered by the same input followed by internal
steps. An output step is answered by internal steps followed by the same output. An internal step is answered by
internal steps alone.

In a rewrite, `imp` is the new subgraph and `spec` is the old one. The rewritten circuit refines the original, not the
other way round.

## What refinement buys

`Graphiti/Core/Trace.lean` turns a module into a transition system whose events are inputs and outputs, and proves
`Module.refines_implies_trace_inclusion`. If `imp ⊑ spec`, every sequence of events that `imp` can produce from an
initial state, `spec` can produce too. Anyone watching only the ports cannot catch the new circuit doing something the
old one could not.

Refinement is also compositional. `refines_product`, `refines_connect` and `refines_renamePorts` show that swapping a
part of a larger module for something that refines it yields a larger module that refines the original. That is the
property a rewriter depends on. A rewrite is proved once, on its own left-hand and right-hand sides, and the result
holds in every graph where the pattern appears.

## What refinement does not buy

Trace inclusion is a safety property. It says the new circuit does nothing new. It does not say the new circuit does
anything at all.

Take a module with the same ports as `spec` whose rules never fire. Its only behaviour is the empty trace, and every
module with an initial state has the empty trace too. Such a module refines `spec`, with any `φ`, because it never
takes a step that needs answering. A rewrite that deadlocks a circuit would pass the same kind of proof.

Keep this in mind when you read that a rewrite is verified. It means the rewrite cannot add behaviour. It does not
mean the circuit still makes progress. The work under `Graphiti/Projects/Liveness`,
`Graphiti/Projects/Flushability` and `Graphiti/Projects/DeadlockRefinement.lean` looks at stronger notions.
