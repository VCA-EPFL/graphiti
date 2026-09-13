+++
title = "Components"
description = "The dataflow components in Component.lean, their ports and their behaviour."
weight = 50
[menus.main]
  parent = "reference"
  weight = 50
+++

Components are defined in `Graphiti/Core/Dataflow/Component.lean`. Each one is first written as a `NatModule`, with
ports numbered from 0, and then converted to a `StringModule` by `NatModule.stringify`. Input port `n` becomes `in{n+1}`
and output port `n` becomes `out{n+1}`, so the first input is always `in1`.

Every component stores its pending values in lists, so each port behaves like an unbounded buffer. An input rule that
has no successor state blocks, which is how a component refuses input.

## Components with a graph type

`Env.well_formed` ties these type strings to components. A well-formed environment must map a node type whose name is
in the first column to the component in the second column, for some choice of the Lean types. Type strings that are not
in this table are not constrained.

| Type string | Lean definition | Ports | Behaviour |
| --- | --- | --- | --- |
| `queue` | `StringModule.queue T` | `in1`, `out1` | First in, first out. |
| `pure` | `StringModule.pure f` | `in1 : S`, `out1 : T` | Stores `f v` for each input `v` and outputs the results in order. |
| `fork2` | `StringModule.fork2 T` | `in1`, `out1`, `out2` | Copies each input into two queues, one per output. |
| `fork` | `StringModule.fork T n` | `in1`, `out1` to `out{n}` | Copies each input into `n` queues. |
| `merge` | `StringModule.merge T n` | `in1` to `in{n}`, `out1` | Stores values from any input and outputs any stored value. |
| `merge2` | `StringModule.merge T 2` | `in1`, `in2`, `out1` | `merge` with two inputs. |
| `cntrl_merge` | `StringModule.cntrl_merge T` | `in1`, `in2`, `out1 : T`, `out2 : Bool` | Queues values in arrival order. `out2` reports `true` for a value from `in1` and `false` for one from `in2`. |
| `join` | `StringModule.join T T'` | `in1 : T`, `in2 : T'`, `out1 : T × T'` | Pairs the oldest value from each input. |
| `split` | `StringModule.split T T'` | `in1 : T × T'`, `out1 : T`, `out2 : T'` | Splits each pair into two queues. |
| `branch` | `StringModule.branch T` | `in1 : T`, `in2 : Bool`, `out1`, `out2` | Sends the oldest value to `out1` if the oldest condition is `true` and to `out2` if it is `false`. |
| `mux` | `StringModule.mux T` | `in1 : Bool`, `in2 : T`, `in3 : T`, `out1 : T` | Reads the oldest condition. `true` takes the oldest value from `in3`, `false` from `in2`. |
| `init` | `StringModule.init T d` | `in1`, `out1` | Outputs `d` once without reading an input, then behaves as a queue. |
| `initBool` | `StringModule.init Bool false` | `in1 : Bool`, `out1 : Bool` | `init` fixed to `Bool` and `false`. |
| `sink` | `StringModule.sink T n` | `in1` to `in{n}` | Accepts and discards every value. |
| `constant` | `StringModule.constant t` | `in1 : Unit`, `out1 : T` | Outputs `t` once for each token received. |
| `operator1` | `StringModule.operator1 T₁ T s` | `in1`, `out1` | Applies the opaque function `op1_function s`. |
| `operator2` | `StringModule.operator2 T₁ T₂ T s` | `in1`, `in2`, `out1` | Applies the opaque function `op2_function s` to the oldest pair of inputs. |
| `operator3` | `StringModule.operator3 T₁ T₂ T₃ T s` | `in1` to `in3`, `out1` | Applies the opaque function `op3_function s`. |
| `load` | `StringModule.load S T` | `in1 : S`, `in2 : T`, `out1 : S`, `out2 : T` | Two independent queues, `in1` to `out1` and `in2` to `out2`. |
| `tagger_untagger_val` | `StringModule.tagger_untagger_val TagT T T'` | `in1 : TagT × T'`, `in2 : T`, `out1 : TagT × T`, `out2 : T'` | See below. |
| `tagger_untagger_val_ghost` | `StringModule.tagger_untagger_val_ghost TagT T` | as above, with ghost data | Proof-only variant used by the loop rewrite proof. |

### Tagger and untagger

`tagger_untagger_val` holds a list of tags in allocation order, a map from tags to results and a queue of values waiting
for a tag.

- `in2` queues a value from outside the tagged region.
- `out1` takes the oldest queued value, pairs it with a tag that is not in use and appends the tag to the order.
- `in1` accepts a result for a tag that is in use and has no result yet.
- `out2` outputs the result for the oldest tag once that result has arrived, and frees the tag.

Results can come back in any order, and `out2` still releases them in the order the values went in.

The loop rewrite `LoopRewrite2` and the Dynamatic printer use the type string `tag_untagger_val` for this component.
`Env.well_formed` constrains the string `tagger_untagger_val`.

## Components without a graph type

These are defined in `Component.lean` but have no entry in `Env.well_formed`.

| Lean definition | Ports | Behaviour |
| --- | --- | --- |
| `StringModule.bag T` | `in1`, `out1` | Outputs any stored value. |
| `StringModule.merge' T n` | `in1` to `in{n}`, `out1` | Merge that outputs values in arrival order. |
| `StringModule.muxC T` | `in1 : Bool`, `in2`, `in3`, `out1 : T × Bool` | `mux` that also outputs the condition. |
| `StringModule.joinC T T' T''` | `in1 : T`, `in2 : T' × T''`, `out1 : T × T'` | `join` that drops the second half of its second input. |
| `StringModule.tagger TagT T` | `in1 : T`, `in2 : TagT`, `out1 : TagT × T` | `in1` tags a value with an unused tag, `in2` frees a tag. |
| `StringModule.aligner TagT T` | `in1`, `in2 : TagT × T`, `out1` | Outputs a pair of values with the same tag, one from each input. |
| `StringModule.unary_op f`, `binary_op f`, `ternary_op f` | one, two or three inputs, `out1` | Apply `f` to the oldest input values. |
| `StringModule.cast S T` | `in1`, `out1` | `unary_op` with the opaque function named `cast`. |
| `StringModule.sync`, `sync1` | `in1 : S`, `in2 : T`, `out1 : T` | Each output consumes the oldest `S` and outputs the oldest `T`. `sync1` holds at most one `S`. |
| `StringModule.dsync f`, `dsync1 f`, `dsyncU`, `dsync1U` | `in1 : T`, `out1 : S`, `out2 : T` | Duplicate each input into `f` applied to it and the value itself. |
| `StringModule.FixedSize.join T T' n`, `joinL T T' T'' n` | two inputs, `out1` | Join variants whose lists hold at most `n` values. |
| `StringModule.empty` | none | No ports and no behaviour. |

`NatModule.io T` and `NatModule.tagger_untagger` exist only as `NatModule` definitions.

## Operator functions

`operator1`, `operator2`, `operator3` and `cast` apply the `opaque` functions `op1_function`, `op2_function` and
`op3_function`, indexed by the operator name string. Because the functions are opaque, a proof about an operator node
holds for whatever the operator computes.
