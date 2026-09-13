+++
title = "DOT input format"
description = "What the DOT parser accepts and how Dynamatic node types map to Graphiti types."
weight = 40
[menus.main]
  parent = "reference"
  weight = 40
+++

The executable parses its input with `String.toExprHigh` from `Graphiti/Core/Dataflow/DotParser.lean`. In the default
mode the input first goes through `scripts/dynamatic-to-graphiti.py`, so this page describes the file that script
writes. With `--no-python` it describes the input file itself.

## Grammar

```text
graph     ::= ("digraph" | "Digraph") ID? "{" stmt* "}"
stmt      ::= comment? (edge ";" | node ";" | attr ";" | subgraph)
node      ::= ID attrs?
edge      ::= ID "->" ID attrs?
attr      ::= ID "=" ID
attrs     ::= "[" attr ("," attr)* ","? "]"
subgraph  ::= "subgraph" ID? "{" stmt* "}"
comment   ::= "//" text up to the end of the line
ID        ::= identifier | quoted string | number
```

An identifier starts with a letter or `_` and continues with letters, digits and `_`. Quoted strings accept JSON
escapes. Graph-level attribute statements such as `splines=spline;` are parsed and dropped. The nodes and edges inside
a subgraph are added to the top-level graph.

## Node attributes

| Attribute | Required | Use |
| --- | --- | --- |
| `type` | yes | Dynamatic node type, such as `Mux`. Translated as described below. |
| `in` | no | Input ports and widths, for example `"in1?:1 in2:32 in3:32"`. The widths select the Graphiti type. |
| `out` | no | Output ports and widths, for example `"out1+:32 out2-:32"`. |
| `op` | for `Operator` | Operator name such as `add_op`. |
| `value` | for `Constant` | Hexadecimal value starting with `0x`. |
| `cluster` | no | `true` or `false`. See the note below. |

The parser keeps a fixed set of attributes per node and passes them to the Dynamatic printer unchanged: `bbID`,
`graphiti_metadata`, `in`, `out`, `tagged`, `taggers_num` and `tagger_id` for types other than `MC`, `Sink` and `Exit`,
`delay` for `Mux` and `Merge`, `control` for `Entry`, `value` for `Constant`, `portId` and `offset` for
`mc_store_op` and `mc_load_op` operators, `delay`, `latency`, `II`, `constants` and `op` for `Operator`, and `memory`,
`bbcount`, `ldcount` and `stcount` for `MC`.

The parser passes the `cluster` value to `updateNodeMaps` in the position of the IO flag. A node with
`cluster = true` therefore becomes a top-level port rather than a component.

## Edge attributes

| Attribute | Meaning |
| --- | --- |
| `from` | Output port on the source node. |
| `to` | Input port on the target node. |

The port rules are the same as for the [graph syntax]({{< relref "graph-syntax" >}}).

## Type translation

`dynamaticToGraphiti` in `Graphiti/Core/Dataflow/DynamaticTypes.lean` looks up the Dynamatic type together with the
input and output widths in the `dynamatic_types` table and returns the first match. An empty width in the table
matches any width. A type with no match becomes `_graphiti_` followed by the Dynamatic type.

| Graphiti type | Dynamatic type | Input widths | Output widths |
| --- | --- | --- | --- |
| `join` | `Concat` | any, any | any |
| `split` | `Split` | any | any, any |
| `branch` | `Branch` | any, 1 | any, any |
| `fork2` to `fork10` | `Fork` | any | 2 to 10 outputs, any width |
| `merge2` | `Merge` | any, any | any |
| `operator1` to `operator5` | `Operator` | 1 to 5 inputs of 32 | 32 |
| `cond_operator1` to `cond_operator3` | `Operator` | 1 to 3 inputs of 32 | 1 |
| `mc` | `MC` | 32 | 32, 0 |
| `mux` | `Mux` | 1, any, any | any |
| `input` | `Entry` | 0 | 0 |
| `inputNat` | `Entry` | 32 | 32 |
| `inputBool` | `Entry` | 1 | 1 |
| `output0` to `output5` | `Exit` | 0 to 5 inputs, any width | 0 |
| `outputNat0` to `outputNat5` | `Exit` | 0 to 5 inputs, any width | 32 |
| `outputBool0` to `outputBool5` | `Exit` | 0 to 5 inputs, any width | 1 |
| `sink` | `Sink` | any | none |
| `constantNat` | `Constant` | 0 | 32 |
| `constantBool` | `Constant` | 0 | 1 |
| `initBool` | `Init` | 1 | 1 |
| `tag_untagger_val` | `TaggerUntagger` | any, any | any, any |
| `load` | `Operator` | 32, 32 | 32, 32 |

`graphitiToDynamatic` applies the table in the other direction when printing. It strips the `_graphiti_` prefix from
untranslated types and prints `__unknown__` before any other type it does not know.

## Names

After parsing, `String.toExprHigh` renames every node to `PortMapping.hashPortMapping` of its ports, the first eight hex
digits of a hash. It returns the mapping from hashed names back to the original names, and the executable uses it to
restore the names before printing.
