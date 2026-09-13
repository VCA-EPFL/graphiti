+++
title = "Graph syntax"
description = "The [graph| ... ] term syntax for writing ExprHigh graphs in Lean."
weight = 30
[menus.main]
  parent = "reference"
  weight = 30
+++

`Graphiti/Core/Graph/ExprHighElaborator.lean` defines a DOT-like term syntax that elaborates to an `ExprHigh` value.
The syntax is scoped, so it is only available inside `namespace Graphiti` or after `open Graphiti`.

## Form

```lean
[graph|
    NODE_OR_EDGE;
    NODE_OR_EDGE;
    ...
  ]
```

Every statement ends with `;`.

A node statement names an instance and gives its attributes:

```lean
f [type = "pure", arg = $(0)];
```

An edge statement connects two instances:

```lean
f -> g [from = "out1", to = "in1"];
```

Both statement kinds need an attribute list in square brackets. Attributes are separated by commas.

## Attribute values

| Form | Example |
| --- | --- |
| String literal | `"pure"` |
| Number literal | `3` |
| Identifier | `true` |
| Lean term | `$(M + 1)`, `$(T[0])` |

## Node attributes

| Attribute | Required | Meaning |
| --- | --- | --- |
| `type` | yes | The component type. The value `"io"` marks an external port instead of a component. A `$(...)` term of type `String` is accepted. |
| `arg` | depends on the target type | The second half of the node type. See the next section. Not read for `io` nodes. |
| `cluster` | no | `true` or `false`, default `false`. Port names of a cluster node are used as written instead of being prefixed with the node name. |

Other attributes are accepted and ignored by `[graph| ... ]`.

## Target types

The elaborator looks at the expected type of the term.

| Expected type | Node type stored | `arg` |
| --- | --- | --- |
| `ExprHigh String String`, or no expected type | the `type` string | not read |
| `ExprHigh String (String × Nat)` | `(type, arg)` | required, a `Nat` literal or term |
| any other `ExprHigh String _` | `(type, arg)` | required, a `String` literal or term |

`io` nodes never appear in the result, whatever the target type.

## Edge attributes

| Attribute | Meaning |
| --- | --- |
| `from` | The output port name on the source node. |
| `to` | The input port name on the target node. |

## Ports

Each non-`io` node gets a `PortMapping`. Its keys are the node's own port names as top-level ports, for example
`⟨.top, "in1"⟩`. Its values are the wire names used in the graph. An edge between two component nodes creates a
`Connection` and sets both sides:

```lean
f -> g [from = "out1", to = "in1"];
-- f: output ⟨.top, "out1"⟩ ↦ ⟨.internal "f", "out1"⟩
-- g: input  ⟨.top, "in1"⟩  ↦ ⟨.internal "g", "in1"⟩
-- connection ⟨.internal "f", "out1"⟩ → ⟨.internal "g", "in1"⟩
```

An edge from or to an `io` node creates no connection. It maps the component's port to a top-level port named after
the `io` node:

```lean
src -> f [to = "in1"];     -- f: input  ⟨.top, "in1"⟩  ↦ ⟨.top, "src"⟩
g -> snk [from = "out1"];  -- g: output ⟨.top, "out1"⟩ ↦ ⟨.top, "snk"⟩
```

On the `io` side of such an edge, `from` or `to` can be left out, and the port takes the name of the `io` node. On a
component side they are required.

A port value that contains a dot, such as `"a.b"`, is read as the internal port `⟨.internal "a", "b"⟩`.

## Errors

| Message | Cause |
| --- | --- |
| `Element list is not present` | A node statement has no `[...]`. |
| ``No `type` attribute found at node`` | A node has no `type`, or an edge has no `[...]`. |
| ``No `arg` attribute found at node`` | The target type needs `arg` and a component node lacks it. |
| `Multiple references to NAME found` | Two node statements use the same name. |
| `Instance has not been declared: NAME` | An edge refers to a node that was not declared before it. |
| `Both the output ... and input ... are IO ports` | An edge connects two `io` nodes. |
| `No output found for: ...`, `No input found for: ...` | A component side of an edge lacks `from` or `to`. |

## Related syntax

`[graphEnv| ... ]` reads the same statements and returns a pair of an `ExprHigh String String` and an association list
from type names to modules. A node can give its module directly with `typeImp = $(⟨_, module⟩)`, and the elaborator
checks that connected ports have the same Lean type. The file also defines `[graphv2| ... ]`.
