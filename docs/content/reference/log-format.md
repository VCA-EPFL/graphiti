+++
title = "Log format"
description = "Fields of the JSON log written by --log and --log-stdout."
weight = 20
[menus.main]
  parent = "reference"
  weight = 20
+++

The log is a JSON array. Each element is one `RuntimeEntry` from `Graphiti/Core/Rewriter.lean`, in the order the
entries were recorded. The JSON encoding comes from the `Lean.ToJson (RuntimeEntry Ident Typ)` instance in the same
file.

## Entry fields

| Field | JSON type | Content |
| --- | --- | --- |
| `type` | string | The entry type, printed with Lean's `repr`. See the next table. |
| `name` | string or `null` | Name of the rewrite, such as `"pure-seq-comp"`. Undo steps are named `"rev-"` followed by the original name. |
| `input_graph` | string | The graph before the step, as Lean `repr` output for an `ExprHigh` value. |
| `output_graph` | string | The graph after the step, in the same format. |
| `matched_subgraph` | array of strings | Names of the matched nodes, in the order the pattern returned them. |
| `matched_subgraph_types` | array of `[string, number]` | Types of the matched nodes, in the same order. |
| `renamed_input_nodes` | object | Maps each matched node to its name in the output graph, or to `null` if the rewrite removed it. |
| `new_output_nodes` | array of strings | Names of nodes the rewrite created. |
| `fresh_types` | `[string, number]` | The fresh type counter when the step started. |
| `debug` | string or `null` | Free-form text. Rewrites use it for intermediate values while they run. |

Node names in the log are the hashed names Graphiti uses internally, not the names from the input file.

## Entry types

| `type` value | Written by |
| --- | --- |
| `Graphiti.EntryType.rewrite` | A rewrite that finished. `Rewrite.run'` overwrites its own debug entry with this type at the end. |
| `Graphiti.EntryType.debug` | `Rewrite.run'` after a pattern matches, `reverse_rewrite'`, and `RuntimeEntry.debugEntry`. |
| `Graphiti.EntryType.marker "rev-stop"` | `withUndo`, before the steps it wraps. |
| `Graphiti.EntryType.marker "rev-start"` | `withUndo`, after the steps it wraps. |
| `Graphiti.EntryType.abstraction` | Defined, not written by the current pipeline. |
| `Graphiti.EntryType.concretisation` | Defined, not written by the current pipeline. |

A rewrite whose pattern does not match leaves no entry. Pattern matching happens before `Rewrite.run'` records
anything.

## Undo markers

`reverseRewrites` reads the log from the newest entry to the oldest and skips debug entries. It collects the rewrite
entries between each `rev-start` marker and the `rev-stop` marker before it, builds the inverse of each rewrite with
`reverse_rewrite`, and applies the inverses newest first. Marker entries carry no graph data.

## Example

An abridged rewrite entry:

```json
{
  "type": "Graphiti.EntryType.rewrite",
  "name": "pure-seq-comp",
  "input_graph": "{ modules := Batteries.AssocList.cons ... }",
  "output_graph": "{ modules := Batteries.AssocList.cons ... }",
  "matched_subgraph": ["c1f02e4a", "8b1d77f0"],
  "matched_subgraph_types": [["pure", 12], ["pure", 15]],
  "renamed_input_nodes": {"c1f02e4a": null, "8b1d77f0": null},
  "new_output_nodes": ["a6875d39"],
  "fresh_types": ["", 40],
  "debug": "..."
}
```

The node names and numbers above are illustrative.
