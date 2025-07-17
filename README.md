# Graphiti

## How to build

The following commands should successfully build the project.

```shell
# Setup the build and runtime dependencies
make setup
# Build Graphiti
lake build
```

## Executing the rewriter

Graphiti can be executed using:

```shell
lake exe graphiti tests/mulvec.dot -o out.dot -l out.json --no-dynamatic-dot
```

```text
$ lake exe graphiti --help
graphiti -- v0.1.0

FORMAT
  graphiti [OPTIONS...] FILE

OPTIONS
  -h, --help          Print this help text
  -o, --output FILE   Set output file
  -l, --log FILE      Set JSON log output
  --log-stdout        Set JSON log output to STDOUT
  --no-dynamatic-dot  Don't output dynamatic DOT, instead output the raw
                      dot that is easier for debugging purposes.
  --parse-only        Only parse the input without performing rewrites.
```

It will read a DOT graph from the input FILE, and then rewrite it using the internal rewrites.  It will then print it as
a dynamatic dot graph to the output.

The rewrites that were performed can be traced using the output JSON log file.  This log file outputs data in the
following format:

```json5
// List of objects, each representing a rewrite.
[
  {
    // name of the rewrite
    "name": "combine-mux",
    // type of rewrite, one of rewrite, abstraction or concretisation
    "type": "Graphiti.RewriteType.rewrite",
    // input dot graph that was received by the rewrite
    "input_graph": "digraph { ... }",
    // output dot graph that was produced by the rewrite
    "output_graph": "digraph { ... }",
    // a list of nodes making up the subgraph that was matched
    "matched_subgraph": ["node1", "node2"],
    // nodes that were untouched but renamed when going from input to output
    // a null value means the node was removed
    "renamed_input_nodes": {"a": "b", "c": "d", "e": null},
    // name of nodes that were added to the output
    "new_output_nodes": ["x", "y", "z"],
    // optional debug information
    "debug": null
  },
  { "...": "..." }
]
```
