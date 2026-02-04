<picture class="logo">
  <source media="(prefers-color-scheme: dark)" srcset="/docs/static/img/graphiti-logo-white.svg" />
  <source media="(prefers-color-scheme: light)" srcset="/docs/static/img/graphiti-logo.svg" />
  <img src="/img/graphiti-logo.svg" width="75%" />
</picture>

## How to build

The following commands should successfully build the project.

```shell
# Setup the mathlib 4 cache
make setup
# Build Graphiti
lake build
```

The executable `graphiti` can be built using the following, which requires an [installation of `rust` and
`cargo`](https://www.rust-lang.org/tools/install) to install the oracle which is used for the rewrites.

```shell
make build-exe
```

The oracle will be installed under `./bin/graphiti_oracle`.

## Executing the rewriter

Graphiti can be executed using:

```shell
lake exe graphiti --oracle ./bin/graphiti_oracle ./benchmarks/correct/gcd.dot -o out.dot -l out.json --no-dynamatic-dot
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

## Code structure

The repository follows the structure proposed by the [Research Codebase Manifesto](https://www.moderndescartes.com/essays/research_code/).

- `Graphiti/Core`:
> Libraries for reusable components like cloud data storage, notebook tooling, neural network libraries, model serialization/deserialization, statistics tests, visualization, testing libraries, hyperparameter optimization frameworks, wrappers and convenience functions built on top of third-party libraries. Engineers typically work here.  Code is reviewed to engineering standards. Code is tested, covered by continuous integration, and should never be broken. Very low tolerance for tech debt.  Breaking changes to core code should be accompanied by fixes to affected project code. The project owner should assist in identifying potential breakage. No need to fix experimental code.

- `Graphiti/Projects`:
> A new top-level folder for each major effort (rough criteria: a project represents 1-6 months of work). Engineers and researchers work here.  Code is reviewed for correctness. Testing is recommended but optional, as is continuous integration.  No cross-project dependencies. If you need code from a different project, either go through the effort of polishing the code into core, or clone the code.
- `Graphiti/Experimental`:
> Anything goes. Typically used by researchers. I suggest namespacing by time (e.g. a new directory every month).  Rubber-stamp approvals. Code review is optional and comments may be ignored without justification. Do not plug this into continuous integration.  The goal of this directory is to create a safe space for researchers so that they do not need to hide their work. By passively observing research code “in the wild”, engineers can understand research pain points.  Any research result that is shared outside the immediate research group may not be derived from experimental code.
