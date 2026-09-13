+++
title = "Rewrite a Dynamatic benchmark"
description = "Build the graphiti executable and run it on one of the bundled Dynamatic circuits."
weight = 20
[menus.main]
  parent = "tutorials"
  weight = 20
+++

In this tutorial we build the `graphiti` executable and run it on `gsum_single`, one of the Dynamatic circuits that
ship with the repository. We end with a rewritten circuit in Dynamatic's DOT format and a JSON log of every rewrite
that produced it.

You need these tools on your path:

- [elan](https://github.com/leanprover/elan) for Lean,
- [Rust with cargo](https://www.rust-lang.org/tools/install) to install the rewrite oracle,
- [uv](https://docs.astral.sh/uv/) to run the Python conversion scripts,
- [jq](https://jqlang.org/) because the benchmark Makefile reads its settings from JSON.

## Build the executable

From the root of the repository:

```shell
make setup
make build-exe
```

`make build-exe` does two things. It installs the oracle from
[VCA-EPFL/OracleGraphiti](https://github.com/VCA-EPFL/OracleGraphiti) into `bin/graphiti_oracle`, and then it runs
`lake build graphiti`, which compiles `Dataflow.lean` into `.lake/build/bin/graphiti`.

Check that the binary runs:

```shell
.lake/build/bin/graphiti --help
```

The first line of the help text is `graphiti -- v0.1.0`, followed by the list of options.

## Look at the benchmark

Move into the benchmark directory:

```shell
cd benchmarks/dynamatic
ls
```

Every benchmark is a pair of files. `gsum_single.dot` is the circuit as Dynamatic wrote it. Each node has a `type` such
as `Mux`, `Branch` or `Operator`, and port widths in its `in` and `out` attributes:

```text
"phi_1" [type = "Mux", bbID= 2, in = "in1?:1 in2:32 in3:32 ", out = "out1:32", ...];
```

`gsum_single.json` holds the two settings Graphiti needs for this circuit:

```json
{
    "mux-ids": ["phi_1"],
    "tags": 10
}
```

`phi_1` is the `Mux` at the head of the loop we want to transform. `tags` is the number of tags handed to the tagging
logic that the rewrite inserts.

## Run Graphiti

Ask `make` for the rewritten circuit:

```shell
make gsum_single-ooo.dot
```

The Makefile turns the JSON settings into command-line options and runs:

```shell
../../.lake/build/bin/graphiti --output gsum_single-ooo.dot --mids phi_1 --tag-nums 10 -- gsum_single.dot
```

It also exports `GRAPHITI_REPO=../..`, which is how the executable finds `scripts/` and `bin/graphiti_oracle` from
inside the benchmark directory.

While it runs, the tool prints numbered stages, each followed by the number of rewrites it applied and the time it took.
The headings are:

```text
1. Rewriting the main loop
  1.1. Normalising IO ports for the loop | ...
  1.2. Generating a pure node for the loop body | ...
  1.3. Applying the loop rewrite | ...
2. Reconstructing graph from pure
```

The last line gives the total run time.

## Look at the result

`gsum_single-ooo.dot` is a Dynamatic circuit again, so Dynamatic can take it from here. Count the node types before and
after:

```shell
grep -o 'type = "[A-Za-z]*"' gsum_single.dot | sort | uniq -c
grep -o 'type = "[A-Za-z]*"' gsum_single-ooo.dot | sort | uniq -c
```

The loop no longer has the `Mux` and `Branch` pair that Dynamatic generated for `phi_1`. In its place is the tagging
structure from the loop rewrite, which lets a new iteration enter the loop before the previous one leaves.

## Record what happened

The Makefile passes anything in `GRAPHITI_FLAGS` straight to the tool. Run it again with a log file, using `-B` so
`make` rebuilds the output:

```shell
make -B gsum_single-ooo.dot GRAPHITI_FLAGS="--log gsum_single-log.json"
```

The log is a JSON array with one object per step. List the rewrites by name and count them:

```shell
jq -r '.[] | select(.type == "Graphiti.EntryType.rewrite") | .name' gsum_single-log.json | sort | uniq -c
```

The names match the `name` field of each rewrite in `Graphiti/Core/Dataflow/Rewrites`, for example `fork-3`,
`pure-seq-comp` and `loop-rewrite`. Names that start with `rev-` are rewrites that were undone during the
"Reconstructing graph from pure" stage.

## Clean up

Remove the generated circuit with:

```shell
make clean
```

`make all` rebuilds every benchmark in the directory.

## What you did

You built the executable and the oracle, ran Graphiti on a Dynamatic loop with the settings from its JSON file, and read
the log to see which rewrites fired. To do the same with a circuit of your own, follow
[Rewrite your own Dynamatic circuit]({{< relref "/how-to/rewrite-your-own-circuit" >}}). To understand the stages you
saw scroll past, read [The rewriting pipeline]({{< relref "/explanation/rewriting-pipeline" >}}).
