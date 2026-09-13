+++
title = "Command-line interface"
description = "Options, environment, processing stages and exit status of the graphiti executable."
weight = 10
[menus.main]
  parent = "reference"
  weight = 10
+++

The executable is built from `Dataflow.lean` and installed at `.lake/build/bin/graphiti`. `lake exe graphiti` runs it
through Lake.

## Synopsis

```text
graphiti [OPTIONS...] FILE
graphiti [OPTIONS...] -- FILE
```

Exactly one input file is required.

## Options

| Option | Argument | Default | Effect |
| --- | --- | --- | --- |
| `-h`, `--help` | | | Print the help text and exit with status 0. |
| `-o`, `--output` | `FILE` | standard output | Where to write the output graph. |
| `-l`, `--log` | `FILE` | none | Write the JSON log to `FILE`. |
| `--log-stdout` | | off | Print the JSON log on standard output. Ignored when `--log` is given. |
| `-m`, `--mids` | `ID...` | none | Loop head `Mux` node IDs, passed to `dynamatic-to-graphiti.py --mux-ids`. Takes every following argument up to the next one that starts with `-`. |
| `-t`, `--tag-nums` | `N` | `0` | Tag count, passed to `graphiti-to-dynamatic.py --tags`. Must be a natural number. |
| `--no-dynamatic-dot` | | off | Print the graph with Graphiti's own DOT printer and skip the output conversion script. |
| `--bluespec-dot` | | off | Print a DOT graph annotated with Bluespec types and skip the output conversion script. |
| `--no-python` | | off | Skip both conversion scripts. The input file is parsed as it is. |
| `--python` | `CMD` | `uv run` | Command used to run the scripts. It is split on spaces and must accept `--project DIR` after it. |
| `--oracle` | `PATH` | `$GRAPHITI_REPO/bin/graphiti_oracle` | Oracle executable. |
| `--parse-only` | | off | Parse and print the input without rewriting it. |
| `--fast` | | off | Use the abstraction-based pipeline, `rewriteGraphAbs`, instead of `rewriteGraphAll`. The help text describes it as fast but unverified. |
| `--no-reverse` | | | Do not undo the rewrites marked for undo. |
| `--reverse` | | on | Undo the rewrites marked for undo. This is the default. |
| `--` | `FILE...` | | End of options. The remaining arguments are joined with spaces into the input path. |

An argument that starts with a single `-` and is longer than two characters is split into one option per letter, so
`-ol` is read as `-o -l`.

## Environment

| Variable | Default | Use |
| --- | --- | --- |
| `GRAPHITI_REPO` | `.` | Repository root. The executable passes it to `--project`, looks for the scripts in `$GRAPHITI_REPO/scripts/` and uses `$GRAPHITI_REPO/bin/graphiti_oracle` as the default oracle. |

## Processing stages

1. Unless `--no-python` is given, run `scripts/dynamatic-to-graphiti.py --output TMP --mux-ids ID... -- FILE` and read
   `TMP`. Otherwise read `FILE`.
2. Parse the DOT text with `String.toExprHigh`. Node names are replaced by hashes of their port mappings, and the
   original names are kept in a separate mapping.
3. Keep only the first word of each node type, then number every node type uniquely with `to_typed_exprhigh`.
4. Unless `--parse-only` is given, rewrite:
   - without `--fast`, run `rewriteGraph` once for every node of type `initBool`,
   - with `--fast`, run `rewriteGraphAbs` once on the whole graph,
   - then, unless `--no-reverse` is given, run `reverseRewrites`.
5. Write the log if `--log` or `--log-stdout` is given.
6. Restore the original node names, following the renames recorded in the log.
7. Infer port types with `ExprHigh.infer_equalities`.
8. Print the graph. The printer is `dynamaticString` by default, `ExprHigh.toBlueSpec` with `--bluespec-dot`, and the
   `ToString` instance of `ExprHigh` with `--no-dynamatic-dot`.
9. If `--output` is given and neither `--no-python`, `--no-dynamatic-dot` nor `--bluespec-dot` is set, run
   `scripts/graphiti-to-dynamatic.py --output FILE --tags N TMP` on the printed graph. Otherwise write the printed graph
   directly, to the output file or to standard output.

Without `--output`, standard output receives the result of stage 8 even in the default mode, so it is not converted by
`graphiti-to-dynamatic.py`.

## Progress output

Each rewriting stage prints a numbered heading, then a count of the rewrites it applied and its run time. Without
`--fast`, one section runs per loop:

```text
1. Rewriting the main loop
  1.1. Normalising IO ports for the loop | ...
  1.2. Generating a pure node for the loop body | ...
  1.3. Applying the loop rewrite | ...
2. Reconstructing graph from pure
```

The run ends with a `Total:` line and the total time.

## Exit status

| Status | Cause |
| --- | --- |
| 0 | Success, or `--help`. |
| 1 | The arguments could not be parsed. The tool prints `error: ` and the message, then the help text. |
| 1 | A rewrite failed. The tool prints the error and writes the log up to that point. |
| non-zero | An uncaught IO error, for example when the oracle or a Python script cannot be started. |

Argument errors include `no input file passed`, `more than one input file passed`, `argument '...' not recognised` and
`could not parse a number: ...`.
