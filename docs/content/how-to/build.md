+++
title = "Build Graphiti"
description = "Build the Lean libraries, the proofs, the executable and this manual."
weight = 10
[menus.main]
  parent = "how-to"
  weight = 10
+++

## Install Lean

Install [elan](https://github.com/leanprover/elan). The first `lake` command in the repository reads `lean-toolchain`
and installs the pinned Lean version, currently `leanprover/lean4:v4.34.1`.

## Fetch the mathlib cache

```shell
make setup
```

This runs `lake exe cache get`. Skip it and Lake builds mathlib from source, which takes hours.

## Build a Lean target

Pick the target that covers what you need:

| Command | Builds |
| --- | --- |
| `lake build` | The default `Graphiti` library: `Graphiti.Core.Graph`, `Graphiti.Core.Dataflow` and their imports. |
| `lake build GraphitiCore` | Every module under `Graphiti/Core`, including the proofs such as `LoopImplementationProof`. |
| `lake build GraphitiProjects` | Every module under `Graphiti/Projects`. |
| `lake build GraphitiTest` | The test modules. `lake test` does the same. |
| `lake build Graphiti.Core.Rewriter` | One module and the modules it imports. |

`make ci` runs the same two builds as continuous integration, `GraphitiCore` and then `GraphitiProjects`.

## Check a single file

```shell
lake env lean path/to/File.lean
```

This works for files that no library includes, such as scratch files or anything in `Graphiti/Experimental`. The
experimental files are not guaranteed to build.

## Build the executable

The `graphiti` executable needs the rewrite oracle, which is a Rust program. Install
[Rust and cargo](https://www.rust-lang.org/tools/install), then run:

```shell
make build-exe
```

The target installs the oracle with
`cargo install --git https://github.com/VCA-EPFL/OracleGraphiti --locked --root .`, which puts it in
`bin/graphiti_oracle`. It then runs `lake build graphiti`, which compiles `Dataflow.lean` to
`.lake/build/bin/graphiti`. The oracle step only runs if `bin/graphiti_oracle` does not exist yet.

## Set up Python

By default the executable converts graphs with the scripts in `scripts/`, calling them through `uv run --project
<repository>`. Install [uv](https://docs.astral.sh/uv/). The first run creates an environment from `pyproject.toml`,
which asks for Python 3.14 or newer with `networkx` and `pydot`.

Pass `--no-python` to the executable if you want to skip the scripts and feed it graphs that are already in Graphiti's
format.

## Build this manual

The manual is a [Hugo](https://gohugo.io/) site in `docs/`. Preview it with live reload:

```shell
cd docs
hugo server
```

Run `hugo` instead to write the static site to `docs/public`, which git ignores.
