+++
title = "Run the tests and benchmarks"
description = "Run the Lean tests, the checks that continuous integration runs, and the Dynamatic benchmarks."
weight = 60
[menus.main]
  parent = "how-to"
  weight = 60
+++

## Run the Lean tests

```shell
lake test
```

`lakefile.toml` sets `testDriver = "GraphitiTest"`, so `lake test` builds the `GraphitiTest` library. Each test is a
`#guard_msgs` command that compares Lean's output with the expected text in the docstring above it. A mismatch is a
build error.

## Run what continuous integration runs

The `CI` workflow in `.github/workflows/build.yml` runs three commands on every push and pull request to `main`:

```shell
lake build GraphitiCore
lake build GraphitiProjects
lake test
```

`make ci` runs the first two.

## Add a test

Create a file under `GraphitiTest/`. The library includes every module that matches `GraphitiTest.+`, so there is no
list to update. There are two common forms.

Compare a value:

```lean
/-- info: true -/
#guard_msgs in
#eval parseTypeExpr " ( Bool ×   ( T × T))"
  == some (.pair .bool (.pair .nat .nat))
```

Pin the axioms of a theorem, so that a `sorry` anywhere in its proof fails the tests:

```lean
/--
info: 'Graphiti.run'_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms run'_refines
```

When the output legitimately changes, run the file, copy the new message into the docstring and check the difference
by eye.

## Run the benchmarks

The benchmarks need the executable, the oracle, `uv` and `jq`:

```shell
make -C benchmarks/dynamatic all
```

Each `NAME.dot` with a matching `NAME.json` produces `NAME-ooo.dot`. Continuous integration does not run this step, and
the job for it in `build.yml` is commented out. Remove the outputs with `make -C benchmarks/dynamatic clean`.

## Run the arbiter simulation

`examples/arbiter-simulation.bsv` compares a static and a dynamic arbiter in Bluespec. It needs the `bsc` compiler:

```shell
make -C examples test-static test-dynamic
```

`examples/README.md` records the expected cycle counts, 1023 for the static arbiter and 575 for the dynamic one.
