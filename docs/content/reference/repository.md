+++
title = "Repository layout"
description = "What lives where in the repository, which Lake target builds it, and the state of each project."
weight = 90
[menus.main]
  parent = "reference"
  weight = 90
+++

## Top level

| Path | Contents |
| --- | --- |
| `Graphiti.lean` | Root of the default `Graphiti` library. Imports `Graphiti.Core.Graph` and `Graphiti.Core.Dataflow`. |
| `Dataflow.lean` | Source of the `graphiti` executable. |
| `Graphiti/Core/` | Reusable definitions and proofs. |
| `Graphiti/Projects/` | One file or directory per research effort. |
| `Graphiti/Experimental/` | Work in progress. Not part of any Lake target and not guaranteed to build. |
| `GraphitiTest/` | `#guard_msgs` tests. |
| `scripts/` | Python conversion between Dynamatic and Graphiti DOT files. |
| `benchmarks/dynamatic/` | Dynamatic circuits, their JSON settings and a Makefile that runs Graphiti on them. |
| `tests/` | Sample DOT graphs. No target uses them. |
| `examples/` | A Bluespec simulation comparing a static and a dynamic arbiter. |
| `docs/` | This manual, a Hugo site. |
| `bin/` | Created by `make build-exe` to hold `graphiti_oracle`. Ignored by git. |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake configuration, locked dependencies and the Lean version. |
| `pyproject.toml`, `uv.lock`, `.python-version` | Python project for the scripts. |
| `Makefile` | Targets `setup`, `build`, `build-exe`, `ci` and `help`. |
| `AGENTS.md` | Rules for writing proofs in this repository. `CLAUDE.md` is a link to it. |
| `CITATION.cff` | Citation metadata for the ASPLOS'26 paper. |
| `.github/workflows/` | `build.yml` for continuous integration and `update-mathlib-version.yml` for toolchain updates. |

## Lake targets

| Target | Kind | Contents |
| --- | --- | --- |
| `Graphiti` | library, default | `Graphiti.lean` and its imports. |
| `GraphitiCore` | library | Modules matching `Graphiti.Core.+`. |
| `GraphitiProjects` | library | Modules matching `Graphiti.Projects.+`. |
| `GraphitiTest` | library, test driver | Modules matching `GraphitiTest.+`. |
| `graphiti` | executable | Root module `Dataflow`. |

`lakefile.toml` sets `autoImplicit = false` for every target and turns off a number of linters. The only dependency
is mathlib, pinned to the same tag as the Lean version.

## Graphiti/Core

| Path | Contents |
| --- | --- |
| `Basic.lean`, `BasicLemmas.lean` | Small utilities, simprocs that compute `toString` on literals, and supporting lemmas. |
| `Simp.lean` | Registration of the `dr...` simp sets. |
| `Types.lean` | Ports, port maps and port mappings. |
| `AssocList/` | Extra functions and lemmas for `Batteries.AssocList`, including `bijectivePortRenaming`. |
| `StateTransition.lean` | Generic transition systems and their behaviours. |
| `Trace.lean`, `StateTrace.lean` | Modules as transition systems, and the proof that refinement implies trace inclusion. |
| `Tactic.lean` | Custom tactics. |
| `Graph/Module.lean`, `Graph/ModuleLemmas.lean` | `Module`, its operations, refinement and the refinement lemmas. |
| `Graph/ModuleReduction.lean` | `def_module`, `dr_reduce_module` and the simprocs behind them. |
| `Graph/ExprLow.lean`, `Graph/ExprLowLemmas.lean` | `ExprLow`, its operations, `build_module` and the proofs that reordering preserves refinement. |
| `Graph/ExprHigh.lean`, `Graph/ExprHighLemmas.lean` | `ExprHigh`, conversion to and from `ExprLow`, and naming. |
| `Graph/ExprHighElaborator.lean` | The `[graph| ... ]` syntax. |
| `Graph/Environment.lean` | `Env` and `FinEnv`. |
| `Graph/WellTyped.lean` | Well-typedness of graph expressions. |
| `Rewriter.lean`, `RewriterLemmas.lean` | The rewriting engine and its correctness theorem. |
| `Dataflow/Component.lean` | Component definitions and `Env.well_formed`. |
| `Dataflow/Rewrites/`, `Dataflow/Rewrites.lean` | One file per rewrite, proofs, `rewrite_index` and `reverseRewrites`. |
| `Dataflow/DotParser.lean` | DOT parser. |
| `Dataflow/DynamaticTypes.lean` | Table between Dynamatic and Graphiti node types. |
| `Dataflow/DynamaticPrinter.lean` | Dynamatic DOT printer. |
| `Dataflow/BluespecPrinter.lean` | DOT printer with Bluespec types, used by `--bluespec-dot`. |
| `Dataflow/TypeExpr.lean` | Type and value expressions and a parser for type strings. |
| `Dataflow/InferTypes.lean` | Union-find inference of port types. |
| `Dataflow/JSLang.lean` | Interface to the oracle. |
| `Dataflow/JsonParser.lean` | JSON encoding of `ExprHigh`, with `parseGraph` and `printGraph`. Not imported by `Graphiti.Core.Dataflow`. |
| `Netlist/VerilogExport.lean` | Verilog text from an `ExprHigh` graph and a table of instance templates. |

## Graphiti/Projects

| Path | Topic | Contains `sorry` |
| --- | --- | --- |
| `AnalogCircuit.lean` | Modules over continuous-time signals, with results about resistor, RC and NAND circuits such as `nand_both_high`. | no |
| `CombinationalStream.lean` | Combinational circuits over streams. Proves that a full adder implementation refines its specification, with an axiom check. | no |
| `DeadlockRefinement.lean` | Refinement between a module and the same module with an extra internal no-op step. | yes |
| `Flushability/` | Confluence, determinism and flushed modules, including `flushed_refines_nonflushed`, and a join rewrite proof. | yes |
| `Liveness/` | Liveness of composed modules, such as `gcompf_wellness_implies_liveness`, and module histories. | in some files |
| `Noc/` | A language for networks on chip, mesh and torus topologies, and a correctness proof against bag and queue specifications. | yes |
| `CFG/` | Translation of control-flow graph nodes into dataflow nodes with `RewriteHigh`, with a GCD example. | no |
| `TaggerRewrites/` | Rewrites that fuse taggers and move a tagger out of a branch. | no |

## Graphiti/Experimental

Files for join, merge and tagged mux rewrites and their proof attempts, a bag and queue refinement, a two-phase commit
model, network-on-chip correctness work under `Noc/Correctness`, `InductivePhi/` for locked queues, and a delaborator
for `ExprHigh`. The directory `README.md` says the files are not guaranteed to build.

## scripts

| File | Contents |
| --- | --- |
| `dynamatic-to-graphiti.py` | Prepares a Dynamatic graph for Graphiti. Options `--output` and `--mux-ids`. |
| `graphiti-to-dynamatic.py` | Converts a Graphiti graph back for Dynamatic. Options `--output` and `--tags`. |
| `graphiti_conv.py` | Shared helpers for reading and writing DOT with `pydot` and `networkx`. |
| `dynamatic-to-graphiti.md` | Manual checklist of the changes the first script makes. |
| `notes.org` | Notes on benchmarks that did not convert. |
