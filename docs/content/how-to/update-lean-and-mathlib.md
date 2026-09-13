+++
title = "Update Lean and mathlib"
description = "Move the repository to a new Lean release and the matching mathlib tag."
weight = 70
[menus.main]
  parent = "how-to"
  weight = 70
+++

The repository pins a Lean release candidate and the mathlib tag with the same name. Update both together.

## Change the pins

Set the new version in `lean-toolchain`:

```text
leanprover/lean4:v4.34.0
```

Set the same tag as the mathlib revision in `lakefile.toml`:

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.34.0"
```

The version numbers are examples. Use a tag that exists in both repositories.

## Update the dependencies

```shell
lake update mathlib
make setup
```

`lake update` rewrites `lake-manifest.json`. `make setup` downloads the compiled mathlib for the new tag.

## Rebuild and fix

```shell
lake build GraphitiCore
lake build GraphitiProjects
lake test
```

Fix errors in `Graphiti/Core` first, because the projects depend on it. Leave `Graphiti/Experimental` alone unless you
need a file there.

Check the `#print axioms` tests while fixing proofs. A proof that you patch with `sorry` changes their output and fails
`lake test`, which is the intended signal.

## About the update workflow

`.github/workflows/update-mathlib-version.yml` automates this for nightly toolchains. It rewrites `nightly-` strings
in `lean-toolchain` and `nightly-testing-` strings in `lakefile.toml`. The current pins are release tags without those
strings, so the workflow has nothing to rewrite, and a manual update as above is the way to go.
