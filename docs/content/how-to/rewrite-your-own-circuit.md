+++
title = "Rewrite your own Dynamatic circuit"
description = "Choose the settings for a new Dynamatic circuit, run Graphiti on it, and add it to the benchmarks."
weight = 40
[menus.main]
  parent = "how-to"
  weight = 40
+++

This guide assumes the executable, the oracle and `uv` are installed, as described in
[Build Graphiti]({{< relref "build" >}}).

## Export the circuit from Dynamatic

Graphiti reads the DOT file that Dynamatic writes for a compiled function. Copy it somewhere convenient. The examples
below call it `mycircuit.dot`.

## Find the loop head multiplexers

Graphiti transforms loops that start with a `Mux`. Open the DOT file and find the `Mux` node at the head of each loop you
want transformed. Its first input is the one-bit select signal, so its `in` attribute starts with `in1?:1`:

```text
"phi_1" [type = "Mux", bbID= 2, in = "in1?:1 in2:32 in3:32 ", out = "out1:32", ...];
```

Note the node names. `scripts/dynamatic-to-graphiti.py` uses them to rewire the loop before Graphiti parses it. The
script turns the `Merge` that drives the select signal into an `init Bool false` node and reorders the forks around
the `Branch` and `Mux`. `scripts/dynamatic-to-graphiti.md` lists the same changes as a checklist, which is useful when the
script rejects a circuit.

## Choose a tag count

Pick how many tags the inserted tagger may hand out. Each JSON file in `benchmarks/dynamatic` records the count used
for its circuit, and `gsum_single.json` uses 10.

## Run Graphiti

```shell
GRAPHITI_REPO=/path/to/graphiti /path/to/graphiti/.lake/build/bin/graphiti \
  --output mycircuit-ooo.dot --log mycircuit-log.json \
  --mids phi_1 --tag-nums 10 -- mycircuit.dot
```

- `--mids` takes every following argument up to the next one that starts with `-`, so list several loop heads with
  spaces between them.
- `--` ends the options. Everything after it is joined with spaces into the input path.
- `GRAPHITI_REPO` tells the executable where to find `scripts/` and `bin/graphiti_oracle`. It defaults to the current
  directory, so you can leave it out when you run from the repository root.

The output file is a Dynamatic DOT file. If a stage fails, the tool prints the error, writes the log up to that point
and exits with status 1.

## Change how the loop is rewritten

- Add `--no-reverse` to keep the loop body as the single `pure` node that the pipeline builds, instead of expanding it
  back into the original components.
- Add `--fast` to use the abstraction-based pipeline. The help text calls it the fast but unverified approach.
- Add `--no-dynamatic-dot` to get Graphiti's own DOT output. This also skips the conversion back to Dynamatic.

## Add the circuit to the benchmarks

To rebuild the circuit with the others, copy it into `benchmarks/dynamatic/` and write a JSON file with the same base
name:

```json
{
    "mux-ids": ["phi_1"],
    "tags": 10
}
```

Then add `mycircuit-ooo.dot` to the `all` target in `benchmarks/dynamatic/Makefile`:

```make
all: gemm-ooo.dot mvt-ooo.dot matvec-ooo.dot gsum_single-ooo.dot gsum_many-ooo.dot mycircuit-ooo.dot
```

`make -C benchmarks/dynamatic all` now includes it.
