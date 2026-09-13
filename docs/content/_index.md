+++
title = "Graphiti manual"
description = "Documentation for Graphiti, a Lean 4 framework for verified rewriting of dataflow circuits."
+++

Graphiti rewrites dataflow circuits and proves that the rewrites are safe. It reads a circuit produced by the
[Dynamatic](https://github.com/EPFL-LAP/dynamatic) high-level synthesis compiler, transforms its loops so that several iterations
can be in flight at once, and writes a Dynamatic circuit back out. Everything is written in Lean 4.

The rewriting engine carries a proof. If a rewrite comes with a correctness proof, applying it to any circuit gives a
circuit that refines the original. Every sequence of inputs and outputs the new circuit can produce, the old one could
produce too. The [explanation]({{< relref "/explanation" >}}) section says exactly what that covers and what it leaves
out.

## How this manual is organised

The manual follows the [Diátaxis](https://diataxis.fr/) framework, which splits documentation by what the reader is
trying to do.

- [Tutorials]({{< relref "/tutorials" >}}) are lessons. Start here if you have never used Graphiti.
- [How-to guides]({{< relref "/how-to" >}}) give the steps for one job, such as adding a rewrite or running the
  benchmarks.
- [Reference]({{< relref "/reference" >}}) lists command-line options, file formats, components, rewrites and Lean
  definitions.
- [Explanation]({{< relref "/explanation" >}}) covers the ideas: the circuit semantics, the two graph forms, how a
  rewrite runs and what the proofs guarantee.

## Citing Graphiti

The work is described in the ASPLOS'26 paper *Graphiti: Formally Verified Out-of-Order Execution in Dataflow Circuits*
by Yann Herklotz, Ayatallah Elakhras, Martina Camaioni, Paolo Ienne, Lana Josipović and Thomas Bourgeat. The BibTeX
entry is in the repository `README.md`, and `CITATION.cff` has the same data.
