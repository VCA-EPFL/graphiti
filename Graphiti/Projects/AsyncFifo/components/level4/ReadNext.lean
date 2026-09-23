/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.components.level1.Gates
import Graphiti.Projects.AsyncFifo.components.level3.Contracts

/-!
# The next-state logic of the read domain as gates

A netlist of 16 gates, 11 forks and two bus adapters, for a FIFO of depth `2^2`.  The netlist computes `rNext`: the incremented
pointer (half-adder chain gated by the read enable), its Gray encoding (two XORs), the `empty`
flag (Gray decoding of the synchronised write pointer, equality by XNORs and ANDs) and the
pass-through of the first synchroniser stage.  `unpackR` splits the record bus of the state
register into bits and `packR` assembles the record bus loaded by the register bank; both are
wiring, without logic.

It is the write domain's netlist (`WriteNext.lean`) minus the memory command --- no data, no
write enable, no address --- and with one gate changed: the write side compares its pointer
with `ungray q2 + 2^n`, whose top bit is the complement of `q2`'s, so its top comparison is an
XOR; the read side compares with `ungray q2` itself, so all three are XNORs.

Dropping the memory command costs one thing.  The write domain's `we` output is one gate from
`inc`, so its packer never runs more than one instant ahead of `inc`; here `inc` reaches the
record only through the enable and then a half-adder, and the packer would report past its own
inputs.  So the packer takes three reference streams --- the block's `st`, `inc` and `q1`,
forked off before the logic --- and truncates to them: the boundary cut of `Gates.cut3`, folded
into the packer because the bus is a record rather than a bit.

It is proved to be a next-state block with delay window `[0, 8]`
(`ReadNext.impl_refines : nextImpl ⊑ nextSpec 0 8`, `TopRefinement.lean`).  The longest path (read enable → carries → equality → `empty`) has
eight gates, and some bits pass straight through.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Graphiti.AsyncFifo.ReadNext

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Gates Gray
open Batteries (AssocList)

/-! ### Bus adapters -/

/-- The state register's record bus and the synchroniser's bus, split into bits. -/
@[drcomponents]
def unpackR : StringModule (List (RSt 2) × List (BitVec 3)) :=
  { inputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"q1", ⟨List (BitVec 3), fun s v s' => s.2 ⊏ v ∧ s' = (s.1, v)⟩) ].toAssocList
    outputs := [
                (↑"p0", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.ptr.getLsbD 0) s.1⟩)
               , (↑"p1", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.ptr.getLsbD 1) s.1⟩)
               , (↑"p2", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.ptr.getLsbD 2) s.1⟩)
               , (↑"em", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.empty) s.1⟩)
               , (↑"q20", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.q2.getLsbD 0) s.1⟩)
               , (↑"q21", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.q2.getLsbD 1) s.1⟩)
               , (↑"q22", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.q2.getLsbD 2) s.1⟩)
               , (↑"q10", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.getLsbD 0) s.2⟩)
               , (↑"q11", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.getLsbD 1) s.2⟩)
               , (↑"q12", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.getLsbD 2) s.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], []) }

/-- Stored inputs of the packer: the ten bit streams of the next-state bus. -/
structure PackSt where
  p0 : List Bool
  p1 : List Bool
  p2 : List Bool
  em : List Bool
  q0 : List Bool
  q1 : List Bool
  q2 : List Bool
  g0 : List Bool
  g1 : List Bool
  g2 : List Bool
  r1 : List Bool
  r2 : List Bool
  r3 : List Bool

/-- How far the gates of the record's bits have computed. -/
def packLen (s : PackSt) : Nat :=
  min s.p0.length (min s.p1.length (min s.p2.length (min s.em.length (min s.q0.length (min s.q1.length (min s.q2.length (min s.g0.length (min s.g1.length (s.g2.length)))))))))

/-- How far the block's own inputs are known: the three reference streams of the cut.
Associated exactly like `rnextLen`, which it is.  -/
def refLen (s : PackSt) : Nat :=
  min (min s.r1.length s.r2.length) s.r3.length

/-- The record bus assembled from its bits, reported no further than the block's own inputs.

That bound is the block's reporting policy: it keeps the block inside the horizon its *inputs*
justify, which is what `CombOut`'s length clause asks for and what makes that contract monotone.
Each bit of the bus is at least one gate deep from at least one input, so the gates run at least
one instant ahead of the bits they read; but `inc` reaches the record only through the enable
`ok` and then a half-adder, two gates deep, so dropping one instant is *not* enough here --- the
write domain's netlist gets away with it because its `we` output is one gate from `inc`.  So the
packer takes three reference streams (`r1 r2 r3`, the block's own `st`, `inc` and `q1`, forked
off before the logic) and truncates to them.  This is the boundary cut of `Gates.cut3`, folded
into the packer because the bus is a record rather than a bit.  It computes nothing, and
reporting less than one computes is always sound. -/
def packROut (s : PackSt) : List (RNext 2) :=
  timeline (fun t => ⟨⟨bv3 (s.p0.getD t false) (s.p1.getD t false) (s.p2.getD t false), s.em.getD t false,
      bv3 (s.q0.getD t false) (s.q1.getD t false) (s.q2.getD t false)⟩,
    bv3 (s.g0.getD t false) (s.g1.getD t false) (s.g2.getD t false)⟩) (min (packLen s - 1) (refLen s))

@[drcomponents]
def packR : StringModule PackSt :=
  { inputs := [
               (↑"p0", ⟨List Bool, fun s v s' => s.p0 ⊏ v ∧ s' = { s with p0 := v }⟩)
              , (↑"p1", ⟨List Bool, fun s v s' => s.p1 ⊏ v ∧ s' = { s with p1 := v }⟩)
              , (↑"p2", ⟨List Bool, fun s v s' => s.p2 ⊏ v ∧ s' = { s with p2 := v }⟩)
              , (↑"em", ⟨List Bool, fun s v s' => s.em ⊏ v ∧ s' = { s with em := v }⟩)
              , (↑"q0", ⟨List Bool, fun s v s' => s.q0 ⊏ v ∧ s' = { s with q0 := v }⟩)
              , (↑"q1", ⟨List Bool, fun s v s' => s.q1 ⊏ v ∧ s' = { s with q1 := v }⟩)
              , (↑"q2", ⟨List Bool, fun s v s' => s.q2 ⊏ v ∧ s' = { s with q2 := v }⟩)
              , (↑"g0", ⟨List Bool, fun s v s' => s.g0 ⊏ v ∧ s' = { s with g0 := v }⟩)
              , (↑"g1", ⟨List Bool, fun s v s' => s.g1 ⊏ v ∧ s' = { s with g1 := v }⟩)
              , (↑"g2", ⟨List Bool, fun s v s' => s.g2 ⊏ v ∧ s' = { s with g2 := v }⟩)
              , (↑"r1", ⟨List Bool, fun s v s' => s.r1 ⊏ v ∧ s' = { s with r1 := v }⟩)
              , (↑"r2", ⟨List Bool, fun s v s' => s.r2 ⊏ v ∧ s' = { s with r2 := v }⟩)
              , (↑"r3", ⟨List Bool, fun s v s' => s.r3 ⊏ v ∧ s' = { s with r3 := v }⟩)
              ].toAssocList
    outputs := [ (↑"d", ⟨List (RNext 2), fun s v s' => s' = s ∧ v = packROut s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], [], [], [], [], [], [], [], [], []⟩ }

/-! ### The netlist -/

@[drunfold_defs]
def gateNextRExpr : ExprLow String String :=
  -- The netlist: 54 connections, then the 29 nodes they join.
  -- One `.connect` per wire; `<|` is ordinary application, so this is the term the
  -- graph lowers to and nothing more.
  .connect { output := ⟨.internal "unp", "em"⟩, input := ⟨.internal "nem", "a"⟩ } <|
  .connect { output := ⟨.internal "finc", "out1"⟩, input := ⟨.internal "ok", "a"⟩ } <|
  .connect { output := ⟨.internal "nem", "out"⟩, input := ⟨.internal "ok", "b"⟩ } <|
  .connect { output := ⟨.internal "ok", "out"⟩, input := ⟨.internal "fok", "in"⟩ } <|
  .connect { output := ⟨.internal "unp", "p0"⟩, input := ⟨.internal "fp0", "in"⟩ } <|
  .connect { output := ⟨.internal "unp", "p1"⟩, input := ⟨.internal "fp1", "in"⟩ } <|
  .connect { output := ⟨.internal "fp0", "out1"⟩, input := ⟨.internal "xp0", "a"⟩ } <|
  .connect { output := ⟨.internal "fok", "out1"⟩, input := ⟨.internal "xp0", "b"⟩ } <|
  .connect { output := ⟨.internal "fp0", "out2"⟩, input := ⟨.internal "cp0", "a"⟩ } <|
  .connect { output := ⟨.internal "fok", "out2"⟩, input := ⟨.internal "cp0", "b"⟩ } <|
  .connect { output := ⟨.internal "cp0", "out"⟩, input := ⟨.internal "fc0", "in"⟩ } <|
  .connect { output := ⟨.internal "fp1", "out1"⟩, input := ⟨.internal "xp1", "a"⟩ } <|
  .connect { output := ⟨.internal "fc0", "out1"⟩, input := ⟨.internal "xp1", "b"⟩ } <|
  .connect { output := ⟨.internal "fp1", "out2"⟩, input := ⟨.internal "cp1", "a"⟩ } <|
  .connect { output := ⟨.internal "fc0", "out2"⟩, input := ⟨.internal "cp1", "b"⟩ } <|
  .connect { output := ⟨.internal "unp", "p2"⟩, input := ⟨.internal "xp2", "a"⟩ } <|
  .connect { output := ⟨.internal "cp1", "out"⟩, input := ⟨.internal "xp2", "b"⟩ } <|
  .connect { output := ⟨.internal "xp0", "out"⟩, input := ⟨.internal "fpa", "in"⟩ } <|
  .connect { output := ⟨.internal "xp1", "out"⟩, input := ⟨.internal "fpb", "in"⟩ } <|
  .connect { output := ⟨.internal "xp2", "out"⟩, input := ⟨.internal "fpc", "in"⟩ } <|
  .connect { output := ⟨.internal "fpb", "out2"⟩, input := ⟨.internal "xg0", "a"⟩ } <|
  .connect { output := ⟨.internal "fpa", "out2"⟩, input := ⟨.internal "xg0", "b"⟩ } <|
  .connect { output := ⟨.internal "fpc", "out2"⟩, input := ⟨.internal "xg1", "a"⟩ } <|
  .connect { output := ⟨.internal "fpb", "out3"⟩, input := ⟨.internal "xg1", "b"⟩ } <|
  .connect { output := ⟨.internal "unp", "q22"⟩, input := ⟨.internal "fq2", "in"⟩ } <|
  .connect { output := ⟨.internal "fq2", "out1"⟩, input := ⟨.internal "xu1", "a"⟩ } <|
  .connect { output := ⟨.internal "unp", "q21"⟩, input := ⟨.internal "xu1", "b"⟩ } <|
  .connect { output := ⟨.internal "xu1", "out"⟩, input := ⟨.internal "fu1", "in"⟩ } <|
  .connect { output := ⟨.internal "fu1", "out1"⟩, input := ⟨.internal "xu0", "a"⟩ } <|
  .connect { output := ⟨.internal "unp", "q20"⟩, input := ⟨.internal "xu0", "b"⟩ } <|
  .connect { output := ⟨.internal "fpc", "out4"⟩, input := ⟨.internal "xe2", "a"⟩ } <|
  .connect { output := ⟨.internal "fq2", "out2"⟩, input := ⟨.internal "xe2", "b"⟩ } <|
  .connect { output := ⟨.internal "fpb", "out4"⟩, input := ⟨.internal "xe1", "a"⟩ } <|
  .connect { output := ⟨.internal "fu1", "out2"⟩, input := ⟨.internal "xe1", "b"⟩ } <|
  .connect { output := ⟨.internal "fpa", "out3"⟩, input := ⟨.internal "xe0", "a"⟩ } <|
  .connect { output := ⟨.internal "xu0", "out"⟩, input := ⟨.internal "xe0", "b"⟩ } <|
  .connect { output := ⟨.internal "xe2", "out"⟩, input := ⟨.internal "ae", "a"⟩ } <|
  .connect { output := ⟨.internal "xe1", "out"⟩, input := ⟨.internal "ae", "b"⟩ } <|
  .connect { output := ⟨.internal "ae", "out"⟩, input := ⟨.internal "am", "a"⟩ } <|
  .connect { output := ⟨.internal "xe0", "out"⟩, input := ⟨.internal "am", "b"⟩ } <|
  .connect { output := ⟨.internal "fpa", "out1"⟩, input := ⟨.internal "pk", "p0"⟩ } <|
  .connect { output := ⟨.internal "fpb", "out1"⟩, input := ⟨.internal "pk", "p1"⟩ } <|
  .connect { output := ⟨.internal "fpc", "out1"⟩, input := ⟨.internal "pk", "p2"⟩ } <|
  .connect { output := ⟨.internal "am", "out"⟩, input := ⟨.internal "pk", "em"⟩ } <|
  .connect { output := ⟨.internal "unp", "q10"⟩, input := ⟨.internal "fq1", "in"⟩ } <|
  .connect { output := ⟨.internal "fq1", "out1"⟩, input := ⟨.internal "pk", "q0"⟩ } <|
  .connect { output := ⟨.internal "unp", "q11"⟩, input := ⟨.internal "pk", "q1"⟩ } <|
  .connect { output := ⟨.internal "unp", "q12"⟩, input := ⟨.internal "pk", "q2"⟩ } <|
  .connect { output := ⟨.internal "xg0", "out"⟩, input := ⟨.internal "pk", "g0"⟩ } <|
  .connect { output := ⟨.internal "xg1", "out"⟩, input := ⟨.internal "pk", "g1"⟩ } <|
  .connect { output := ⟨.internal "fpc", "out3"⟩, input := ⟨.internal "pk", "g2"⟩ } <|
  .connect { output := ⟨.internal "fp0", "out3"⟩, input := ⟨.internal "pk", "r1"⟩ } <|
  .connect { output := ⟨.internal "finc", "out2"⟩, input := ⟨.internal "pk", "r2"⟩ } <|
  .connect { output := ⟨.internal "fq1", "out2"⟩, input := ⟨.internal "pk", "r3"⟩ } <|
  .product (.base { input := (.cons ⟨.top, "st"⟩ ⟨.top, "st"⟩ (.cons ⟨.top, "q1"⟩ ⟨.top, "q1"⟩ .nil)), output := (.cons ⟨.top, "p0"⟩ ⟨.internal "unp", "p0"⟩ (.cons ⟨.top, "p1"⟩ ⟨.internal "unp", "p1"⟩ (.cons ⟨.top, "p2"⟩ ⟨.internal "unp", "p2"⟩ (.cons ⟨.top, "em"⟩ ⟨.internal "unp", "em"⟩ (.cons ⟨.top, "q20"⟩ ⟨.internal "unp", "q20"⟩ (.cons ⟨.top, "q21"⟩ ⟨.internal "unp", "q21"⟩ (.cons ⟨.top, "q22"⟩ ⟨.internal "unp", "q22"⟩ (.cons ⟨.top, "q10"⟩ ⟨.internal "unp", "q10"⟩ (.cons ⟨.top, "q11"⟩ ⟨.internal "unp", "q11"⟩ (.cons ⟨.top, "q12"⟩ ⟨.internal "unp", "q12"⟩ .nil)))))))))) } "unpackR") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "nem", "a"⟩ .nil), output := (.cons ⟨.top, "out"⟩ ⟨.internal "nem", "out"⟩ .nil) } "g1_not") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.top, "inc"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "finc", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "finc", "out2"⟩ .nil)) } "fork2") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "ok", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "ok", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "ok", "out"⟩ .nil) } "g2_Bool_and") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fok", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fok", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fok", "out2"⟩ .nil)) } "fork2") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fp0", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fp0", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fp0", "out2"⟩ (.cons ⟨.top, "out3"⟩ ⟨.internal "fp0", "out3"⟩ .nil))) } "fork3") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fp1", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fp1", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fp1", "out2"⟩ .nil)) } "fork2") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fq1", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fq1", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fq1", "out2"⟩ .nil)) } "fork2") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xp0", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xp0", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xp0", "out"⟩ .nil) } "g2_Bool_xor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "cp0", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "cp0", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "cp0", "out"⟩ .nil) } "g2_Bool_and") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fc0", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fc0", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fc0", "out2"⟩ .nil)) } "fork2") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xp1", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xp1", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xp1", "out"⟩ .nil) } "g2_Bool_xor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "cp1", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "cp1", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "cp1", "out"⟩ .nil) } "g2_Bool_and") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xp2", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xp2", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xp2", "out"⟩ .nil) } "g2_Bool_xor") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fpa", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fpa", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fpa", "out2"⟩ (.cons ⟨.top, "out3"⟩ ⟨.internal "fpa", "out3"⟩ .nil))) } "fork3") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fpb", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fpb", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fpb", "out2"⟩ (.cons ⟨.top, "out3"⟩ ⟨.internal "fpb", "out3"⟩ (.cons ⟨.top, "out4"⟩ ⟨.internal "fpb", "out4"⟩ .nil)))) } "fork4") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fpc", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fpc", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fpc", "out2"⟩ (.cons ⟨.top, "out3"⟩ ⟨.internal "fpc", "out3"⟩ (.cons ⟨.top, "out4"⟩ ⟨.internal "fpc", "out4"⟩ .nil)))) } "fork4") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xg0", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xg0", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xg0", "out"⟩ .nil) } "g2_Bool_xor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xg1", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xg1", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xg1", "out"⟩ .nil) } "g2_Bool_xor") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fq2", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fq2", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fq2", "out2"⟩ .nil)) } "fork2") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xu1", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xu1", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xu1", "out"⟩ .nil) } "g2_Bool_xor") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fu1", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fu1", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fu1", "out2"⟩ .nil)) } "fork2") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xu0", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xu0", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xu0", "out"⟩ .nil) } "g2_Bool_xor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xe2", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xe2", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xe2", "out"⟩ .nil) } "g2_xnor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xe1", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xe1", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xe1", "out"⟩ .nil) } "g2_xnor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xe0", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xe0", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xe0", "out"⟩ .nil) } "g2_xnor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "ae", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "ae", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "ae", "out"⟩ .nil) } "g2_Bool_and") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "am", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "am", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "am", "out"⟩ .nil) } "g2_Bool_and") <|
  (.base { input := (.cons ⟨.top, "p0"⟩ ⟨.internal "pk", "p0"⟩ (.cons ⟨.top, "p1"⟩ ⟨.internal "pk", "p1"⟩ (.cons ⟨.top, "p2"⟩ ⟨.internal "pk", "p2"⟩ (.cons ⟨.top, "em"⟩ ⟨.internal "pk", "em"⟩ (.cons ⟨.top, "q0"⟩ ⟨.internal "pk", "q0"⟩ (.cons ⟨.top, "q1"⟩ ⟨.internal "pk", "q1"⟩ (.cons ⟨.top, "q2"⟩ ⟨.internal "pk", "q2"⟩ (.cons ⟨.top, "g0"⟩ ⟨.internal "pk", "g0"⟩ (.cons ⟨.top, "g1"⟩ ⟨.internal "pk", "g1"⟩ (.cons ⟨.top, "g2"⟩ ⟨.internal "pk", "g2"⟩ (.cons ⟨.top, "r1"⟩ ⟨.internal "pk", "r1"⟩ (.cons ⟨.top, "r2"⟩ ⟨.internal "pk", "r2"⟩ (.cons ⟨.top, "r3"⟩ ⟨.internal "pk", "r3"⟩ .nil))))))))))))), output := (.cons ⟨.top, "d"⟩ ⟨.top, "d"⟩ .nil) } "packR")

def genv : AssocList String (TModule1 String) :=
  [ ("unpackR", ⟨_, unpackR⟩)
  , ("g1_not", ⟨_, gate1 not⟩)
  , ("fork2", ⟨_, fork2 Bool⟩)
  , ("g2_Bool_and", ⟨_, gate2 Bool.and⟩)
  , ("fork3", ⟨_, fork3⟩)
  , ("g2_Bool_xor", ⟨_, gate2 Bool.xor⟩)
  , ("fork4", ⟨_, fork4⟩)
  , ("g2_xnor", ⟨_, gate2 (fun a b => a == b)⟩)
  , ("packR", ⟨_, packR⟩)
  ].toAssocList

/-- **The read domain's next-state logic, as gates.** -/
def nextImpl := [e| gateNextRExpr, genv.find? ]

section Spec
variable {n : Nat}

/-- State of the read domain's next-state block: its three input streams and the bus it has
emitted. -/
structure RNextSt (n : Nat) where
  st : List (RSt n)
  inc : List Bool
  q1 : List (BitVec (n+1))
  d : List (RNext n)

def rnextDep (s : RNextSt n) (u : Nat) : RSt n × Bool × BitVec (n+1) :=
  (s.st.getD u default, s.inc.getD u false, s.q1.getD u 0)

def rnextLen (s : RNextSt n) : Nat := min (min s.st.length s.inc.length) s.q1.length

def rnextFun (x : RSt n × Bool × BitVec (n+1)) : RNext n := rNext x.1 x.2.1 x.2.2

@[drcomponents]
def nextSpec (dmin dmax : Nat) : StringModule (RNextSt n) :=
  { inputs := [ (↑"st", ⟨List (RSt n), fun s v s' => s.st ⊏ v ∧ s' = { s with st := v }⟩)
              , (↑"inc", ⟨List Bool, fun s v s' => s.inc ⊏ v ∧ s' = { s with inc := v }⟩)
              , (↑"q1", ⟨List (BitVec (n+1)), fun s v s' => s.q1 ⊏ v ∧ s' = { s with q1 := v }⟩)
              ].toAssocList
    outputs := [ (↑"d", ⟨List (RNext n), fun s v s' => s.d <+: v ∧
                    CombOut (rnextDep s) rnextFun (rnextLen s) dmin dmax v ∧
                    s' = { s with d := v }⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], []⟩ }

end Spec

end Graphiti.AsyncFifo.ReadNext
