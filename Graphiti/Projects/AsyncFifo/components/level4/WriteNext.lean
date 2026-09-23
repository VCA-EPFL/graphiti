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
# The next-state logic of the write domain as gates

A netlist of 16 gates, 9 forks and two bus adapters, for a FIFO of depth `2^2` with 1-bit
data.  The netlist computes `wNext`: the
incremented pointer (half-adder chain gated by the write enable), its Gray encoding (two
XORs), the `full` flag (Gray decoding of the synchronised read pointer, MSB flip for the
`+ 2^n`, equality by XNORs and ANDs), the write command and the pass-through of the first
synchroniser stage.  `unpack2` splits the record bus of the state register into bits and
`pack2` assembles the record bus loaded by the register bank; both are wiring, without logic.

It is proved to be a next-state block with delay window `[0, 8]`
(`WriteNext.impl_refines : nextImpl ⊑ nextSpec Bool 0 8`, `TopRefinement.lean`).  The longest path (write enable → carries → equality → `full`) has
eight gates, and some bits pass straight through.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Graphiti.AsyncFifo.WriteNext

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Gates Gray
open Batteries (AssocList)

/-! ### Bus adapters -/

/-- The state register's record bus and the synchroniser's bus, split into bits. -/
@[drcomponents]
def unpack2 : StringModule (List (WSt 2) × List (BitVec 3)) :=
  { inputs := [ (↑"st", ⟨List (WSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"q1", ⟨List (BitVec 3), fun s v s' => s.2 ⊏ v ∧ s' = (s.1, v)⟩) ].toAssocList
    outputs := [
                (↑"p0", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.ptr.getLsbD 0) s.1⟩)
               , (↑"p1", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.ptr.getLsbD 1) s.1⟩)
               , (↑"p2", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.ptr.getLsbD 2) s.1⟩)
               , (↑"fl", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.full) s.1⟩)
               , (↑"q20", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.q2.getLsbD 0) s.1⟩)
               , (↑"q21", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.q2.getLsbD 1) s.1⟩)
               , (↑"q22", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.q2.getLsbD 2) s.1⟩)
               , (↑"q10", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.getLsbD 0) s.2⟩)
               , (↑"q11", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.getLsbD 1) s.2⟩)
               , (↑"q12", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map (fun x => x.getLsbD 2) s.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], []) }

/-- Stored inputs of the packer: the fourteen bit streams of the next-state bus. -/
structure PackSt where
  p0 : List Bool
  p1 : List Bool
  p2 : List Bool
  fl : List Bool
  q0 : List Bool
  q1 : List Bool
  q2 : List Bool
  g0 : List Bool
  g1 : List Bool
  g2 : List Bool
  we : List Bool
  a0 : List Bool
  a1 : List Bool
  dt : List Bool

def packLen (s : PackSt) : Nat :=
  min s.p0.length (min s.p1.length (min s.p2.length (min s.fl.length (min s.q0.length (min s.q1.length (min s.q2.length (min s.g0.length (min s.g1.length (min s.g2.length (min s.we.length (min s.a0.length (min s.a1.length (s.dt.length)))))))))))))

/-- The record bus assembled from its bits, reported one instant short of where the bits reach.

That instant is the block's reporting policy: it keeps the block inside the horizon its
*inputs* justify, which is what `CombOut`'s length clause asks for and what makes that contract
monotone.  Each bit of the bus is at least one gate deep from at least one input, so the gates
run one instant ahead; `W_pack_length` checks that dropping one is enough.  Reporting less than
one computes is always sound. -/
def pack2Out (s : PackSt) : List (WNext Bool 2) :=
  timeline (fun t => ⟨⟨bv3 (s.p0.getD t false) (s.p1.getD t false) (s.p2.getD t false), s.fl.getD t false,
      bv3 (s.q0.getD t false) (s.q1.getD t false) (s.q2.getD t false)⟩,
    bv3 (s.g0.getD t false) (s.g1.getD t false) (s.g2.getD t false), s.we.getD t false,
    bv2 (s.a0.getD t false) (s.a1.getD t false), s.dt.getD t false⟩) (packLen s - 1)

@[drcomponents]
def pack2 : StringModule PackSt :=
  { inputs := [
               (↑"p0", ⟨List Bool, fun s v s' => s.p0 ⊏ v ∧ s' = { s with p0 := v }⟩)
              , (↑"p1", ⟨List Bool, fun s v s' => s.p1 ⊏ v ∧ s' = { s with p1 := v }⟩)
              , (↑"p2", ⟨List Bool, fun s v s' => s.p2 ⊏ v ∧ s' = { s with p2 := v }⟩)
              , (↑"fl", ⟨List Bool, fun s v s' => s.fl ⊏ v ∧ s' = { s with fl := v }⟩)
              , (↑"q0", ⟨List Bool, fun s v s' => s.q0 ⊏ v ∧ s' = { s with q0 := v }⟩)
              , (↑"q1", ⟨List Bool, fun s v s' => s.q1 ⊏ v ∧ s' = { s with q1 := v }⟩)
              , (↑"q2", ⟨List Bool, fun s v s' => s.q2 ⊏ v ∧ s' = { s with q2 := v }⟩)
              , (↑"g0", ⟨List Bool, fun s v s' => s.g0 ⊏ v ∧ s' = { s with g0 := v }⟩)
              , (↑"g1", ⟨List Bool, fun s v s' => s.g1 ⊏ v ∧ s' = { s with g1 := v }⟩)
              , (↑"g2", ⟨List Bool, fun s v s' => s.g2 ⊏ v ∧ s' = { s with g2 := v }⟩)
              , (↑"we", ⟨List Bool, fun s v s' => s.we ⊏ v ∧ s' = { s with we := v }⟩)
              , (↑"a0", ⟨List Bool, fun s v s' => s.a0 ⊏ v ∧ s' = { s with a0 := v }⟩)
              , (↑"a1", ⟨List Bool, fun s v s' => s.a1 ⊏ v ∧ s' = { s with a1 := v }⟩)
              , (↑"dt", ⟨List Bool, fun s v s' => s.dt ⊏ v ∧ s' = { s with dt := v }⟩)
              ].toAssocList
    outputs := [ (↑"d", ⟨List (WNext Bool 2), fun s v s' => s' = s ∧ v = pack2Out s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], []⟩ }

/-! ### The netlist -/

@[drunfold_defs]
def gateNextExpr : ExprLow String String :=
  -- The netlist: 52 connections, then the 27 nodes they join.
  -- One `.connect` per wire; `<|` is ordinary application, so this is the term the
  -- graph lowers to and nothing more.
  .connect { output := ⟨.internal "unp", "fl"⟩, input := ⟨.internal "nfl", "a"⟩ } <|
  .connect { output := ⟨.internal "nfl", "out"⟩, input := ⟨.internal "ok", "b"⟩ } <|
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
  .connect { output := ⟨.internal "ae", "out"⟩, input := ⟨.internal "af", "a"⟩ } <|
  .connect { output := ⟨.internal "xe0", "out"⟩, input := ⟨.internal "af", "b"⟩ } <|
  .connect { output := ⟨.internal "fpa", "out1"⟩, input := ⟨.internal "pk", "p0"⟩ } <|
  .connect { output := ⟨.internal "fpb", "out1"⟩, input := ⟨.internal "pk", "p1"⟩ } <|
  .connect { output := ⟨.internal "fpc", "out1"⟩, input := ⟨.internal "pk", "p2"⟩ } <|
  .connect { output := ⟨.internal "af", "out"⟩, input := ⟨.internal "pk", "fl"⟩ } <|
  .connect { output := ⟨.internal "unp", "q10"⟩, input := ⟨.internal "pk", "q0"⟩ } <|
  .connect { output := ⟨.internal "unp", "q11"⟩, input := ⟨.internal "pk", "q1"⟩ } <|
  .connect { output := ⟨.internal "unp", "q12"⟩, input := ⟨.internal "pk", "q2"⟩ } <|
  .connect { output := ⟨.internal "xg0", "out"⟩, input := ⟨.internal "pk", "g0"⟩ } <|
  .connect { output := ⟨.internal "xg1", "out"⟩, input := ⟨.internal "pk", "g1"⟩ } <|
  .connect { output := ⟨.internal "fpc", "out3"⟩, input := ⟨.internal "pk", "g2"⟩ } <|
  .connect { output := ⟨.internal "fok", "out3"⟩, input := ⟨.internal "pk", "we"⟩ } <|
  .connect { output := ⟨.internal "fp0", "out3"⟩, input := ⟨.internal "pk", "a0"⟩ } <|
  .connect { output := ⟨.internal "fp1", "out3"⟩, input := ⟨.internal "pk", "a1"⟩ } <|
  .product (.base { input := (.cons ⟨.top, "st"⟩ ⟨.top, "st"⟩ (.cons ⟨.top, "q1"⟩ ⟨.top, "q1"⟩ .nil)), output := (.cons ⟨.top, "p0"⟩ ⟨.internal "unp", "p0"⟩ (.cons ⟨.top, "p1"⟩ ⟨.internal "unp", "p1"⟩ (.cons ⟨.top, "p2"⟩ ⟨.internal "unp", "p2"⟩ (.cons ⟨.top, "fl"⟩ ⟨.internal "unp", "fl"⟩ (.cons ⟨.top, "q20"⟩ ⟨.internal "unp", "q20"⟩ (.cons ⟨.top, "q21"⟩ ⟨.internal "unp", "q21"⟩ (.cons ⟨.top, "q22"⟩ ⟨.internal "unp", "q22"⟩ (.cons ⟨.top, "q10"⟩ ⟨.internal "unp", "q10"⟩ (.cons ⟨.top, "q11"⟩ ⟨.internal "unp", "q11"⟩ (.cons ⟨.top, "q12"⟩ ⟨.internal "unp", "q12"⟩ .nil)))))))))) } "unpack2") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "nfl", "a"⟩ .nil), output := (.cons ⟨.top, "out"⟩ ⟨.internal "nfl", "out"⟩ .nil) } "g1_not") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.top, "inc"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "ok", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "ok", "out"⟩ .nil) } "g2_Bool_and") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fok", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fok", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fok", "out2"⟩ (.cons ⟨.top, "out3"⟩ ⟨.internal "fok", "out3"⟩ .nil))) } "fork3") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fp0", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fp0", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fp0", "out2"⟩ (.cons ⟨.top, "out3"⟩ ⟨.internal "fp0", "out3"⟩ .nil))) } "fork3") <|
  .product (.base { input := (.cons ⟨.top, "in"⟩ ⟨.internal "fp1", "in"⟩ .nil), output := (.cons ⟨.top, "out1"⟩ ⟨.internal "fp1", "out1"⟩ (.cons ⟨.top, "out2"⟩ ⟨.internal "fp1", "out2"⟩ (.cons ⟨.top, "out3"⟩ ⟨.internal "fp1", "out3"⟩ .nil))) } "fork3") <|
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
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xe2", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xe2", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xe2", "out"⟩ .nil) } "g2_Bool_xor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xe1", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xe1", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xe1", "out"⟩ .nil) } "g2_xnor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "xe0", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "xe0", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "xe0", "out"⟩ .nil) } "g2_xnor") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "ae", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "ae", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "ae", "out"⟩ .nil) } "g2_Bool_and") <|
  .product (.base { input := (.cons ⟨.top, "a"⟩ ⟨.internal "af", "a"⟩ (.cons ⟨.top, "b"⟩ ⟨.internal "af", "b"⟩ .nil)), output := (.cons ⟨.top, "out"⟩ ⟨.internal "af", "out"⟩ .nil) } "g2_Bool_and") <|
  (.base { input := (.cons ⟨.top, "p0"⟩ ⟨.internal "pk", "p0"⟩ (.cons ⟨.top, "p1"⟩ ⟨.internal "pk", "p1"⟩ (.cons ⟨.top, "p2"⟩ ⟨.internal "pk", "p2"⟩ (.cons ⟨.top, "fl"⟩ ⟨.internal "pk", "fl"⟩ (.cons ⟨.top, "q0"⟩ ⟨.internal "pk", "q0"⟩ (.cons ⟨.top, "q1"⟩ ⟨.internal "pk", "q1"⟩ (.cons ⟨.top, "q2"⟩ ⟨.internal "pk", "q2"⟩ (.cons ⟨.top, "g0"⟩ ⟨.internal "pk", "g0"⟩ (.cons ⟨.top, "g1"⟩ ⟨.internal "pk", "g1"⟩ (.cons ⟨.top, "g2"⟩ ⟨.internal "pk", "g2"⟩ (.cons ⟨.top, "we"⟩ ⟨.internal "pk", "we"⟩ (.cons ⟨.top, "a0"⟩ ⟨.internal "pk", "a0"⟩ (.cons ⟨.top, "a1"⟩ ⟨.internal "pk", "a1"⟩ (.cons ⟨.top, "dt"⟩ ⟨.top, "data"⟩ .nil)))))))))))))), output := (.cons ⟨.top, "d"⟩ ⟨.top, "d"⟩ .nil) } "pack2")

def genv : AssocList String (TModule1 String) :=
  [ ("unpack2", ⟨_, unpack2⟩)
  , ("g1_not", ⟨_, gate1 not⟩)
  , ("g2_Bool_and", ⟨_, gate2 Bool.and⟩)
  , ("fork3", ⟨_, fork3⟩)
  , ("g2_Bool_xor", ⟨_, gate2 Bool.xor⟩)
  , ("fork2", ⟨_, fork2 Bool⟩)
  , ("fork4", ⟨_, fork4⟩)
  , ("g2_xnor", ⟨_, gate2 (fun a b => a == b)⟩)
  , ("pack2", ⟨_, pack2⟩)
  ].toAssocList

/-- **The write domain's next-state logic, as gates.** -/
def nextImpl := [e| gateNextExpr, genv.find? ]

section Spec
variable {n : Nat}
variable (α : Type) [Inhabited α]

/-- State of the next-state block: its four input streams and the bus it has emitted. -/
structure NextSt (α : Type) (n : Nat) where
  st : List (WSt n)
  inc : List Bool
  data : List α
  q1 : List (BitVec (n+1))
  d : List (WNext α n)

/-- The dependency cone of the next-state block at instant `u`: all four inputs. -/
def nextDep (s : NextSt α n) (u : Nat) : WSt n × Bool × α × BitVec (n+1) :=
  (s.st.getD u default, s.inc.getD u false, s.data.getD u default, s.q1.getD u 0)

def nextLen (s : NextSt α n) : Nat :=
  min (min s.st.length s.inc.length) (min s.data.length s.q1.length)

def nextFun (x : WSt n × Bool × α × BitVec (n+1)) : WNext α n := wNext α x.1 x.2.1 x.2.2.1 x.2.2.2

/-- Combinational next-state block with delay window `[dmin, dmax]`.  Its single output is the
bus carrying the whole `WNext` record (next state, next Gray pointer, memory write command);
its implementation `nextImpl` is a netlist, and the bus its individual wires. -/
@[drcomponents]
def nextSpec (dmin dmax : Nat) : StringModule (NextSt α n) :=
  { inputs := [ (↑"st", ⟨List (WSt n), fun s v s' => s.st ⊏ v ∧ s' = { s with st := v }⟩)
              , (↑"inc", ⟨List Bool, fun s v s' => s.inc ⊏ v ∧ s' = { s with inc := v }⟩)
              , (↑"data", ⟨List α, fun s v s' => s.data ⊏ v ∧ s' = { s with data := v }⟩)
              , (↑"q1", ⟨List (BitVec (n+1)), fun s v s' => s.q1 ⊏ v ∧ s' = { s with q1 := v }⟩)
              ].toAssocList
    outputs := [ (↑"d", ⟨List (WNext α n), fun s v s' => s.d <+: v ∧
                    CombOut (nextDep α s) (nextFun α) (nextLen α s) dmin dmax v ∧ s' = { s with d := v }⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], []⟩ }

end Spec

end Graphiti.AsyncFifo.WriteNext
