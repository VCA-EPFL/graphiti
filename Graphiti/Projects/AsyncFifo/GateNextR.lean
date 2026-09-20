/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Gates
import Graphiti.Projects.AsyncFifo.NetlistWf

/-!
# The next-state logic of the read domain as gates

A netlist of 16 gates, 11 forks and two bus adapters, for a FIFO of depth `2^2`.  The netlist computes `rNext`: the incremented
pointer (half-adder chain gated by the read enable), its Gray encoding (two XORs), the `empty`
flag (Gray decoding of the synchronised write pointer, equality by XNORs and ANDs) and the
pass-through of the first synchroniser stage.  `unpackR` splits the record bus of the state
register into bits and `packR` assembles the record bus loaded by the register bank; both are
wiring, without logic.

It is the write domain's netlist (`GateNext.lean`) minus the memory command --- no data, no
write enable, no address --- and with one gate changed: the write side compares its pointer
with `ungray q2 + 2^n`, whose top bit is the complement of `q2`'s, so its top comparison is an
XOR; the read side compares with `ungray q2` itself, so all three are XNORs.

Dropping the memory command costs one thing.  The write domain's `we` output is one gate from
`inc`, so its packer never runs more than one instant ahead of `inc`; here `inc` reaches the
record only through the enable and then a half-adder, and the packer would report past its own
inputs.  So the packer takes three reference streams --- the block's `st`, `inc` and `q1`,
forked off before the logic --- and truncates to them: the boundary cut of `Gates.cut3`, folded
into the packer because the bus is a record rather than a bit.

`gateNextR_refines : gateNextR ⊑ rnextBlock 0 8`: the netlist is a next-state block with
delay window `[0, 8]`.  The longest path (read enable → carries → equality → `empty`) has
eight gates, and some bits pass straight through.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Graphiti.AsyncFifo.GateNextR

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Gates Gray
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

@[simp] theorem packROut_length (s : PackSt) :
    (packROut s).length = min (packLen s - 1) (refLen s) := timeline_length _ _

theorem packROut_getD (s : PackSt) {t : Nat} (ht : t < min (packLen s - 1) (refLen s)) :
    (packROut s).getD t default = ⟨⟨bv3 (s.p0.getD t false) (s.p1.getD t false) (s.p2.getD t false), s.em.getD t false,
      bv3 (s.q0.getD t false) (s.q1.getD t false) (s.q2.getD t false)⟩,
    bv3 (s.g0.getD t false) (s.g1.getD t false) (s.g2.getD t false)⟩ := timeline_getD _ ht _

theorem packROut_mono {s s' : PackSt} (hp0 : s.p0 <+: s'.p0) (hp1 : s.p1 <+: s'.p1) (hp2 : s.p2 <+: s'.p2) (hem : s.em <+: s'.em) (hq0 : s.q0 <+: s'.q0) (hq1 : s.q1 <+: s'.q1) (hq2 : s.q2 <+: s'.q2) (hg0 : s.g0 <+: s'.g0) (hg1 : s.g1 <+: s'.g1) (hg2 : s.g2 <+: s'.g2) (hr1 : s.r1 <+: s'.r1) (hr2 : s.r2 <+: s'.r2) (hr3 : s.r3 <+: s'.r3) :
    packROut s <+: packROut s' := by
  apply timeline_mono (min_mono (Nat.sub_le_sub_right (min_mono hp0.length_le (min_mono hp1.length_le (min_mono hp2.length_le (min_mono hem.length_le (min_mono hq0.length_le (min_mono hq1.length_le (min_mono hq2.length_le (min_mono hg0.length_le (min_mono hg1.length_le (hg2.length_le)))))))))) 1) (min_mono (min_mono hr1.length_le hr2.length_le) hr3.length_le))
  intro t ht
  have ht2 : t < packLen s :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le ht (Nat.min_le_left _ _)) (Nat.sub_le _ _)
  simp only [packLen, Nat.lt_min] at ht2
  obtain ⟨t_p0, t_p1, t_p2, t_em, t_q0, t_q1, t_q2, t_g0, t_g1, t_g2⟩ := ht2
  rw [hp0.getD_eq_left t_p0, hp1.getD_eq_left t_p1, hp2.getD_eq_left t_p2, hem.getD_eq_left t_em, hq0.getD_eq_left t_q0, hq1.getD_eq_left t_q1, hq2.getD_eq_left t_q2, hg0.getD_eq_left t_g0, hg1.getD_eq_left t_g1, hg2.getD_eq_left t_g2]

/-- `packROut_mono` stated field by field: callers then unify their wires with the fields
syntactically, instead of unfolding a wire to compare it with a projection. -/
theorem packROut_mono' {p0 p0' p1 p1' p2 p2' em em' q0 q0' q1 q1' q2 q2' g0 g0' g1 g1' g2 g2' r1 r1' r2 r2' r3 r3' : List Bool}
    (hp0 : p0 <+: p0') (hp1 : p1 <+: p1') (hp2 : p2 <+: p2') (hem : em <+: em') (hq0 : q0 <+: q0') (hq1 : q1 <+: q1') (hq2 : q2 <+: q2') (hg0 : g0 <+: g0') (hg1 : g1 <+: g1') (hg2 : g2 <+: g2') (hr1 : r1 <+: r1') (hr2 : r2 <+: r2') (hr3 : r3 <+: r3') :
    packROut ⟨p0, p1, p2, em, q0, q1, q2, g0, g1, g2, r1, r2, r3⟩ <+: packROut ⟨p0', p1', p2', em', q0', q1', q2', g0', g1', g2', r1', r2', r3'⟩ :=
  packROut_mono hp0 hp1 hp2 hem hq0 hq1 hq2 hg0 hg1 hg2 hr1 hr2 hr3

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

@[drenv] theorem genv_unpackR : genv.find? "unpackR" = .some ⟨_, unpackR⟩ := rfl
@[drenv] theorem genv_g1_not : genv.find? "g1_not" = .some ⟨_, gate1 not⟩ := rfl
@[drenv] theorem genv_fork2 : genv.find? "fork2" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem genv_g2_Bool_and : genv.find? "g2_Bool_and" = .some ⟨_, gate2 Bool.and⟩ := rfl
@[drenv] theorem genv_fork3 : genv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem genv_g2_Bool_xor : genv.find? "g2_Bool_xor" = .some ⟨_, gate2 Bool.xor⟩ := rfl
@[drenv] theorem genv_fork4 : genv.find? "fork4" = .some ⟨_, fork4⟩ := rfl
@[drenv] theorem genv_g2_xnor : genv.find? "g2_xnor" = .some ⟨_, gate2 (fun a b => a == b)⟩ := rfl
@[drenv] theorem genv_packR : genv.find? "packR" = .some ⟨_, packR⟩ := rfl

/-- The state of the netlist: the stored inputs of every node, in netlist order. -/
abbrev gateNextRT : Type :=
  (List (Timed.RSt 2) × List (BitVec 3)) × List Bool × List Bool × (List Bool × List Bool) × List Bool × List Bool × List Bool × List Bool × (List Bool × List Bool) × (List Bool × List Bool) × List Bool × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × List Bool × List Bool × List Bool × (List Bool × List Bool) × (List Bool × List Bool) × List Bool × (List Bool × List Bool) × List Bool × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × PackSt

seal genv in
def_module gateNextRT' : Type :=
  [T| gateNextRExpr, genv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

/-- A compiled check, not a step of any proof: the type `def_module` reduces the graph to
is the one written by hand above, so the hand-written `abbrev` — which every statement below
names — cannot drift from the graph. -/
theorem gateNextRT_eq : gateNextRT' = gateNextRT := rfl

set_option maxHeartbeats 4000000 in
seal genv in
def_module gateNextR : StringModule gateNextRT :=
  [e| gateNextRExpr, genv.find? ]

/-! ### The wires as functions of the block's inputs -/

/-- Primary inputs at one instant, as `nextDep` produces them. -/
abbrev Inp := RSt 2 × Bool × BitVec 3

def F_inc : Inp → Bool := fun i => i.2.1
def F_unp_p0 : Inp → Bool := fun i => i.1.ptr.getLsbD 0
def F_unp_p1 : Inp → Bool := fun i => i.1.ptr.getLsbD 1
def F_unp_p2 : Inp → Bool := fun i => i.1.ptr.getLsbD 2
def F_unp_em : Inp → Bool := fun i => i.1.empty
def F_unp_q20 : Inp → Bool := fun i => i.1.q2.getLsbD 0
def F_unp_q21 : Inp → Bool := fun i => i.1.q2.getLsbD 1
def F_unp_q22 : Inp → Bool := fun i => i.1.q2.getLsbD 2
def F_unp_q10 : Inp → Bool := fun i => i.2.2.getLsbD 0
def F_unp_q11 : Inp → Bool := fun i => i.2.2.getLsbD 1
def F_unp_q12 : Inp → Bool := fun i => i.2.2.getLsbD 2
def F_nem : Inp → Bool := fun i => not (F_unp_em i)
def F_ok : Inp → Bool := fun i => Bool.and (F_inc i) (F_nem i)
def F_xp0 : Inp → Bool := fun i => Bool.xor (F_unp_p0 i) (F_ok i)
def F_cp0 : Inp → Bool := fun i => Bool.and (F_unp_p0 i) (F_ok i)
def F_xp1 : Inp → Bool := fun i => Bool.xor (F_unp_p1 i) (F_cp0 i)
def F_cp1 : Inp → Bool := fun i => Bool.and (F_unp_p1 i) (F_cp0 i)
def F_xp2 : Inp → Bool := fun i => Bool.xor (F_unp_p2 i) (F_cp1 i)
def F_xg0 : Inp → Bool := fun i => Bool.xor (F_xp1 i) (F_xp0 i)
def F_xg1 : Inp → Bool := fun i => Bool.xor (F_xp2 i) (F_xp1 i)
def F_xu1 : Inp → Bool := fun i => Bool.xor (F_unp_q22 i) (F_unp_q21 i)
def F_xu0 : Inp → Bool := fun i => Bool.xor (F_xu1 i) (F_unp_q20 i)
def F_xe2 : Inp → Bool := fun i => (fun a b => a == b) (F_xp2 i) (F_unp_q22 i)
def F_xe1 : Inp → Bool := fun i => (fun a b => a == b) (F_xp1 i) (F_xu1 i)
def F_xe0 : Inp → Bool := fun i => (fun a b => a == b) (F_xp0 i) (F_xu0 i)
def F_ae : Inp → Bool := fun i => Bool.and (F_xe2 i) (F_xe1 i)
def F_am : Inp → Bool := fun i => Bool.and (F_ae i) (F_xe0 i)

def W_unp_p0 (s : RNextSt 2) : List Bool := List.map (fun x => x.ptr.getLsbD 0) s.st
def W_unp_p1 (s : RNextSt 2) : List Bool := List.map (fun x => x.ptr.getLsbD 1) s.st
def W_unp_p2 (s : RNextSt 2) : List Bool := List.map (fun x => x.ptr.getLsbD 2) s.st
def W_unp_em (s : RNextSt 2) : List Bool := List.map (fun x => x.empty) s.st
def W_unp_q20 (s : RNextSt 2) : List Bool := List.map (fun x => x.q2.getLsbD 0) s.st
def W_unp_q21 (s : RNextSt 2) : List Bool := List.map (fun x => x.q2.getLsbD 1) s.st
def W_unp_q22 (s : RNextSt 2) : List Bool := List.map (fun x => x.q2.getLsbD 2) s.st
def W_unp_q10 (s : RNextSt 2) : List Bool := List.map (fun x => x.getLsbD 0) s.q1
def W_unp_q11 (s : RNextSt 2) : List Bool := List.map (fun x => x.getLsbD 1) s.q1
def W_unp_q12 (s : RNextSt 2) : List Bool := List.map (fun x => x.getLsbD 2) s.q1
def W_nem (s : RNextSt 2) : List Bool := gate1Out not (W_unp_em s)
def W_ok (s : RNextSt 2) : List Bool := gateOut Bool.and (s.inc) (W_nem s)
def W_xp0 (s : RNextSt 2) : List Bool := gateOut Bool.xor (W_unp_p0 s) (W_ok s)
def W_cp0 (s : RNextSt 2) : List Bool := gateOut Bool.and (W_unp_p0 s) (W_ok s)
def W_xp1 (s : RNextSt 2) : List Bool := gateOut Bool.xor (W_unp_p1 s) (W_cp0 s)
def W_cp1 (s : RNextSt 2) : List Bool := gateOut Bool.and (W_unp_p1 s) (W_cp0 s)
def W_xp2 (s : RNextSt 2) : List Bool := gateOut Bool.xor (W_unp_p2 s) (W_cp1 s)
def W_xg0 (s : RNextSt 2) : List Bool := gateOut Bool.xor (W_xp1 s) (W_xp0 s)
def W_xg1 (s : RNextSt 2) : List Bool := gateOut Bool.xor (W_xp2 s) (W_xp1 s)
def W_xu1 (s : RNextSt 2) : List Bool := gateOut Bool.xor (W_unp_q22 s) (W_unp_q21 s)
def W_xu0 (s : RNextSt 2) : List Bool := gateOut Bool.xor (W_xu1 s) (W_unp_q20 s)
def W_xe2 (s : RNextSt 2) : List Bool := gateOut (fun a b => a == b) (W_xp2 s) (W_unp_q22 s)
def W_xe1 (s : RNextSt 2) : List Bool := gateOut (fun a b => a == b) (W_xp1 s) (W_xu1 s)
def W_xe0 (s : RNextSt 2) : List Bool := gateOut (fun a b => a == b) (W_xp0 s) (W_xu0 s)
def W_ae (s : RNextSt 2) : List Bool := gateOut Bool.and (W_xe2 s) (W_xe1 s)
def W_am (s : RNextSt 2) : List Bool := gateOut Bool.and (W_ae s) (W_xe0 s)

/-- The packer's stored inputs when every wire carries its full stream. -/
def Wpk (s : RNextSt 2) : PackSt := ⟨W_xp0 s, W_xp1 s, W_xp2 s, W_am s, W_unp_q10 s, W_unp_q11 s, W_unp_q12 s, W_xg0 s, W_xg1 s, W_xp2 s, W_unp_p0 s, s.inc, W_unp_q10 s⟩
def W_pack (s : RNextSt 2) : List (RNext 2) := packROut (Wpk s)

/-! ### Monotonicity of the wires in the inputs -/

variable {s s' : RNextSt 2}

theorem W_unp_p0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_p0 s <+: W_unp_p0 s' := h1.map _
theorem W_unp_p1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_p1 s <+: W_unp_p1 s' := h1.map _
theorem W_unp_p2_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_p2 s <+: W_unp_p2 s' := h1.map _
theorem W_unp_em_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_em s <+: W_unp_em s' := h1.map _
theorem W_unp_q20_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_q20 s <+: W_unp_q20 s' := h1.map _
theorem W_unp_q21_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_q21 s <+: W_unp_q21 s' := h1.map _
theorem W_unp_q22_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_q22 s <+: W_unp_q22 s' := h1.map _
theorem W_unp_q10_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_q10 s <+: W_unp_q10 s' := h3.map _
theorem W_unp_q11_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_q11 s <+: W_unp_q11 s' := h3.map _
theorem W_unp_q12_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_unp_q12 s <+: W_unp_q12 s' := h3.map _
theorem W_nem_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_nem s <+: W_nem s' := gate1Out_mono _ (W_unp_em_mono h1 h2 h3)
theorem W_ok_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_ok s <+: W_ok s' := gateOut_mono _ h2 (W_nem_mono h1 h2 h3)
theorem W_xp0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xp0 s <+: W_xp0 s' := gateOut_mono _ (W_unp_p0_mono h1 h2 h3) (W_ok_mono h1 h2 h3)
theorem W_cp0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_cp0 s <+: W_cp0 s' := gateOut_mono _ (W_unp_p0_mono h1 h2 h3) (W_ok_mono h1 h2 h3)
theorem W_xp1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xp1 s <+: W_xp1 s' := gateOut_mono _ (W_unp_p1_mono h1 h2 h3) (W_cp0_mono h1 h2 h3)
theorem W_cp1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_cp1 s <+: W_cp1 s' := gateOut_mono _ (W_unp_p1_mono h1 h2 h3) (W_cp0_mono h1 h2 h3)
theorem W_xp2_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xp2 s <+: W_xp2 s' := gateOut_mono _ (W_unp_p2_mono h1 h2 h3) (W_cp1_mono h1 h2 h3)
theorem W_xg0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xg0 s <+: W_xg0 s' := gateOut_mono _ (W_xp1_mono h1 h2 h3) (W_xp0_mono h1 h2 h3)
theorem W_xg1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xg1 s <+: W_xg1 s' := gateOut_mono _ (W_xp2_mono h1 h2 h3) (W_xp1_mono h1 h2 h3)
theorem W_xu1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xu1 s <+: W_xu1 s' := gateOut_mono _ (W_unp_q22_mono h1 h2 h3) (W_unp_q21_mono h1 h2 h3)
theorem W_xu0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xu0 s <+: W_xu0 s' := gateOut_mono _ (W_xu1_mono h1 h2 h3) (W_unp_q20_mono h1 h2 h3)
theorem W_xe2_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xe2 s <+: W_xe2 s' := gateOut_mono _ (W_xp2_mono h1 h2 h3) (W_unp_q22_mono h1 h2 h3)
theorem W_xe1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xe1 s <+: W_xe1 s' := gateOut_mono _ (W_xp1_mono h1 h2 h3) (W_xu1_mono h1 h2 h3)
theorem W_xe0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_xe0 s <+: W_xe0 s' := gateOut_mono _ (W_xp0_mono h1 h2 h3) (W_xu0_mono h1 h2 h3)
theorem W_ae_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_ae s <+: W_ae s' := gateOut_mono _ (W_xe2_mono h1 h2 h3) (W_xe1_mono h1 h2 h3)
theorem W_am_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.q1 <+: s'.q1) :
    W_am s <+: W_am s' := gateOut_mono _ (W_ae_mono h1 h2 h3) (W_xe0_mono h1 h2 h3)

/-! ### Combinational contracts of the wires -/

variable (s : RNextSt 2)

theorem C_inc : Comb 0 0 F_inc (rnextDep s) s.inc := Comb.input (fun t _ => rfl)
theorem C_unp_p0 : Comb 0 0 F_unp_p0 (rnextDep s) (W_unp_p0 s) :=
  Comb.input (fun t ht => by unfold W_unp_p0 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_p1 : Comb 0 0 F_unp_p1 (rnextDep s) (W_unp_p1 s) :=
  Comb.input (fun t ht => by unfold W_unp_p1 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_p2 : Comb 0 0 F_unp_p2 (rnextDep s) (W_unp_p2 s) :=
  Comb.input (fun t ht => by unfold W_unp_p2 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_em : Comb 0 0 F_unp_em (rnextDep s) (W_unp_em s) :=
  Comb.input (fun t ht => by unfold W_unp_em at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q20 : Comb 0 0 F_unp_q20 (rnextDep s) (W_unp_q20 s) :=
  Comb.input (fun t ht => by unfold W_unp_q20 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q21 : Comb 0 0 F_unp_q21 (rnextDep s) (W_unp_q21 s) :=
  Comb.input (fun t ht => by unfold W_unp_q21 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q22 : Comb 0 0 F_unp_q22 (rnextDep s) (W_unp_q22 s) :=
  Comb.input (fun t ht => by unfold W_unp_q22 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q10 : Comb 0 0 F_unp_q10 (rnextDep s) (W_unp_q10 s) :=
  Comb.input (fun t ht => by unfold W_unp_q10 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q11 : Comb 0 0 F_unp_q11 (rnextDep s) (W_unp_q11 s) :=
  Comb.input (fun t ht => by unfold W_unp_q11 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q12 : Comb 0 0 F_unp_q12 (rnextDep s) (W_unp_q12 s) :=
  Comb.input (fun t ht => by unfold W_unp_q12 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_nem : Comb 1 1 F_nem (rnextDep s) (W_nem s) :=
  Comb.gate1 not (C_unp_em s)
theorem C_ok : Comb 1 2 F_ok (rnextDep s) (W_ok s) :=
  Comb.gate2 Bool.and (C_inc s) (C_nem s)
theorem C_xp0 : Comb 1 3 F_xp0 (rnextDep s) (W_xp0 s) :=
  Comb.gate2 Bool.xor (C_unp_p0 s) (C_ok s)
theorem C_cp0 : Comb 1 3 F_cp0 (rnextDep s) (W_cp0 s) :=
  Comb.gate2 Bool.and (C_unp_p0 s) (C_ok s)
theorem C_xp1 : Comb 1 4 F_xp1 (rnextDep s) (W_xp1 s) :=
  Comb.gate2 Bool.xor (C_unp_p1 s) (C_cp0 s)
theorem C_cp1 : Comb 1 4 F_cp1 (rnextDep s) (W_cp1 s) :=
  Comb.gate2 Bool.and (C_unp_p1 s) (C_cp0 s)
theorem C_xp2 : Comb 1 5 F_xp2 (rnextDep s) (W_xp2 s) :=
  Comb.gate2 Bool.xor (C_unp_p2 s) (C_cp1 s)
theorem C_xg0 : Comb 2 5 F_xg0 (rnextDep s) (W_xg0 s) :=
  Comb.gate2 Bool.xor (C_xp1 s) (C_xp0 s)
theorem C_xg1 : Comb 2 6 F_xg1 (rnextDep s) (W_xg1 s) :=
  Comb.gate2 Bool.xor (C_xp2 s) (C_xp1 s)
theorem C_xu1 : Comb 1 1 F_xu1 (rnextDep s) (W_xu1 s) :=
  Comb.gate2 Bool.xor (C_unp_q22 s) (C_unp_q21 s)
theorem C_xu0 : Comb 1 2 F_xu0 (rnextDep s) (W_xu0 s) :=
  Comb.gate2 Bool.xor (C_xu1 s) (C_unp_q20 s)
theorem C_xe2 : Comb 1 6 F_xe2 (rnextDep s) (W_xe2 s) :=
  Comb.gate2 (fun a b => a == b) (C_xp2 s) (C_unp_q22 s)
theorem C_xe1 : Comb 2 5 F_xe1 (rnextDep s) (W_xe1 s) :=
  Comb.gate2 (fun a b => a == b) (C_xp1 s) (C_xu1 s)
theorem C_xe0 : Comb 2 4 F_xe0 (rnextDep s) (W_xe0 s) :=
  Comb.gate2 (fun a b => a == b) (C_xp0 s) (C_xu0 s)
theorem C_ae : Comb 2 7 F_ae (rnextDep s) (W_ae s) :=
  Comb.gate2 Bool.and (C_xe2 s) (C_xe1 s)
theorem C_am : Comb 3 8 F_am (rnextDep s) (W_am s) :=
  Comb.gate2 Bool.and (C_ae s) (C_xe0 s)

/-! ### The netlist computes the next-state function

One field of the record at a time, for all 4096 values of the input bits, checked by the kernel. -/

theorem identity_st_ptr : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ empty inc : Bool,
    bv3 (F_xp0 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) (F_xp1 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) (F_xp2 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) = (rnextFun ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)).st.ptr := by decide +kernel

theorem identity_st_empty : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ empty inc : Bool,
    F_am ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c) = (rnextFun ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)).st.empty := by decide +kernel

theorem identity_st_q2 : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ empty inc : Bool,
    bv3 (F_unp_q10 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) (F_unp_q11 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) (F_unp_q12 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) = (rnextFun ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)).st.q2 := by decide +kernel

theorem identity_gnext : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ empty inc : Bool,
    bv3 (F_xg0 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) (F_xg1 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) (F_xp2 ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)) = (rnextFun ((⟨BitVec.ofNat 3 a, empty, BitVec.ofNat 3 b⟩ : RSt 2), inc, BitVec.ofNat 3 c)).gnext := by decide +kernel

theorem pack_identity' (ptr q2 q1 : BitVec 3) (empty inc : Bool) :
    (⟨⟨bv3 (F_xp0 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)) (F_xp1 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)) (F_xp2 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)), F_am ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1), bv3 (F_unp_q10 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)) (F_unp_q11 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)) (F_unp_q12 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1))⟩, bv3 (F_xg0 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)) (F_xg1 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)) (F_xp2 ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1))⟩ : RNext 2) = rnextFun ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1) := by
  have e : ∀ x : BitVec 3, BitVec.ofNat 3 x.toNat = x := fun x => by simp
  have h_st_ptr := identity_st_ptr ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt empty inc
  rw [e ptr, e q2, e q1] at h_st_ptr
  have h_st_empty := identity_st_empty ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt empty inc
  rw [e ptr, e q2, e q1] at h_st_empty
  have h_st_q2 := identity_st_q2 ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt empty inc
  rw [e ptr, e q2, e q1] at h_st_q2
  have h_gnext := identity_gnext ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt empty inc
  rw [e ptr, e q2, e q1] at h_gnext
  rw [show rnextFun ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1) = ⟨⟨(rnextFun ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)).st.ptr, (rnextFun ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)).st.empty, (rnextFun ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)).st.q2⟩, (rnextFun ((⟨ptr, empty, q2⟩ : RSt 2), inc, q1)).gnext⟩ from rfl]
  rw [h_st_ptr, h_st_empty, h_st_q2, h_gnext]

theorem pack_identity (i : Inp) : (⟨⟨bv3 (F_xp0 i) (F_xp1 i) (F_xp2 i), F_am i, bv3 (F_unp_q10 i) (F_unp_q11 i) (F_unp_q12 i)⟩, bv3 (F_xg0 i) (F_xg1 i) (F_xp2 i)⟩ : RNext 2) = rnextFun i := by
  obtain ⟨⟨ptr, empty, q2⟩, inc, q1⟩ := i
  exact pack_identity' ptr q2 q1 empty inc

/-- The packer's output is no longer than the block's inputs: that is what the cut says,
and the three reference streams *are* the block's inputs. -/
theorem W_pack_length : (W_pack s).length ≤ rnextLen s := by
  simp only [W_pack, packROut_length, Wpk, refLen, W_unp_p0, W_unp_q10, List.length_map, rnextLen]
  exact Nat.min_le_right _ _

/-- **The netlist satisfies the contract of the next-state block** with delay window `[0, 8]`. -/
theorem W_pack_comb : CombOut (rnextDep s) (rnextFun) (rnextLen s) 0 8 (W_pack s) := by
  refine ⟨W_pack_length s, fun t hdt ht hs => ?_⟩
  have hst := Comb.stable_of_StableOn hs
  simp only [W_pack, packROut_length] at ht
  have htp : t < min (packLen (Wpk s) - 1) (refLen (Wpk s)) := ht
  have ht : t < packLen (Wpk s) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le htp (Nat.min_le_left _ _)) (Nat.sub_le _ _)
  simp only [packLen, Wpk, Nat.lt_min] at ht
  obtain ⟨t_p0, t_p1, t_p2, t_em, t_q0, t_q1, t_q2, t_g0, t_g1, t_g2⟩ := ht
  rw [W_pack, packROut_getD _ htp]
  simp only [Wpk]
  rw [(C_xp0 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_p0 hst]
  rw [(C_xp1 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_p1 hst]
  rw [(C_xp2 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_p2 hst]
  rw [(C_am s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_em hst]
  rw [(C_unp_q10 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_q0 hst]
  rw [(C_unp_q11 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_q1 hst]
  rw [(C_unp_q12 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_q2 hst]
  rw [(C_xg0 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_g0 hst]
  rw [(C_xg1 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_g1 hst]
  exact pack_identity _

/-! ### Refinement of the next-state block -/

instance : MatchInterface gateNextR (rnextBlock (n := 2) 0 8) := by
  dsimp [gateNextR, rnextBlock]
  solve_match_interface
/-! ### The netlist, as an index type

Each wire holds a prefix of what the specification computes for it.  This block is
combinational, so `drv` does not read the other wires at all -- it is the specification's own
`W_*`, wire by wire -- and a connection is then one monotonicity step, written on its own
line below. -/

open Graphiti.AsyncFifo.Netlist

/-- The 54 driven wires. -/
inductive W
  | nem_a
  | ok_a
  | ok_b
  | fok_in
  | fp0_in
  | fp1_in
  | xp0_a
  | xp0_b
  | cp0_a
  | cp0_b
  | fc0_in
  | xp1_a
  | xp1_b
  | cp1_a
  | cp1_b
  | xp2_a
  | xp2_b
  | fpa_in
  | fpb_in
  | fpc_in
  | xg0_a
  | xg0_b
  | xg1_a
  | xg1_b
  | fq2_in
  | xu1_a
  | xu1_b
  | fu1_in
  | xu0_a
  | xu0_b
  | xe2_a
  | xe2_b
  | xe1_a
  | xe1_b
  | xe0_a
  | xe0_b
  | ae_a
  | ae_b
  | am_a
  | am_b
  | pk_p0
  | pk_p1
  | pk_p2
  | pk_em
  | fq1_in
  | pk_q0
  | pk_q1
  | pk_q2
  | pk_g0
  | pk_g1
  | pk_g2
  | pk_r1
  | pk_r2
  | pk_r3
  deriving DecidableEq

/-- What each wire settles to: the specification's value for it.  One line per wire, and the
only place the shape of this netlist is written down. -/
def drv (s : RNextSt 2) : Drv W
  | _, .nem_a => W_unp_em s
  | _, .ok_a => s.inc
  | _, .ok_b => W_nem s
  | _, .fok_in => W_ok s
  | _, .fp0_in => W_unp_p0 s
  | _, .fp1_in => W_unp_p1 s
  | _, .xp0_a => W_unp_p0 s
  | _, .xp0_b => W_ok s
  | _, .cp0_a => W_unp_p0 s
  | _, .cp0_b => W_ok s
  | _, .fc0_in => W_cp0 s
  | _, .xp1_a => W_unp_p1 s
  | _, .xp1_b => W_cp0 s
  | _, .cp1_a => W_unp_p1 s
  | _, .cp1_b => W_cp0 s
  | _, .xp2_a => W_unp_p2 s
  | _, .xp2_b => W_cp1 s
  | _, .fpa_in => W_xp0 s
  | _, .fpb_in => W_xp1 s
  | _, .fpc_in => W_xp2 s
  | _, .xg0_a => W_xp1 s
  | _, .xg0_b => W_xp0 s
  | _, .xg1_a => W_xp2 s
  | _, .xg1_b => W_xp1 s
  | _, .fq2_in => W_unp_q22 s
  | _, .xu1_a => W_unp_q22 s
  | _, .xu1_b => W_unp_q21 s
  | _, .fu1_in => W_xu1 s
  | _, .xu0_a => W_xu1 s
  | _, .xu0_b => W_unp_q20 s
  | _, .xe2_a => W_xp2 s
  | _, .xe2_b => W_unp_q22 s
  | _, .xe1_a => W_xp1 s
  | _, .xe1_b => W_xu1 s
  | _, .xe0_a => W_xp0 s
  | _, .xe0_b => W_xu0 s
  | _, .ae_a => W_xe2 s
  | _, .ae_b => W_xe1 s
  | _, .am_a => W_ae s
  | _, .am_b => W_xe0 s
  | _, .pk_p0 => W_xp0 s
  | _, .pk_p1 => W_xp1 s
  | _, .pk_p2 => W_xp2 s
  | _, .pk_em => W_am s
  | _, .fq1_in => W_unp_q10 s
  | _, .pk_q0 => W_unp_q10 s
  | _, .pk_q1 => W_unp_q11 s
  | _, .pk_q2 => W_unp_q12 s
  | _, .pk_g0 => W_xg0 s
  | _, .pk_g1 => W_xg1 s
  | _, .pk_g2 => W_xp2 s
  | _, .pk_r1 => W_unp_p0 s
  | _, .pk_r2 => s.inc
  | _, .pk_r3 => W_unp_q10 s

theorem drv_mono {s} : Mono (drv s) := by
  intro a b _ k; cases k <;> exact List.prefix_rfl

/-- Growing the block's own inputs grows every value it computes.  `s` and `s'` are explicit:
they are only reachable through projections in the hypotheses, which unification cannot
invert, and left implicit the two collapse into one metavariable. -/
theorem drv_env (s : RNextSt 2) {st' : List (RSt 2)} {inc' : List Bool} {q1' : List (BitVec 3)} (hst : s.st <+: st') (hinc : s.inc <+: inc') (hq1 : s.q1 <+: q1') (w : Wires W) (k : W) :
    drv s w k <+: drv { s with st := st', inc := inc', q1 := q1' } w k := by
  cases k <;> simp only [drv]
  case nem_a => exact W_unp_em_mono hst hinc hq1
  case ok_a => exact hinc
  case ok_b => exact W_nem_mono hst hinc hq1
  case fok_in => exact W_ok_mono hst hinc hq1
  case fp0_in => exact W_unp_p0_mono hst hinc hq1
  case fp1_in => exact W_unp_p1_mono hst hinc hq1
  case xp0_a => exact W_unp_p0_mono hst hinc hq1
  case xp0_b => exact W_ok_mono hst hinc hq1
  case cp0_a => exact W_unp_p0_mono hst hinc hq1
  case cp0_b => exact W_ok_mono hst hinc hq1
  case fc0_in => exact W_cp0_mono hst hinc hq1
  case xp1_a => exact W_unp_p1_mono hst hinc hq1
  case xp1_b => exact W_cp0_mono hst hinc hq1
  case cp1_a => exact W_unp_p1_mono hst hinc hq1
  case cp1_b => exact W_cp0_mono hst hinc hq1
  case xp2_a => exact W_unp_p2_mono hst hinc hq1
  case xp2_b => exact W_cp1_mono hst hinc hq1
  case fpa_in => exact W_xp0_mono hst hinc hq1
  case fpb_in => exact W_xp1_mono hst hinc hq1
  case fpc_in => exact W_xp2_mono hst hinc hq1
  case xg0_a => exact W_xp1_mono hst hinc hq1
  case xg0_b => exact W_xp0_mono hst hinc hq1
  case xg1_a => exact W_xp2_mono hst hinc hq1
  case xg1_b => exact W_xp1_mono hst hinc hq1
  case fq2_in => exact W_unp_q22_mono hst hinc hq1
  case xu1_a => exact W_unp_q22_mono hst hinc hq1
  case xu1_b => exact W_unp_q21_mono hst hinc hq1
  case fu1_in => exact W_xu1_mono hst hinc hq1
  case xu0_a => exact W_xu1_mono hst hinc hq1
  case xu0_b => exact W_unp_q20_mono hst hinc hq1
  case xe2_a => exact W_xp2_mono hst hinc hq1
  case xe2_b => exact W_unp_q22_mono hst hinc hq1
  case xe1_a => exact W_xp1_mono hst hinc hq1
  case xe1_b => exact W_xu1_mono hst hinc hq1
  case xe0_a => exact W_xp0_mono hst hinc hq1
  case xe0_b => exact W_xu0_mono hst hinc hq1
  case ae_a => exact W_xe2_mono hst hinc hq1
  case ae_b => exact W_xe1_mono hst hinc hq1
  case am_a => exact W_ae_mono hst hinc hq1
  case am_b => exact W_xe0_mono hst hinc hq1
  case pk_p0 => exact W_xp0_mono hst hinc hq1
  case pk_p1 => exact W_xp1_mono hst hinc hq1
  case pk_p2 => exact W_xp2_mono hst hinc hq1
  case pk_em => exact W_am_mono hst hinc hq1
  case fq1_in => exact W_unp_q10_mono hst hinc hq1
  case pk_q0 => exact W_unp_q10_mono hst hinc hq1
  case pk_q1 => exact W_unp_q11_mono hst hinc hq1
  case pk_q2 => exact W_unp_q12_mono hst hinc hq1
  case pk_g0 => exact W_xg0_mono hst hinc hq1
  case pk_g1 => exact W_xg1_mono hst hinc hq1
  case pk_g2 => exact W_xp2_mono hst hinc hq1
  case pk_r1 => exact W_unp_p0_mono hst hinc hq1
  case pk_r2 => exact hinc
  case pk_r3 => exact W_unp_q10_mono hst hinc hq1

/-- The reduced state is a nested product ending in a `PackSt`; `wires` reads it as an
assignment. -/
def wires (i : gateNextRT) : Wires W
  | .nem_a => i.2.1
  | .ok_a => i.2.2.2.1.1
  | .ok_b => i.2.2.2.1.2
  | .fok_in => i.2.2.2.2.1
  | .fp0_in => i.2.2.2.2.2.1
  | .fp1_in => i.2.2.2.2.2.2.1
  | .xp0_a => i.2.2.2.2.2.2.2.2.1.1
  | .xp0_b => i.2.2.2.2.2.2.2.2.1.2
  | .cp0_a => i.2.2.2.2.2.2.2.2.2.1.1
  | .cp0_b => i.2.2.2.2.2.2.2.2.2.1.2
  | .fc0_in => i.2.2.2.2.2.2.2.2.2.2.1
  | .xp1_a => i.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xp1_b => i.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .cp1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .cp1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xp2_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xp2_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .fpa_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .fpb_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .fpc_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .xg0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xg0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xg1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xg1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .fq2_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .xu1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xu1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .fu1_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .xu0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xu0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xe2_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xe2_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xe1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xe1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xe0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xe0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .ae_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .ae_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .am_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .am_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .pk_p0 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.p0
  | .pk_p1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.p1
  | .pk_p2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.p2
  | .pk_em => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.em
  | .fq1_in => i.2.2.2.2.2.2.2.1
  | .pk_q0 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.q0
  | .pk_q1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.q1
  | .pk_q2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.q2
  | .pk_g0 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.g0
  | .pk_g1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.g1
  | .pk_g2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.g2
  | .pk_r1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.r1
  | .pk_r2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.r2
  | .pk_r3 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.r3

/-- The invariant: the wires are well formed, the inputs the netlist holds are the
specification's, and the packer has reported no more than the wires behind it hold. -/
def ψ (i : gateNextRT) (s : RNextSt 2) : Prop :=
  Wf (drv s) (wires i)
    ∧ i.1.1 = s.st
    ∧ i.1.2 = s.q1
    ∧ i.2.2.1 = s.inc
    ∧ s.d <+: packROut ⟨(wires i .pk_p0), (wires i .pk_p1), (wires i .pk_p2), (wires i .pk_em), (wires i .pk_q0), (wires i .pk_q1), (wires i .pk_q2), (wires i .pk_g0), (wires i .pk_g1), (wires i .pk_g2), (wires i .pk_r1), (wires i .pk_r2), (wires i .pk_r3)⟩

/-- What the block reports meets the specification's combinational contract. -/
theorem out_comb {s : RNextSt 2} {w : Wires W} (hw : Wf (drv s) w) :
    CombOut (rnextDep s) (rnextFun) (rnextLen s) 0 8 (packROut ⟨(w .pk_p0), (w .pk_p1), (w .pk_p2), (w .pk_em), (w .pk_q0), (w .pk_q1), (w .pk_q2), (w .pk_g0), (w .pk_g1), (w .pk_g2), (w .pk_r1), (w .pk_r2), (w .pk_r3)⟩) :=
  CombOut.of_prefix (packROut_mono' (hw .pk_p0) (hw .pk_p1) (hw .pk_p2) (hw .pk_em) (hw .pk_q0) (hw .pk_q1) (hw .pk_q2) (hw .pk_g0) (hw .pk_g1) (hw .pk_g2) (hw .pk_r1) (hw .pk_r2) (hw .pk_r3)) (W_pack_comb s)

/-! ### One tactic for every connection -/

/-- Each of the packer's inputs either stands or advances; one `⊏` is in scope. -/
syntax "gn_pre" : tactic
/-- Every wire of `mid` is the wire of `i`: what an input rule changes is an input. -/
syntax "gn_same" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| gn_pre) => `(tactic| first | exact List.prefix_rfl | exact (‹_ ⊏ _›).isPrefix)
  | `(tactic| gn_same) =>
      `(tactic| (intro j; cases j <;> dsimp only [wires] <;> exact List.prefix_rfl))

/-- `gn_case t` proves one connection: `t` is the monotonicity step that says the value now on
the wire is still a prefix of what the specification computes for it. -/
syntax "gn_case " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| gn_case $t:term) => `(tactic| (
      obtain ⟨⟨unp_st, unp_q1⟩, nem_a, finc_in, ⟨ok_a, ok_b⟩, fok_in, fp0_in, fp1_in, fq1_in, ⟨xp0_a, xp0_b⟩, ⟨cp0_a, cp0_b⟩, fc0_in, ⟨xp1_a, xp1_b⟩, ⟨cp1_a, cp1_b⟩, ⟨xp2_a, xp2_b⟩, fpa_in, fpb_in, fpc_in, ⟨xg0_a, xg0_b⟩, ⟨xg1_a, xg1_b⟩, fq2_in, ⟨xu1_a, xu1_b⟩, fu1_in, ⟨xu0_a, xu0_b⟩, ⟨xe2_a, xe2_b⟩, ⟨xe1_a, xe1_b⟩, ⟨xe0_a, xe0_b⟩, ⟨ae_a, ae_b⟩, ⟨am_a, am_b⟩, ⟨pk_p0, pk_p1, pk_p2, pk_em, pk_q0, pk_q1, pk_q2, pk_g0, pk_g1, pk_g2, pk_r1, pk_r2, pk_r3⟩⟩ := i
      obtain ⟨⟨_, _⟩, _, _, ⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _⟩, _, _, ⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e0, e1, e2, hd⟩ := H
      try dsimp only [] at e0
      try dsimp only [] at e1
      try dsimp only [] at e2
      refine ⟨s, existSR_reflexive, Wf_step_of hw drv_mono ?_ ?_,
        e0, e1, e2, ?_⟩
      · intro j
        cases j <;> dsimp only [wires] <;> gn_pre
      · intro j
        have hj := hw j
        cases j <;> (try dsimp only [wires, drv] at hj) <;> dsimp only [wires, drv] <;>
          first | exact hj | exact $t
      · dsimp only [wires] at hd ⊢
        exact hd.trans (packROut_mono' (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre))))

theorem gateNextR_internals_eq : gateNextR.internals =
    [gateNextR.internals.getD 0 (fun _ _ => False), gateNextR.internals.getD 1 (fun _ _ => False), gateNextR.internals.getD 2 (fun _ _ => False),
     gateNextR.internals.getD 3 (fun _ _ => False), gateNextR.internals.getD 4 (fun _ _ => False), gateNextR.internals.getD 5 (fun _ _ => False),
     gateNextR.internals.getD 6 (fun _ _ => False), gateNextR.internals.getD 7 (fun _ _ => False), gateNextR.internals.getD 8 (fun _ _ => False),
     gateNextR.internals.getD 9 (fun _ _ => False), gateNextR.internals.getD 10 (fun _ _ => False), gateNextR.internals.getD 11 (fun _ _ => False),
     gateNextR.internals.getD 12 (fun _ _ => False), gateNextR.internals.getD 13 (fun _ _ => False), gateNextR.internals.getD 14 (fun _ _ => False),
     gateNextR.internals.getD 15 (fun _ _ => False), gateNextR.internals.getD 16 (fun _ _ => False), gateNextR.internals.getD 17 (fun _ _ => False),
     gateNextR.internals.getD 18 (fun _ _ => False), gateNextR.internals.getD 19 (fun _ _ => False), gateNextR.internals.getD 20 (fun _ _ => False),
     gateNextR.internals.getD 21 (fun _ _ => False), gateNextR.internals.getD 22 (fun _ _ => False), gateNextR.internals.getD 23 (fun _ _ => False),
     gateNextR.internals.getD 24 (fun _ _ => False), gateNextR.internals.getD 25 (fun _ _ => False), gateNextR.internals.getD 26 (fun _ _ => False),
     gateNextR.internals.getD 27 (fun _ _ => False), gateNextR.internals.getD 28 (fun _ _ => False), gateNextR.internals.getD 29 (fun _ _ => False),
     gateNextR.internals.getD 30 (fun _ _ => False), gateNextR.internals.getD 31 (fun _ _ => False), gateNextR.internals.getD 32 (fun _ _ => False),
     gateNextR.internals.getD 33 (fun _ _ => False), gateNextR.internals.getD 34 (fun _ _ => False), gateNextR.internals.getD 35 (fun _ _ => False),
     gateNextR.internals.getD 36 (fun _ _ => False), gateNextR.internals.getD 37 (fun _ _ => False), gateNextR.internals.getD 38 (fun _ _ => False),
     gateNextR.internals.getD 39 (fun _ _ => False), gateNextR.internals.getD 40 (fun _ _ => False), gateNextR.internals.getD 41 (fun _ _ => False),
     gateNextR.internals.getD 42 (fun _ _ => False), gateNextR.internals.getD 43 (fun _ _ => False), gateNextR.internals.getD 44 (fun _ _ => False),
     gateNextR.internals.getD 45 (fun _ _ => False), gateNextR.internals.getD 46 (fun _ _ => False), gateNextR.internals.getD 47 (fun _ _ => False),
     gateNextR.internals.getD 48 (fun _ _ => False), gateNextR.internals.getD 49 (fun _ _ => False), gateNextR.internals.getD 50 (fun _ _ => False),
     gateNextR.internals.getD 51 (fun _ _ => False), gateNextR.internals.getD 52 (fun _ _ => False), gateNextR.internals.getD 53 (fun _ _ => False)] := rfl

/-! All 54 connections, one line each: the wire, and why its new value is still
a prefix of what the specification computes. -/

theorem case_0 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- nem_a

theorem case_1 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (e2 ▸ List.prefix_rfl)   -- ok_a

theorem case_2 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gate1Out_mono _ (hw .nem_a)   -- ok_b

theorem case_3 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .ok_a) (hw .ok_b)   -- fok_in

theorem case_4 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- fp0_in

theorem case_5 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- fp1_in

theorem case_6 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp0_in)   -- xp0_a

theorem case_7 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fok_in)   -- xp0_b

theorem case_8 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp0_in)   -- cp0_a

theorem case_9 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fok_in)   -- cp0_b

theorem case_10 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .cp0_a) (hw .cp0_b)   -- fc0_in

theorem case_11 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp1_in)   -- xp1_a

theorem case_12 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fc0_in)   -- xp1_b

theorem case_13 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp1_in)   -- cp1_a

theorem case_14 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fc0_in)   -- cp1_b

theorem case_15 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- xp2_a

theorem case_16 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .cp1_a) (hw .cp1_b)   -- xp2_b

theorem case_17 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xp0_a) (hw .xp0_b)   -- fpa_in

theorem case_18 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xp1_a) (hw .xp1_b)   -- fpb_in

theorem case_19 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xp2_a) (hw .xp2_b)   -- fpc_in

theorem case_20 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpb_in)   -- xg0_a

theorem case_21 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpa_in)   -- xg0_b

theorem case_22 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpc_in)   -- xg1_a

theorem case_23 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpb_in)   -- xg1_b

theorem case_24 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- fq2_in

theorem case_25 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fq2_in)   -- xu1_a

theorem case_26 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- xu1_b

theorem case_27 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xu1_a) (hw .xu1_b)   -- fu1_in

theorem case_28 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 28 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fu1_in)   -- xu0_a

theorem case_29 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 29 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- xu0_b

theorem case_30 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 30 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpc_in)   -- xe2_a

theorem case_31 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 31 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fq2_in)   -- xe2_b

theorem case_32 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 32 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpb_in)   -- xe1_a

theorem case_33 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 33 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fu1_in)   -- xe1_b

theorem case_34 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 34 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpa_in)   -- xe0_a

theorem case_35 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 35 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xu0_a) (hw .xu0_b)   -- xe0_b

theorem case_36 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 36 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xe2_a) (hw .xe2_b)   -- ae_a

theorem case_37 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 37 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xe1_a) (hw .xe1_b)   -- ae_b

theorem case_38 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 38 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .ae_a) (hw .ae_b)   -- am_a

theorem case_39 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 39 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xe0_a) (hw .xe0_b)   -- am_b

theorem case_40 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 40 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpa_in)   -- pk_p0

theorem case_41 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 41 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpb_in)   -- pk_p1

theorem case_42 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 42 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpc_in)   -- pk_p2

theorem case_43 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 43 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .am_a) (hw .am_b)   -- pk_em

theorem case_44 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 44 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e1]; exact List.prefix_rfl)   -- fq1_in

theorem case_45 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 45 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fq1_in)   -- pk_q0

theorem case_46 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 46 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e1]; exact List.prefix_rfl)   -- pk_q1

theorem case_47 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 47 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e1]; exact List.prefix_rfl)   -- pk_q2

theorem case_48 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 48 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xg0_a) (hw .xg0_b)   -- pk_g0

theorem case_49 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 49 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xg1_a) (hw .xg1_b)   -- pk_g1

theorem case_50 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 50 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpc_in)   -- pk_g2

theorem case_51 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 51 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp0_in)   -- pk_r1

theorem case_52 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 52 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (e2 ▸ List.prefix_rfl)   -- pk_r2

theorem case_53 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 53 (fun _ _ => False)) i mid) :
    ∃ s', existSR (rnextBlock (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fq1_in)   -- pk_r3

/-! ### The specification's own rules -/

section SpecRules
variable (sp : RNextSt 2)
theorem spec_in_st (v : List (RSt 2)) (h : sp.st ⊏ v) :
    ((rnextBlock (n := 2) 0 8).inputs.getIO ↑"st").2 sp v { sp with st := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_inc (v : List Bool) (h : sp.inc ⊏ v) :
    ((rnextBlock (n := 2) 0 8).inputs.getIO ↑"inc").2 sp v { sp with inc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_q1 (v : List (BitVec 3)) (h : sp.q1 ⊏ v) :
    ((rnextBlock (n := 2) 0 8).inputs.getIO ↑"q1").2 sp v { sp with q1 := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_out_d (v : List (RNext 2)) (h1 : sp.d <+: v)
    (h2 : CombOut (rnextDep sp) (rnextFun) (rnextLen sp) 0 8 v) :
    ((rnextBlock (n := 2) 0 8).outputs.getIO ↑"d").2 sp v { sp with d := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : gateNextR ⊑_{ψ} (rnextBlock (n := 2) 0 8) := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨unp_st, unp_q1⟩, nem_a, finc_in, ⟨ok_a, ok_b⟩, fok_in, fp0_in, fp1_in, fq1_in, ⟨xp0_a, xp0_b⟩, ⟨cp0_a, cp0_b⟩, fc0_in, ⟨xp1_a, xp1_b⟩, ⟨cp1_a, cp1_b⟩, ⟨xp2_a, xp2_b⟩, fpa_in, fpb_in, fpc_in, ⟨xg0_a, xg0_b⟩, ⟨xg1_a, xg1_b⟩, fq2_in, ⟨xu1_a, xu1_b⟩, fu1_in, ⟨xu0_a, xu0_b⟩, ⟨xe2_a, xe2_b⟩, ⟨xe1_a, xe1_b⟩, ⟨xe0_a, xe0_b⟩, ⟨ae_a, ae_b⟩, ⟨am_a, am_b⟩, ⟨pk_p0, pk_p1, pk_p2, pk_em, pk_q0, pk_q1, pk_q2, pk_g0, pk_g1, pk_g2, pk_r1, pk_r2, pk_r3⟩⟩ := i
    obtain ⟨⟨_, _⟩, _, _, ⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, hd⟩ := H
    try dsimp only [] at e0
    try dsimp only [] at e1
    try dsimp only [] at e2
    case_transition Hcontains : Module.inputs gateNextR, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [gateNextR] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    all_goals dsimp only [wires] at hd
    -- Both pieces are carried across pointwise; see `NetlistWf.lean` for why.
    all_goals first
      | (refine ⟨_, _, spec_in_st s _ (by rw [← e0]; exact hpre), existSR_reflexive,
             ?wf, rfl, e1, e2, ?hist⟩
         case wf =>
           exact Wf_congr drv_mono (Wf_drv hw (drv_env s (by rw [← e0]; exact hpre.isPrefix) List.prefix_rfl List.prefix_rfl _))
             (by gn_same) (by gn_same)
         case hist => exact hd.trans (packROut_mono' List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl))
      | (refine ⟨_, _, spec_in_q1 s _ (by rw [← e1]; exact hpre), existSR_reflexive,
             ?wf, e0, rfl, e2, ?hist⟩
         case wf =>
           exact Wf_congr drv_mono (Wf_drv hw (drv_env s List.prefix_rfl List.prefix_rfl (by rw [← e1]; exact hpre.isPrefix) _))
             (by gn_same) (by gn_same)
         case hist => exact hd.trans (packROut_mono' List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl))
      | (refine ⟨_, _, spec_in_inc s _ (by rw [← e2]; exact hpre), existSR_reflexive,
             ?wf, e0, e1, rfl, ?hist⟩
         case wf =>
           exact Wf_congr drv_mono (Wf_drv hw (drv_env s List.prefix_rfl (by rw [← e2]; exact hpre.isPrefix) List.prefix_rfl _))
             (by gn_same) (by gn_same)
         case hist => exact hd.trans (packROut_mono' List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl))
  · intro ident mid_i v Hrule
    obtain ⟨⟨unp_st, unp_q1⟩, nem_a, finc_in, ⟨ok_a, ok_b⟩, fok_in, fp0_in, fp1_in, fq1_in, ⟨xp0_a, xp0_b⟩, ⟨cp0_a, cp0_b⟩, fc0_in, ⟨xp1_a, xp1_b⟩, ⟨cp1_a, cp1_b⟩, ⟨xp2_a, xp2_b⟩, fpa_in, fpb_in, fpc_in, ⟨xg0_a, xg0_b⟩, ⟨xg1_a, xg1_b⟩, fq2_in, ⟨xu1_a, xu1_b⟩, fu1_in, ⟨xu0_a, xu0_b⟩, ⟨xe2_a, xe2_b⟩, ⟨xe1_a, xe1_b⟩, ⟨xe0_a, xe0_b⟩, ⟨ae_a, ae_b⟩, ⟨am_a, am_b⟩, ⟨pk_p0, pk_p1, pk_p2, pk_em, pk_q0, pk_q1, pk_q2, pk_g0, pk_g1, pk_g2, pk_r1, pk_r2, pk_r3⟩⟩ := i
    obtain ⟨⟨_, _⟩, _, _, ⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, hd⟩ := H
    try dsimp only [] at e0
    try dsimp only [] at e1
    try dsimp only [] at e2
    have ho := out_comb hw
    dsimp only [wires] at ho hd
    case_transition Hcontains : Module.outputs gateNextR, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [gateNextR] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    exact ⟨s, _, existSR_reflexive, spec_out_d s _ hd ho,
      hw, e0, e1, e2, List.prefix_rfl⟩
  · intro rule mid_i Hin Hrule
    rw [gateNextR_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact case_0 s i mid_i H Hrule
    · subst h; exact case_1 s i mid_i H Hrule
    · subst h; exact case_2 s i mid_i H Hrule
    · subst h; exact case_3 s i mid_i H Hrule
    · subst h; exact case_4 s i mid_i H Hrule
    · subst h; exact case_5 s i mid_i H Hrule
    · subst h; exact case_6 s i mid_i H Hrule
    · subst h; exact case_7 s i mid_i H Hrule
    · subst h; exact case_8 s i mid_i H Hrule
    · subst h; exact case_9 s i mid_i H Hrule
    · subst h; exact case_10 s i mid_i H Hrule
    · subst h; exact case_11 s i mid_i H Hrule
    · subst h; exact case_12 s i mid_i H Hrule
    · subst h; exact case_13 s i mid_i H Hrule
    · subst h; exact case_14 s i mid_i H Hrule
    · subst h; exact case_15 s i mid_i H Hrule
    · subst h; exact case_16 s i mid_i H Hrule
    · subst h; exact case_17 s i mid_i H Hrule
    · subst h; exact case_18 s i mid_i H Hrule
    · subst h; exact case_19 s i mid_i H Hrule
    · subst h; exact case_20 s i mid_i H Hrule
    · subst h; exact case_21 s i mid_i H Hrule
    · subst h; exact case_22 s i mid_i H Hrule
    · subst h; exact case_23 s i mid_i H Hrule
    · subst h; exact case_24 s i mid_i H Hrule
    · subst h; exact case_25 s i mid_i H Hrule
    · subst h; exact case_26 s i mid_i H Hrule
    · subst h; exact case_27 s i mid_i H Hrule
    · subst h; exact case_28 s i mid_i H Hrule
    · subst h; exact case_29 s i mid_i H Hrule
    · subst h; exact case_30 s i mid_i H Hrule
    · subst h; exact case_31 s i mid_i H Hrule
    · subst h; exact case_32 s i mid_i H Hrule
    · subst h; exact case_33 s i mid_i H Hrule
    · subst h; exact case_34 s i mid_i H Hrule
    · subst h; exact case_35 s i mid_i H Hrule
    · subst h; exact case_36 s i mid_i H Hrule
    · subst h; exact case_37 s i mid_i H Hrule
    · subst h; exact case_38 s i mid_i H Hrule
    · subst h; exact case_39 s i mid_i H Hrule
    · subst h; exact case_40 s i mid_i H Hrule
    · subst h; exact case_41 s i mid_i H Hrule
    · subst h; exact case_42 s i mid_i H Hrule
    · subst h; exact case_43 s i mid_i H Hrule
    · subst h; exact case_44 s i mid_i H Hrule
    · subst h; exact case_45 s i mid_i H Hrule
    · subst h; exact case_46 s i mid_i H Hrule
    · subst h; exact case_47 s i mid_i H Hrule
    · subst h; exact case_48 s i mid_i H Hrule
    · subst h; exact case_49 s i mid_i H Hrule
    · subst h; exact case_50 s i mid_i H Hrule
    · subst h; exact case_51 s i mid_i H Hrule
    · subst h; exact case_52 s i mid_i H Hrule
    · subst h; exact case_53 s i mid_i H Hrule

theorem refines_initial : Module.refines_initial gateNextR (rnextBlock (n := 2) 0 8) ψ := by
  intro i hi
  obtain ⟨⟨unp_st, unp_q1⟩, nem_a, finc_in, ⟨ok_a, ok_b⟩, fok_in, fp0_in, fp1_in, fq1_in, ⟨xp0_a, xp0_b⟩, ⟨cp0_a, cp0_b⟩, fc0_in, ⟨xp1_a, xp1_b⟩, ⟨cp1_a, cp1_b⟩, ⟨xp2_a, xp2_b⟩, fpa_in, fpb_in, fpc_in, ⟨xg0_a, xg0_b⟩, ⟨xg1_a, xg1_b⟩, fq2_in, ⟨xu1_a, xu1_b⟩, fu1_in, ⟨xu0_a, xu0_b⟩, ⟨xe2_a, xe2_b⟩, ⟨xe1_a, xe1_b⟩, ⟨xe0_a, xe0_b⟩, ⟨ae_a, ae_b⟩, ⟨am_a, am_b⟩, ⟨pk_p0, pk_p1, pk_p2, pk_em, pk_q0, pk_q1, pk_q2, pk_g0, pk_g1, pk_g2, pk_r1, pk_r2, pk_r3⟩⟩ := i
  dsimp only [gateNextR] at hi
  simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The gates refine the next-state block.** -/
theorem gateNextR_refines : gateNextR ⊑ (rnextBlock (n := 2) 0 8) :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.GateNextR
