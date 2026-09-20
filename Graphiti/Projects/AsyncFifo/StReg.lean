/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Dff
import Graphiti.Projects.AsyncFifo.NetlistWf
import Graphiti.Projects.AsyncFifo.Timed

/-!
# The state register from seven flip-flops

The write domain's state is a `WSt 2`: a three-bit pointer, the `full` flag, and the three bits
of the second synchroniser stage.  Seven flip-flops, then, sharing a clock and a clear, with the
record split into bits on the way in and reassembled on the way out.

This is `BusReg.lean` at another width and over a record rather than a bit vector, and the proof
is the same one.

`StRegR.lean` is this same register at the read domain's record, and the two files are
line-for-line the same apart from the polarity of bit `3` --- about four hundred duplicated
lines.  Factoring them into one register generic in the record was tried and abandoned, and the
obstruction is worth recording because it is not the obvious one.  A parameterised *environment*
reduces perfectly well (`Timed.lean` does it), but a node whose state type is abstract does not:
with the record behind an interface, `unpackSt` and `packSt` become stuck applications, and
`def_module` reducing the graph through them cost ten times the heartbeat budget for the state
*type* alone and had not finished the *module* after ten minutes at two hundred times it.  So
the netlist has to name a concrete record, and what is left to share --- `bitsOf`, `packStOut`,
`stOut` and their monotonicity --- is about seventy of the four hundred lines, which does not
pay for an abstraction the netlist itself could not use.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.StReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Dff

/-! ### The record and its bits -/

/-- The seven bits of the write domain's state: the pointer, the flag, the second stage. -/
def stBit (i : Nat) (x : WSt 2) : Bool :=
  if i < 3 then x.ptr.getLsbD i else if i = 3 then x.full else x.q2.getLsbD (i - 4)

/-- A record is its bits. -/
theorem stBit_all (x : WSt 2) :
    (⟨bv3 (stBit 0 x) (stBit 1 x) (stBit 2 x), stBit 3 x,
      bv3 (stBit 4 x) (stBit 5 x) (stBit 6 x)⟩ : WSt 2) = x := by
  obtain ⟨ptr, full, q2⟩ := x
  simp only [stBit, WSt.mk.injEq]
  refine ⟨?_, rfl, ?_⟩
  · show bv3 (ptr.getLsbD 0) (ptr.getLsbD 1) (ptr.getLsbD 2) = ptr
    revert ptr; decide
  · show bv3 (q2.getLsbD 0) (q2.getLsbD 1) (q2.getLsbD 2) = q2
    revert q2; decide

@[simp] theorem stBit_default (i : Nat) : stBit i (default : WSt 2) = false := by
  unfold stBit
  split
  · show (0#3).getLsbD i = false
    simp
  · split
    · rfl
    · show (0#3).getLsbD (i - 4) = false
      simp

def bitsOf (i : Nat) (d : List (WSt 2)) : List Bool := d.map (stBit i)

@[simp] theorem bitsOf_length (i : Nat) (d : List (WSt 2)) : (bitsOf i d).length = d.length := by
  simp [bitsOf]

theorem bitsOf_mono {i : Nat} {d d' : List (WSt 2)} (h : d <+: d') : bitsOf i d <+: bitsOf i d' :=
  h.map _

theorem bitsOf_getD_all (i : Nat) (d : List (WSt 2)) (u : Nat) :
    (bitsOf i d).getD u false = stBit i (d.getD u default) := by
  by_cases h : u < d.length
  · simp [bitsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [bitsOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

/-! ### The bus adapters -/

/-- Split the state record into its seven bits. -/
@[drcomponents]
def unpackSt : StringModule (List (WSt 2)) :=
  { inputs := [ (↑"d", ⟨List (WSt 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"b0", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 0 s⟩)
               , (↑"b1", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 1 s⟩)
               , (↑"b2", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 2 s⟩)
               , (↑"b3", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 3 s⟩)
               , (↑"b4", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 4 s⟩)
               , (↑"b5", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 5 s⟩)
               , (↑"b6", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 6 s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The record assembled from its bits, known as far as every bit is. -/
def packStOut (b0 b1 b2 b3 b4 b5 b6 : List Bool) : List (WSt 2) :=
  timeline (fun t => ⟨bv3 (b0.getD t false) (b1.getD t false) (b2.getD t false), b3.getD t false,
      bv3 (b4.getD t false) (b5.getD t false) (b6.getD t false)⟩)
    (min (min (min b0.length b1.length) (min b2.length b3.length))
      (min (min b4.length b5.length) b6.length))

@[simp] theorem packStOut_length (b0 b1 b2 b3 b4 b5 b6 : List Bool) :
    (packStOut b0 b1 b2 b3 b4 b5 b6).length =
      min (min (min b0.length b1.length) (min b2.length b3.length))
        (min (min b4.length b5.length) b6.length) := timeline_length _ _

theorem packStOut_getD {b0 b1 b2 b3 b4 b5 b6 : List Bool} {t : Nat}
    (ht : t < min (min (min b0.length b1.length) (min b2.length b3.length))
      (min (min b4.length b5.length) b6.length)) :
    (packStOut b0 b1 b2 b3 b4 b5 b6).getD t default =
      ⟨bv3 (b0.getD t false) (b1.getD t false) (b2.getD t false), b3.getD t false,
        bv3 (b4.getD t false) (b5.getD t false) (b6.getD t false)⟩ := timeline_getD _ ht _

theorem packStOut_mono {b0 b0' b1 b1' b2 b2' b3 b3' b4 b4' b5 b5' b6 b6' : List Bool}
    (h0 : b0 <+: b0') (h1 : b1 <+: b1') (h2 : b2 <+: b2') (h3 : b3 <+: b3') (h4 : b4 <+: b4')
    (h5 : b5 <+: b5') (h6 : b6 <+: b6') :
    packStOut b0 b1 b2 b3 b4 b5 b6 <+: packStOut b0' b1' b2' b3' b4' b5' b6' := by
  have := h0.length_le; have := h1.length_le; have := h2.length_le; have := h3.length_le
  have := h4.length_le; have := h5.length_le; have := h6.length_le
  apply timeline_mono (by omega)
  intro t ht
  simp only [Nat.lt_min] at ht
  rw [h0.getD_eq_left (by omega), h1.getD_eq_left (by omega), h2.getD_eq_left (by omega),
    h3.getD_eq_left (by omega), h4.getD_eq_left (by omega), h5.getD_eq_left (by omega),
    h6.getD_eq_left (by omega)]

/-- Assemble the state record from its seven bits. -/
@[drcomponents]
def packSt : StringModule (List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"b0", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"b1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"b2", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"b3", ⟨List Bool, fun s v s' => s.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
              , (↑"b4", ⟨List Bool, fun s v s' => s.2.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩)
              , (↑"b5", ⟨List Bool, fun s v s' => s.2.2.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v, s.2.2.2.2.2.2)⟩)
              , (↑"b6", ⟨List Bool, fun s v s' => s.2.2.2.2.2.2 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List (WSt 2), fun s v s' => s' = s ∧
                    v = packStOut s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1
                      s.2.2.2.2.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], [], []) }

/-! ### The netlist -/

def stGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    q [type="io"];

    unp [type="unpackSt", typeImp=$(⟨_, unpackSt⟩)];
    clkF [type="fork7", typeImp=$(⟨_, fork7⟩)];
    crF [type="fork7", typeImp=$(⟨_, fork7⟩)];
    ff0 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff1 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff2 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff3 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff4 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff5 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff6 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    pk [type="packSt", typeImp=$(⟨_, packSt⟩)];

    clk -> clkF [to="in"];
    d -> unp [to="d"];
    clrn -> crF [to="in"];

    clkF -> ff0 [from="out1", to="clk"];
    clkF -> ff1 [from="out2", to="clk"];
    clkF -> ff2 [from="out3", to="clk"];
    clkF -> ff3 [from="out4", to="clk"];
    clkF -> ff4 [from="out5", to="clk"];
    clkF -> ff5 [from="out6", to="clk"];
    clkF -> ff6 [from="out7", to="clk"];
    crF -> ff0 [from="out1", to="clrn"];
    crF -> ff1 [from="out2", to="clrn"];
    crF -> ff2 [from="out3", to="clrn"];
    crF -> ff3 [from="out4", to="clrn"];
    crF -> ff4 [from="out5", to="clrn"];
    crF -> ff5 [from="out6", to="clrn"];
    crF -> ff6 [from="out7", to="clrn"];
    unp -> ff0 [from="b0", to="d"];
    unp -> ff1 [from="b1", to="d"];
    unp -> ff2 [from="b2", to="d"];
    unp -> ff3 [from="b3", to="d"];
    unp -> ff4 [from="b4", to="d"];
    unp -> ff5 [from="b5", to="d"];
    unp -> ff6 [from="b6", to="d"];
    ff0 -> pk [from="q", to="b0"];
    ff1 -> pk [from="q", to="b1"];
    ff2 -> pk [from="q", to="b2"];
    ff3 -> pk [from="q", to="b3"];
    ff4 -> pk [from="q", to="b4"];
    ff5 -> pk [from="q", to="b5"];
    ff6 -> pk [from="q", to="b6"];

    pk -> q [from="q"];
  ]

@[drunfold_defs]
def stLowered := stGraph.1.lower_TR |>.get rfl

def senv := stGraph.2

@[drenv] theorem senv_unpackSt : senv.find? "unpackSt" = .some ⟨_, unpackSt⟩ := rfl
@[drenv] theorem senv_fork7 : senv.find? "fork7" = .some ⟨_, fork7⟩ := rfl
@[drenv] theorem senv_dff : senv.find? "dff" = .some ⟨_, dffSpec⟩ := rfl
@[drenv] theorem senv_packSt : senv.find? "packSt" = .some ⟨_, packSt⟩ := rfl

seal senv in
def_module stT : Type :=
  [T| stLowered, senv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal senv in
def_module stNetlist : StringModule stT :=
  [e| stLowered, senv.find? ]

/-! ### The specification -/

/-- What the register reports: each bit of the bus through its own flip-flop. -/
def stOut (clk : List Bool) (d : List (WSt 2)) (crn : List Bool) : List (WSt 2) :=
  packStOut (dffOut clk (bitsOf 0 d) crn) (dffOut clk (bitsOf 1 d) crn) (dffOut clk (bitsOf 2 d) crn) (dffOut clk (bitsOf 3 d) crn) (dffOut clk (bitsOf 4 d) crn) (dffOut clk (bitsOf 5 d) crn) (dffOut clk (bitsOf 6 d) crn)

theorem stOut_mono {clk clk' : List Bool} {d d' : List (WSt 2)}
    {crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d') (hr : crn <+: crn') :
    stOut clk d crn <+: stOut clk' d' crn' :=
  packStOut_mono (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr)

/-- The seven-bit state register as a single block. -/
@[drcomponents]
def stSpec : StringModule (List Bool × List (WSt 2) × List Bool × List (WSt 2)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (WSt 2), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List (WSt 2), fun s v s' => s.2.2.2 <+: v ∧
                    v <+: stOut s.1 s.2.1 s.2.2.1 ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

instance : MatchInterface stNetlist stSpec := by
  dsimp [stNetlist, stSpec]
  solve_match_interface

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Stated over an index rather than as a record
with one field per wire, the per-rule lemmas collapse into `Netlist.Wf_set` and
`Netlist.Wf_drv`, so what is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The 28 driven wires. -/
inductive W | pk0 | pk1 | pk2 | pk3 | pk4 | pk5 | pk6
            | f0clk | f0d | f0crn
            | f1clk | f1d | f1crn
            | f2clk | f2d | f2crn
            | f3clk | f3d | f3crn
            | f4clk | f4d | f4crn
            | f5clk | f5d | f5crn
            | f6clk | f6d | f6crn
  deriving DecidableEq

/-- What drives each wire: one line per wire, and the only place the shape of this netlist
is written down. -/
def drv (clk crn : List Bool) (d : List (WSt 2)) : Drv W
  | w, .pk0 => dffOut (w .f0clk) (w .f0d) (w .f0crn)
  | w, .pk1 => dffOut (w .f1clk) (w .f1d) (w .f1crn)
  | w, .pk2 => dffOut (w .f2clk) (w .f2d) (w .f2crn)
  | w, .pk3 => dffOut (w .f3clk) (w .f3d) (w .f3crn)
  | w, .pk4 => dffOut (w .f4clk) (w .f4d) (w .f4crn)
  | w, .pk5 => dffOut (w .f5clk) (w .f5d) (w .f5crn)
  | w, .pk6 => dffOut (w .f6clk) (w .f6d) (w .f6crn)
  | _, .f0clk | _, .f1clk | _, .f2clk | _, .f3clk | _, .f4clk | _, .f5clk | _, .f6clk => clk
  | _, .f0crn | _, .f1crn | _, .f2crn | _, .f3crn | _, .f4crn | _, .f5crn | _, .f6crn => crn
  | _, .f0d => bitsOf 0 d
  | _, .f1d => bitsOf 1 d
  | _, .f2d => bitsOf 2 d
  | _, .f3d => bitsOf 3 d
  | _, .f4d => bitsOf 4 d
  | _, .f5d => bitsOf 5 d
  | _, .f6d => bitsOf 6 d

theorem drv_mono {clk crn d} : Mono (drv clk crn d) := by
  intro a b h k
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, h, dffOut_mono]
theorem drv_env {clk clk' crn crn' : List Bool} {d d' : List (WSt 2)}
    (hc : clk <+: clk') (hr : crn <+: crn') (hd : d <+: d') (w : Wires W) (k : W) :
    drv clk crn d w k <+: drv clk' crn' d' w k := by
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, hc, hd, hr, bitsOf_mono]
def wires (i : stT) : Wires W
  | .pk0 => i.1.1
  | .pk1 => i.1.2.1
  | .pk2 => i.1.2.2.1
  | .pk3 => i.1.2.2.2.1
  | .pk4 => i.1.2.2.2.2.1
  | .pk5 => i.1.2.2.2.2.2.1
  | .pk6 => i.1.2.2.2.2.2.2
  | .f0clk => i.2.2.2.2.2.2.2.2.1.1 | .f0d => i.2.2.2.2.2.2.2.2.1.2.1 | .f0crn => i.2.2.2.2.2.2.2.2.1.2.2
  | .f1clk => i.2.2.2.2.2.2.2.2.2.1.1 | .f1d => i.2.2.2.2.2.2.2.2.2.1.2.1 | .f1crn => i.2.2.2.2.2.2.2.2.2.1.2.2
  | .f2clk => i.2.2.2.2.2.2.2.2.2.2.1 | .f2d => i.2.2.2.2.2.2.2.2.2.2.2.1 | .f2crn => i.2.2.2.2.2.2.2.2.2.2.2.2
  | .f3clk => i.2.2.2.2.2.2.1.1 | .f3d => i.2.2.2.2.2.2.1.2.1 | .f3crn => i.2.2.2.2.2.2.1.2.2
  | .f4clk => i.2.2.2.2.2.2.2.1.1 | .f4d => i.2.2.2.2.2.2.2.1.2.1 | .f4crn => i.2.2.2.2.2.2.2.1.2.2
  | .f5clk => i.2.2.2.2.1.1 | .f5d => i.2.2.2.2.1.2.1 | .f5crn => i.2.2.2.2.1.2.2
  | .f6clk => i.2.1.1 | .f6d => i.2.1.2.1 | .f6crn => i.2.1.2.2

def ψ (i : stT) (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) : Prop :=
  Wf (drv s.1 s.2.2.1 s.2.1) (wires i) ∧ i.2.2.2.2.2.1 = s.1 ∧ i.2.2.1 = s.2.1
    ∧ i.2.2.2.1 = s.2.2.1 ∧ s.2.2.2 <+: packStOut (wires i .pk0) (wires i .pk1) (wires i .pk2) (wires i .pk3) (wires i .pk4) (wires i .pk5) (wires i .pk6)

/-- What the block reports is a prefix of what the specification says. -/
theorem out_q {clk crn d} {w : Wires W} (hw : Wf (drv clk crn d) w) :
    packStOut (w .pk0) (w .pk1) (w .pk2) (w .pk3) (w .pk4) (w .pk5) (w .pk6) <+: stOut clk d crn := by
  refine packStOut_mono ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (hw .pk0).trans (dffOut_mono (hw .f0clk) (hw .f0d) (hw .f0crn))
  · exact (hw .pk1).trans (dffOut_mono (hw .f1clk) (hw .f1d) (hw .f1crn))
  · exact (hw .pk2).trans (dffOut_mono (hw .f2clk) (hw .f2d) (hw .f2crn))
  · exact (hw .pk3).trans (dffOut_mono (hw .f3clk) (hw .f3d) (hw .f3crn))
  · exact (hw .pk4).trans (dffOut_mono (hw .f4clk) (hw .f4d) (hw .f4crn))
  · exact (hw .pk5).trans (dffOut_mono (hw .f5clk) (hw .f5d) (hw .f5crn))
  · exact (hw .pk6).trans (dffOut_mono (hw .f6clk) (hw .f6d) (hw .f6crn))

/-! ### One tactic for every connection -/

syntax "st_case " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| st_case $w:term) => `(tactic| (
      obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6⟩, ⟨x6,y6,z6⟩, ud, cr, ⟨x5,y5,z5⟩, ck, ⟨x3,y3,z3⟩, ⟨x4,y4,z4⟩, ⟨x0,y0,z0⟩, ⟨x1,y1,z1⟩, ⟨x2,y2,z2⟩⟩ := i
      obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_,_,_⟩, _, _, ⟨_,_,_⟩, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _, _, _, _, _, _⟩, ⟨_,_,_⟩, _, _, ⟨_,_,_⟩, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e1, e2, e3, hq⟩ := H
      refine ⟨s, existSR_reflexive, ?_, e1, e2, e3, ?_⟩
      · have key := Wf_set drv_mono hw $w _ (‹_ ⊏ _›).isPrefix (by
          simp only [drv, wires]
          first
            | exact e1 ▸ List.prefix_rfl
            | exact e3 ▸ List.prefix_rfl
            | exact e2 ▸ List.prefix_rfl
            | assumption)
        intro j; have hj := key j; revert hj; cases j <;> simp [wires, upd, drv]
      · have key := hq.trans (packStOut_mono
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _)
          )
        revert key; simp [wires, upd]))

theorem stNetlist_internals_eq : stNetlist.internals =
    [stNetlist.internals.getD 0 (fun _ _ => False), stNetlist.internals.getD 1 (fun _ _ => False), stNetlist.internals.getD 2 (fun _ _ => False),
     stNetlist.internals.getD 3 (fun _ _ => False), stNetlist.internals.getD 4 (fun _ _ => False), stNetlist.internals.getD 5 (fun _ _ => False),
     stNetlist.internals.getD 6 (fun _ _ => False), stNetlist.internals.getD 7 (fun _ _ => False), stNetlist.internals.getD 8 (fun _ _ => False),
     stNetlist.internals.getD 9 (fun _ _ => False), stNetlist.internals.getD 10 (fun _ _ => False), stNetlist.internals.getD 11 (fun _ _ => False),
     stNetlist.internals.getD 12 (fun _ _ => False), stNetlist.internals.getD 13 (fun _ _ => False), stNetlist.internals.getD 14 (fun _ _ => False),
     stNetlist.internals.getD 15 (fun _ _ => False), stNetlist.internals.getD 16 (fun _ _ => False), stNetlist.internals.getD 17 (fun _ _ => False),
     stNetlist.internals.getD 18 (fun _ _ => False), stNetlist.internals.getD 19 (fun _ _ => False), stNetlist.internals.getD 20 (fun _ _ => False),
     stNetlist.internals.getD 21 (fun _ _ => False), stNetlist.internals.getD 22 (fun _ _ => False), stNetlist.internals.getD 23 (fun _ _ => False),
     stNetlist.internals.getD 24 (fun _ _ => False), stNetlist.internals.getD 25 (fun _ _ => False), stNetlist.internals.getD 26 (fun _ _ => False),
     stNetlist.internals.getD 27 (fun _ _ => False)] := rfl

/-! All 28 connections, one line each. -/

theorem case_0 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f0clk

theorem case_1 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f1clk

theorem case_2 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f2clk

theorem case_3 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f3clk

theorem case_4 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f4clk

theorem case_5 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f5clk

theorem case_6 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f6clk

theorem case_7 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f0crn

theorem case_8 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f1crn

theorem case_9 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f2crn

theorem case_10 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f3crn

theorem case_11 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f4crn

theorem case_12 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f5crn

theorem case_13 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f6crn

theorem case_14 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f0d

theorem case_15 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f1d

theorem case_16 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f2d

theorem case_17 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f3d

theorem case_18 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f4d

theorem case_19 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f5d

theorem case_20 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.f6d

theorem case_21 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk0

theorem case_22 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk1

theorem case_23 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk2

theorem case_24 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk3

theorem case_25 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk4

theorem case_26 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk5

theorem case_27 (s) (i mid : stT) (H : ψ i s)
    (Hrule : (stNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by st_case W.pk6
/-! ### The specification's own rules -/

section SpecRules
variable (sp : List Bool × List (WSt 2) × List Bool × List (WSt 2))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (stSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (WSt 2)) (h : sp.2.1 ⊏ v) :
    (stSpec.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (stSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List (WSt 2)) (h1 : sp.2.2.2 <+: v)
    (h2 : v <+: stOut sp.1 sp.2.1 sp.2.2.1) :
    (stSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : stNetlist ⊑_{ψ} stSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6⟩, ⟨x6,y6,z6⟩, ud, cr, ⟨x5,y5,z5⟩, ck, ⟨x3,y3,z3⟩, ⟨x4,y4,z4⟩, ⟨x0,y0,z0⟩, ⟨x1,y1,z1⟩, ⟨x2,y2,z2⟩⟩ := i
    obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_,_,_⟩, _, _, ⟨_,_,_⟩, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, hq⟩ := H
    case_transition Hcontains : Module.inputs stNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [stNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    -- The port's identity is decided by `hpre`'s type; the three proofs are one shape.
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env (e1 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl _),
          rfl, e2, e3, hq⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix) _),
          e1, rfl, e3, hq⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl (e3 ▸ hpre.isPrefix) List.prefix_rfl _),
          e1, e2, rfl, hq⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6⟩, ⟨x6,y6,z6⟩, ud, cr, ⟨x5,y5,z5⟩, ck, ⟨x3,y3,z3⟩, ⟨x4,y4,z4⟩, ⟨x0,y0,z0⟩, ⟨x1,y1,z1⟩, ⟨x2,y2,z2⟩⟩ := i
    obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_,_,_⟩, _, _, ⟨_,_,_⟩, _, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨_,_,_⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, hq⟩ := H
    case_transition Hcontains : Module.outputs stNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [stNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    simp only [eq_mp_eq_cast, cast_self]
    dsimp only [wires] at hq
    have ho := out_q hw
    dsimp only [wires] at ho
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ hq ho, hw, e1, e2, e3, List.prefix_rfl⟩
  · intro rule mid_i Hin Hrule
    rw [stNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
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

theorem refines_initial : Module.refines_initial stNetlist stSpec ψ := by
  intro i hi
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6⟩, ⟨x6,y6,z6⟩, ud, cr, ⟨x5,y5,z5⟩, ck, ⟨x3,y3,z3⟩, ⟨x4,y4,z4⟩, ⟨x0,y0,z0⟩, ⟨x1,y1,z1⟩, ⟨x2,y2,z2⟩⟩ := i
  dsimp only [stNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  repeat' (obtain ⟨rfl, hi⟩ := hi)
  refine ⟨([], [], [], []), rfl, ?_, rfl, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The seven flip-flops refine the state register.** -/
theorem reg_refines : stNetlist ⊑ stSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.StReg
