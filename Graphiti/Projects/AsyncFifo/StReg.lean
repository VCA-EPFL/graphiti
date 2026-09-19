/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Dff
import Graphiti.Projects.AsyncFifo.Timed

/-!
# The state register from seven flip-flops

The write domain's state is a `WSt 2`: a three-bit pointer, the `full` flag, and the three bits
of the second synchroniser stage.  Seven flip-flops, then, sharing a clock and a clear, with the
record split into bits on the way in and reassembled on the way out.

This is `BusReg.lean` at another width and over a record rather than a bit vector; the proof is
the same one, generated from the same table.
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

-- HEADER_END (everything below is generated by gen/gen_busreg.py)

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

/-! ### The invariant -/

structure Wf (pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn : List Bool)
    (unp_d : List (WSt 2)) (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) : Prop where
  e_clk : clkF_in = s.1
  e_d : unp_d = s.2.1
  e_crn : crF_in = s.2.2.1
  w_pk_b0 : pk_b0 <+: dffOut ff0_clk ff0_d ff0_clrn
  w_pk_b1 : pk_b1 <+: dffOut ff1_clk ff1_d ff1_clrn
  w_pk_b2 : pk_b2 <+: dffOut ff2_clk ff2_d ff2_clrn
  w_pk_b3 : pk_b3 <+: dffOut ff3_clk ff3_d ff3_clrn
  w_pk_b4 : pk_b4 <+: dffOut ff4_clk ff4_d ff4_clrn
  w_pk_b5 : pk_b5 <+: dffOut ff5_clk ff5_d ff5_clrn
  w_pk_b6 : pk_b6 <+: dffOut ff6_clk ff6_d ff6_clrn
  w_ff6_clk : ff6_clk <+: clkF_in
  w_ff6_d : ff6_d <+: bitsOf 6 unp_d
  w_ff6_clrn : ff6_clrn <+: crF_in
  w_ff5_clk : ff5_clk <+: clkF_in
  w_ff5_d : ff5_d <+: bitsOf 5 unp_d
  w_ff5_clrn : ff5_clrn <+: crF_in
  w_ff3_clk : ff3_clk <+: clkF_in
  w_ff3_d : ff3_d <+: bitsOf 3 unp_d
  w_ff3_clrn : ff3_clrn <+: crF_in
  w_ff4_clk : ff4_clk <+: clkF_in
  w_ff4_d : ff4_d <+: bitsOf 4 unp_d
  w_ff4_clrn : ff4_clrn <+: crF_in
  w_ff0_clk : ff0_clk <+: clkF_in
  w_ff0_d : ff0_d <+: bitsOf 0 unp_d
  w_ff0_clrn : ff0_clrn <+: crF_in
  w_ff1_clk : ff1_clk <+: clkF_in
  w_ff1_d : ff1_d <+: bitsOf 1 unp_d
  w_ff1_clrn : ff1_clrn <+: crF_in
  w_ff2_clk : ff2_clk <+: clkF_in
  w_ff2_d : ff2_d <+: bitsOf 2 unp_d
  w_ff2_clrn : ff2_clrn <+: crF_in
  h_q : s.2.2.2 <+: packStOut pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6

def ψ (i : stT) (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) : Prop :=
  Wf i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2.1 i.1.2.2.2.2.1 i.1.2.2.2.2.2.1 i.1.2.2.2.2.2.2 i.2.1.1 i.2.1.2.1 i.2.1.2.2 i.2.2.2.1 i.2.2.2.2.1.1 i.2.2.2.2.1.2.1 i.2.2.2.2.1.2.2 i.2.2.2.2.2.1 i.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2 i.2.2.1 s

theorem Wf.init : Wf [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] ([], [], [], []) :=
  ⟨rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩

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

section Cases
variable {pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn : List Bool}
  {unp_d : List (WSt 2)} {sp : List Bool × List (WSt 2) × List Bool × List (WSt 2)}
  (Hψ : Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp)
include Hψ

theorem in_clk (v : List Bool) (h : clkF_in ⊏ v) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn (v) ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d (v, sp.2) := by
  have hm : clkF_in <+: v := h.isPrefix
  exact { e_clk := rfl
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk.trans hm
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk.trans hm
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk.trans hm
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk.trans hm
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk.trans hm
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk.trans hm
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk.trans hm
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem in_d (v : List (WSt 2)) (h : unp_d ⊏ v) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn (v) (sp.1, v, sp.2.2) := by
  have hm : unp_d <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := rfl
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d.trans (bitsOf_mono hm)
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d.trans (bitsOf_mono hm)
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d.trans (bitsOf_mono hm)
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d.trans (bitsOf_mono hm)
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d.trans (bitsOf_mono hm)
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d.trans (bitsOf_mono hm)
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d.trans (bitsOf_mono hm)
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem in_clrn (v : List Bool) (h : crF_in ⊏ v) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn (v) ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d (sp.1, sp.2.1, v, sp.2.2.2) := by
  have hm : crF_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := rfl
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn.trans hm
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn.trans hm
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn.trans hm
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn.trans hm
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn.trans hm
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn.trans hm
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn.trans hm
          h_q := Hψ.h_q }

theorem int_0 (_h : ff0_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn (clkF_in) ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0.trans (dffOut_mono Hψ.w_ff0_clk List.prefix_rfl List.prefix_rfl)
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := List.prefix_rfl
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_1 (_h : ff1_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn (clkF_in) ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1.trans (dffOut_mono Hψ.w_ff1_clk List.prefix_rfl List.prefix_rfl)
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := List.prefix_rfl
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_2 (_h : ff2_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn (clkF_in) ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2.trans (dffOut_mono Hψ.w_ff2_clk List.prefix_rfl List.prefix_rfl)
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := List.prefix_rfl
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_3 (_h : ff3_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in (clkF_in) ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3.trans (dffOut_mono Hψ.w_ff3_clk List.prefix_rfl List.prefix_rfl)
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := List.prefix_rfl
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_4 (_h : ff4_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn (clkF_in) ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4.trans (dffOut_mono Hψ.w_ff4_clk List.prefix_rfl List.prefix_rfl)
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := List.prefix_rfl
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_5 (_h : ff5_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in (clkF_in) ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5.trans (dffOut_mono Hψ.w_ff5_clk List.prefix_rfl List.prefix_rfl)
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := List.prefix_rfl
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_6 (_h : ff6_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 (clkF_in) ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6.trans (dffOut_mono Hψ.w_ff6_clk List.prefix_rfl List.prefix_rfl)
          w_ff6_clk := List.prefix_rfl
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_7 (_h : ff0_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d (crF_in) ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff0_clrn)
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := List.prefix_rfl
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_8 (_h : ff1_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d (crF_in) ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff1_clrn)
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := List.prefix_rfl
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_9 (_h : ff2_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d (crF_in) unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff2_clrn)
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := List.prefix_rfl
          h_q := Hψ.h_q }

theorem int_10 (_h : ff3_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d (crF_in) ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff3_clrn)
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := List.prefix_rfl
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_11 (_h : ff4_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d (crF_in) ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff4_clrn)
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := List.prefix_rfl
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_12 (_h : ff5_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d (crF_in) clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff5_clrn)
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := List.prefix_rfl
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_13 (_h : ff6_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d (crF_in) crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff6_clrn)
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := List.prefix_rfl
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_14 (_h : ff0_d ⊏ bitsOf 0 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk (bitsOf 0 unp_d) ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0.trans (dffOut_mono List.prefix_rfl Hψ.w_ff0_d List.prefix_rfl)
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := List.prefix_rfl
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_15 (_h : ff1_d ⊏ bitsOf 1 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk (bitsOf 1 unp_d) ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1.trans (dffOut_mono List.prefix_rfl Hψ.w_ff1_d List.prefix_rfl)
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := List.prefix_rfl
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_16 (_h : ff2_d ⊏ bitsOf 2 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk (bitsOf 2 unp_d) ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2.trans (dffOut_mono List.prefix_rfl Hψ.w_ff2_d List.prefix_rfl)
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := List.prefix_rfl
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_17 (_h : ff3_d ⊏ bitsOf 3 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk (bitsOf 3 unp_d) ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3.trans (dffOut_mono List.prefix_rfl Hψ.w_ff3_d List.prefix_rfl)
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := List.prefix_rfl
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_18 (_h : ff4_d ⊏ bitsOf 4 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk (bitsOf 4 unp_d) ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4.trans (dffOut_mono List.prefix_rfl Hψ.w_ff4_d List.prefix_rfl)
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := List.prefix_rfl
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_19 (_h : ff5_d ⊏ bitsOf 5 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk (bitsOf 5 unp_d) ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5.trans (dffOut_mono List.prefix_rfl Hψ.w_ff5_d List.prefix_rfl)
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := List.prefix_rfl
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_20 (_h : ff6_d ⊏ bitsOf 6 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk (bitsOf 6 unp_d) ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6.trans (dffOut_mono List.prefix_rfl Hψ.w_ff6_d List.prefix_rfl)
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := List.prefix_rfl
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_21 {out : List Bool} (_h : pk_b0 ⊏ out) (hout : out <+: dffOut ff0_clk ff0_d ff0_clrn) :
    Wf (out) pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := hout
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (packStOut_mono (_h.isPrefix) List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl) }

theorem int_22 {out : List Bool} (_h : pk_b1 ⊏ out) (hout : out <+: dffOut ff1_clk ff1_d ff1_clrn) :
    Wf pk_b0 (out) pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := hout
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (packStOut_mono List.prefix_rfl (_h.isPrefix) List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl) }

theorem int_23 {out : List Bool} (_h : pk_b2 ⊏ out) (hout : out <+: dffOut ff2_clk ff2_d ff2_clrn) :
    Wf pk_b0 pk_b1 (out) pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := hout
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (packStOut_mono List.prefix_rfl List.prefix_rfl (_h.isPrefix) List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl) }

theorem int_24 {out : List Bool} (_h : pk_b3 ⊏ out) (hout : out <+: dffOut ff3_clk ff3_d ff3_clrn) :
    Wf pk_b0 pk_b1 pk_b2 (out) pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := hout
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (packStOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl (_h.isPrefix) List.prefix_rfl List.prefix_rfl List.prefix_rfl) }

theorem int_25 {out : List Bool} (_h : pk_b4 ⊏ out) (hout : out <+: dffOut ff4_clk ff4_d ff4_clrn) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 (out) pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := hout
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (packStOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl (_h.isPrefix) List.prefix_rfl List.prefix_rfl) }

theorem int_26 {out : List Bool} (_h : pk_b5 ⊏ out) (hout : out <+: dffOut ff5_clk ff5_d ff5_clrn) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 (out) pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := hout
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (packStOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl (_h.isPrefix) List.prefix_rfl) }

theorem int_27 {out : List Bool} (_h : pk_b6 ⊏ out) (hout : out <+: dffOut ff6_clk ff6_d ff6_clrn) :
    Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 (out) ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := hout
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (packStOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl (_h.isPrefix)) }

/-- What the block reports is a prefix of the specification's stream: each bit is a prefix
of its flip-flop's output, and the flip-flops see prefixes of the block's own inputs. -/
theorem out_q : packStOut pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 <+: stOut sp.1 sp.2.1 sp.2.2.1 := by
  refine packStOut_mono ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Hψ.w_pk_b0.trans (dffOut_mono (Hψ.w_ff0_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff0_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff0_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))
  · exact Hψ.w_pk_b1.trans (dffOut_mono (Hψ.w_ff1_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff1_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff1_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))
  · exact Hψ.w_pk_b2.trans (dffOut_mono (Hψ.w_ff2_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff2_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff2_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))
  · exact Hψ.w_pk_b3.trans (dffOut_mono (Hψ.w_ff3_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff3_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff3_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))
  · exact Hψ.w_pk_b4.trans (dffOut_mono (Hψ.w_ff4_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff4_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff4_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))
  · exact Hψ.w_pk_b5.trans (dffOut_mono (Hψ.w_ff5_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff5_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff5_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))
  · exact Hψ.w_pk_b6.trans (dffOut_mono (Hψ.w_ff6_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff6_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff6_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))

/-- What it has reported it has reported: the report is the packer's, and the packer's
inputs only grow. -/
theorem out_wf : Wf pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 ff6_clk ff6_d ff6_clrn crF_in ff5_clk ff5_d ff5_clrn clkF_in ff3_clk ff3_d ff3_clrn ff4_clk ff4_d ff4_clrn ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d (sp.1, sp.2.1, sp.2.2.1, packStOut pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_pk_b3 := Hψ.w_pk_b3
          w_pk_b4 := Hψ.w_pk_b4
          w_pk_b5 := Hψ.w_pk_b5
          w_pk_b6 := Hψ.w_pk_b6
          w_ff6_clk := Hψ.w_ff6_clk
          w_ff6_d := Hψ.w_ff6_d
          w_ff6_clrn := Hψ.w_ff6_clrn
          w_ff5_clk := Hψ.w_ff5_clk
          w_ff5_d := Hψ.w_ff5_d
          w_ff5_clrn := Hψ.w_ff5_clrn
          w_ff3_clk := Hψ.w_ff3_clk
          w_ff3_d := Hψ.w_ff3_d
          w_ff3_clrn := Hψ.w_ff3_clrn
          w_ff4_clk := Hψ.w_ff4_clk
          w_ff4_d := Hψ.w_ff4_d
          w_ff4_clrn := Hψ.w_ff4_clrn
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := List.prefix_rfl }

end Cases

/-! ### The refinement -/

theorem int_case_0 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_0 Hψ ‹_›⟩

theorem int_case_1 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_1 Hψ ‹_›⟩

theorem int_case_2 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_2 Hψ ‹_›⟩

theorem int_case_3 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_3 Hψ ‹_›⟩

theorem int_case_4 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_4 Hψ ‹_›⟩

theorem int_case_5 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_5 Hψ ‹_›⟩

theorem int_case_6 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_6 Hψ ‹_›⟩

theorem int_case_7 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_7 Hψ ‹_›⟩

theorem int_case_8 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_8 Hψ ‹_›⟩

theorem int_case_9 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_9 Hψ ‹_›⟩

theorem int_case_10 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_10 Hψ ‹_›⟩

theorem int_case_11 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_11 Hψ ‹_›⟩

theorem int_case_12 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_12 Hψ ‹_›⟩

theorem int_case_13 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_13 Hψ ‹_›⟩

theorem int_case_14 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_14 Hψ ‹_›⟩

theorem int_case_15 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_15 Hψ ‹_›⟩

theorem int_case_16 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_16 Hψ ‹_›⟩

theorem int_case_17 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_17 Hψ ‹_›⟩

theorem int_case_18 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_18 Hψ ‹_›⟩

theorem int_case_19 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_19 Hψ ‹_›⟩

theorem int_case_20 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_20 Hψ ‹_›⟩

theorem int_case_21 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_21 Hψ ‹_› ‹_›⟩

theorem int_case_22 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_22 Hψ ‹_› ‹_›⟩

theorem int_case_23 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_23 Hψ ‹_› ‹_›⟩

theorem int_case_24 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_24 Hψ ‹_› ‹_›⟩

theorem int_case_25 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_25 Hψ ‹_› ‹_›⟩

theorem int_case_26 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_26 Hψ ‹_› ‹_›⟩

theorem int_case_27 (s : List Bool × List (WSt 2) × List Bool × List (WSt 2)) (i mid : stT) (Hψ : ψ i s)
    (Hrule : (stNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR stSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2, c_pk_b3, c_pk_b4, c_pk_b5, c_pk_b6⟩, ⟨c_ff6_clk, c_ff6_d, c_ff6_clrn⟩, c_unp_d, c_crF_in, ⟨c_ff5_clk, c_ff5_d, c_ff5_clrn⟩, c_clkF_in, ⟨c_ff3_clk, c_ff3_d, c_ff3_clrn⟩, ⟨c_ff4_clk, c_ff4_d, c_ff4_clrn⟩, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_27 Hψ ‹_› ‹_›⟩

theorem stNetlist_internals_eq : stNetlist.internals = [stNetlist.internals.getD 0 (fun _ _ => False), stNetlist.internals.getD 1 (fun _ _ => False), stNetlist.internals.getD 2 (fun _ _ => False), stNetlist.internals.getD 3 (fun _ _ => False), stNetlist.internals.getD 4 (fun _ _ => False), stNetlist.internals.getD 5 (fun _ _ => False), stNetlist.internals.getD 6 (fun _ _ => False), stNetlist.internals.getD 7 (fun _ _ => False), stNetlist.internals.getD 8 (fun _ _ => False), stNetlist.internals.getD 9 (fun _ _ => False), stNetlist.internals.getD 10 (fun _ _ => False), stNetlist.internals.getD 11 (fun _ _ => False), stNetlist.internals.getD 12 (fun _ _ => False), stNetlist.internals.getD 13 (fun _ _ => False), stNetlist.internals.getD 14 (fun _ _ => False), stNetlist.internals.getD 15 (fun _ _ => False), stNetlist.internals.getD 16 (fun _ _ => False), stNetlist.internals.getD 17 (fun _ _ => False), stNetlist.internals.getD 18 (fun _ _ => False), stNetlist.internals.getD 19 (fun _ _ => False), stNetlist.internals.getD 20 (fun _ _ => False), stNetlist.internals.getD 21 (fun _ _ => False), stNetlist.internals.getD 22 (fun _ _ => False), stNetlist.internals.getD 23 (fun _ _ => False), stNetlist.internals.getD 24 (fun _ _ => False), stNetlist.internals.getD 25 (fun _ _ => False), stNetlist.internals.getD 26 (fun _ _ => False), stNetlist.internals.getD 27 (fun _ _ => False)] := rfl

theorem refines_ψ : stNetlist ⊑_{ψ} stSpec := by
  intro i s Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs stNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [stNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← Hψ.e_clk]; assumption), existSR_reflexive, in_clk Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← Hψ.e_d]; assumption), existSR_reflexive, in_d Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← Hψ.e_crn]; assumption), existSR_reflexive, in_clrn Hψ _ ‹_›⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2, m_pk_b3, m_pk_b4, m_pk_b5, m_pk_b6⟩, ⟨m_ff6_clk, m_ff6_d, m_ff6_clrn⟩, m_unp_d, m_crF_in, ⟨m_ff5_clk, m_ff5_d, m_ff5_clrn⟩, m_clkF_in, ⟨m_ff3_clk, m_ff3_d, m_ff3_clrn⟩, ⟨m_ff4_clk, m_ff4_d, m_ff4_clrn⟩, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs stNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [stNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ Hψ.h_q (out_q Hψ), out_wf Hψ⟩
  · intro rule mid_i Hin Hrule
    rw [stNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact int_case_0 s i mid_i Hψ Hrule
    · subst h; exact int_case_1 s i mid_i Hψ Hrule
    · subst h; exact int_case_2 s i mid_i Hψ Hrule
    · subst h; exact int_case_3 s i mid_i Hψ Hrule
    · subst h; exact int_case_4 s i mid_i Hψ Hrule
    · subst h; exact int_case_5 s i mid_i Hψ Hrule
    · subst h; exact int_case_6 s i mid_i Hψ Hrule
    · subst h; exact int_case_7 s i mid_i Hψ Hrule
    · subst h; exact int_case_8 s i mid_i Hψ Hrule
    · subst h; exact int_case_9 s i mid_i Hψ Hrule
    · subst h; exact int_case_10 s i mid_i Hψ Hrule
    · subst h; exact int_case_11 s i mid_i Hψ Hrule
    · subst h; exact int_case_12 s i mid_i Hψ Hrule
    · subst h; exact int_case_13 s i mid_i Hψ Hrule
    · subst h; exact int_case_14 s i mid_i Hψ Hrule
    · subst h; exact int_case_15 s i mid_i Hψ Hrule
    · subst h; exact int_case_16 s i mid_i Hψ Hrule
    · subst h; exact int_case_17 s i mid_i Hψ Hrule
    · subst h; exact int_case_18 s i mid_i Hψ Hrule
    · subst h; exact int_case_19 s i mid_i Hψ Hrule
    · subst h; exact int_case_20 s i mid_i Hψ Hrule
    · subst h; exact int_case_21 s i mid_i Hψ Hrule
    · subst h; exact int_case_22 s i mid_i Hψ Hrule
    · subst h; exact int_case_23 s i mid_i Hψ Hrule
    · subst h; exact int_case_24 s i mid_i Hψ Hrule
    · subst h; exact int_case_25 s i mid_i Hψ Hrule
    · subst h; exact int_case_26 s i mid_i Hψ Hrule
    · subst h; exact int_case_27 s i mid_i Hψ Hrule

theorem refines_initial : Module.refines_initial stNetlist stSpec ψ := by
  intro i hi
  obtain ⟨⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6⟩, ⟨ff6_clk, ff6_d, ff6_clrn⟩, unp_d, crF_in, ⟨ff5_clk, ff5_d, ff5_clrn⟩, clkF_in, ⟨ff3_clk, ff3_d, ff3_clrn⟩, ⟨ff4_clk, ff4_d, ff4_clrn⟩, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  dsimp only [stNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨([], [], [], []), rfl, Wf.init⟩

/-- **The 7 flip-flops refine a seven-bit state register.** -/
theorem reg_refines : stNetlist ⊑ stSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.StReg
