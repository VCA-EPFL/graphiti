/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Dff
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncOutMono
import Graphiti.Projects.AsyncFifo.components.level4.WriteState

/-! # `WriteState`: the lemmas

Facts about the definitions in `components/level4/WriteState.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.WriteState
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Dff

@[drenv] theorem senv_unpackSt : senv.find? "unpackSt" = .some ⟨_, unpackSt⟩ := rfl
@[drenv] theorem senv_fork7 : senv.find? "fork7" = .some ⟨_, fork7⟩ := rfl
@[drenv] theorem senv_dff : senv.find? "dff" = .some ⟨_, dffSpec⟩ := rfl
@[drenv] theorem senv_packSt : senv.find? "packSt" = .some ⟨_, packSt⟩ := rfl


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

theorem stOut_mono {clk clk' : List Bool} {d d' : List (WSt 2)}
    {crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d') (hr : crn <+: crn') :
    stOut clk d crn <+: stOut clk' d' crn' :=
  packStOut_mono (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr)

instance : MatchInterface stNetlist stSpec := by
  dsimp [stNetlist, stSpec]
  solve_match_interface
end Graphiti.AsyncFifo.WriteState