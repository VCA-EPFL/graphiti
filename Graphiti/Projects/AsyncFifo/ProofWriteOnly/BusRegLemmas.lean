/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Dff
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.components.level4.BusReg

/-! # `BusReg`: the lemmas

Facts about the definitions in `components/level4/BusReg.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.BusReg
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Dff

@[drenv] theorem benv_unpack3 : benv.find? "unpack3" = .some ⟨_, unpack3⟩ := rfl
@[drenv] theorem benv_fork3 : benv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem benv_dff : benv.find? "dff" = .some ⟨_, dffSpec⟩ := rfl
@[drenv] theorem benv_pack3 : benv.find? "pack3" = .some ⟨_, pack3⟩ := rfl


@[simp] theorem bitsOf_length (i : Nat) (d : List (BitVec 3)) : (bitsOf i d).length = d.length := by
  simp [bitsOf]

theorem bitsOf_mono {i : Nat} {d d' : List (BitVec 3)} (h : d <+: d') : bitsOf i d <+: bitsOf i d' :=
  h.map _

theorem bitsOf_getD {i : Nat} {d : List (BitVec 3)} {t : Nat} (ht : t < d.length) :
    (bitsOf i d).getD t false = (d.getD t 0#3).getLsbD i := by
  simp [bitsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht]

@[simp] theorem pack3Out_length (b0 b1 b2 : List Bool) :
    (pack3Out b0 b1 b2).length = min (min b0.length b1.length) b2.length := timeline_length _ _

theorem pack3Out_getD {b0 b1 b2 : List Bool} {t : Nat}
    (ht : t < min (min b0.length b1.length) b2.length) :
    (pack3Out b0 b1 b2).getD t 0#3 =
      bv3 (b0.getD t false) (b1.getD t false) (b2.getD t false) := timeline_getD _ ht _

theorem pack3Out_mono {b0 b0' b1 b1' b2 b2' : List Bool} (h0 : b0 <+: b0') (h1 : b1 <+: b1')
    (h2 : b2 <+: b2') : pack3Out b0 b1 b2 <+: pack3Out b0' b1' b2' := by
  have := h0.length_le; have := h1.length_le; have := h2.length_le
  apply timeline_mono (by omega)
  intro t ht
  simp only [Nat.lt_min] at ht
  rw [h0.getD_eq_left (by omega), h1.getD_eq_left (by omega), h2.getD_eq_left (by omega)]

seal benv in
def_module busT : Type :=
  [T| busLowered, benv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal benv in
def_module busNetlist : StringModule busT :=
  [e| busLowered, benv.find? ]

theorem busOut_mono {clk clk' : List Bool} {d d' : List (BitVec 3)}
    {crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d') (hr : crn <+: crn') :
    busOut clk d crn <+: busOut clk' d' crn' :=
  pack3Out_mono (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr)

instance : MatchInterface busNetlist busSpec := by
  dsimp [busNetlist, busSpec]
  solve_match_interface
end Graphiti.AsyncFifo.BusReg