/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gates
import Graphiti.Projects.AsyncFifo.components.level3.Dff

/-! # `Dff`: the lemmas

Facts about the definitions in `components/level3/Dff.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.Dff
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates

section NetlistAsModule

/-! ### The circuit reduced to a single module, for the proofs -/

@[drenv] theorem denv_fork2 : denv.find? "fork2" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem denv_fork3 : denv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem denv_fork5 : denv.find? "fork5" = .some ⟨_, fork5⟩ := rfl
@[drenv] theorem denv_and2 : denv.find? "and2" = .some ⟨_, gate2 and2⟩ := rfl
@[drenv] theorem denv_cut3 : denv.find? "cut3" = .some ⟨_, cut3⟩ := rfl
@[drenv] theorem denv_nand2 : denv.find? "nand2" = .some ⟨_, gate2 nand2⟩ := rfl
@[drenv] theorem denv_nand3 : denv.find? "nand3" = .some ⟨_, gate3 nand3⟩ := rfl

seal denv in
def_module dffT : Type :=
  [T| dffLowered, denv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal denv in
def_module dffNetlist : StringModule dffT :=
  [e| dffLowered, denv.find? ]

seal denv in
/-- The `def_module` above is the `[e| … ]` circuit `components/` names, reduced. -/
theorem dffNetlist_sigma :
    (⟨_, dffNetlist⟩ : Σ T, StringModule T) = ExprLow.build_module denv.find? dffLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [Batteries.AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

end NetlistAsModule


instance : Inhabited DffSt := ⟨⟨false, false, false, false, false, false⟩⟩

theorem dffRun_congr {clk clk' d d' crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d')
    (hr : crn <+: crn') {t : Nat} (ht : t ≤ dffLen clk d crn) :
    dffRun clk d crn t = dffRun clk' d' crn' t := by
  refine run_congr _ _ (fun u hu => ?_) t ht
  unfold dffLen at hu
  unfold dffInp
  rw [hc.getD_eq_left (by omega), hd.getD_eq_left (by omega), hr.getD_eq_left (by omega)]

@[simp] theorem dffOut_length (clk d crn : List Bool) :
    (dffOut clk d crn).length = dffLen clk d crn + 1 := timeline_length _ _

theorem dffOut_getD (clk d crn : List Bool) {t : Nat} (ht : t < dffLen clk d crn + 1) :
    (dffOut clk d crn).getD t false = qAt clk d crn t := timeline_getD _ ht _

theorem dffOut_mono {clk clk' d d' crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d')
    (hr : crn <+: crn') : dffOut clk d crn <+: dffOut clk' d' crn' := by
  have := hc.length_le; have := hd.length_le; have := hr.length_le
  apply timeline_mono (by unfold dffLen; omega)
  intro t ht
  match t with
  | 0 => rfl
  | u + 1 =>
    simp only [dffLen] at ht
    show and2 _ _ = and2 _ _
    rw [dffRun_congr hc hd hr (by unfold dffLen; omega), hr.getD_eq_left (by omega)]

instance : MatchInterface dffNetlist dffSpec := by
  dsimp [dffNetlist, dffSpec]
  solve_match_interface
end Graphiti.AsyncFifo.Dff