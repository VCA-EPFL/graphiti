/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadNext
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadBankContract
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadPortContract
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.StorageGates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncStageContract
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteDomainGates
import Graphiti.Projects.AsyncFifo.TopGates

/-! # The read domain as gates: the refinement proof -/

namespace Graphiti.AsyncFifo

open Batteries (AssocList)
open Contracts Timed

section Domain

variable {lat stl Rc : Nat}

theorem rdomGateEnv_next : (rdomGateEnv lat stl Rc).find? "ReadNext" = .some ⟨_, ReadNext.nextImpl⟩ := rfl
theorem rdomGateEnv_bank :
    (rdomGateEnv lat stl Rc).find? "ReadBank" = .some ⟨_, ReadBank.gates⟩ := rfl
theorem rdomGateEnv_rdat : (rdomGateEnv lat stl Rc).find? "ReadPort" = .some ⟨_, ReadPort.readImpl⟩ := rfl
theorem rdomGateEnv_sync :
    (rdomGateEnv lat stl Rc).find? "SyncStage" = .some ⟨_, SyncStage.syncImpl lat 8 stl⟩ := rfl

theorem rdomGateEnv_find_ne (t : String) (h : t ≠ "ReadNext") (h' : t ≠ "ReadBank")
    (h'' : t ≠ "ReadPort") (hsy : t ≠ "SyncStage") :
    (rdomGateEnv lat stl Rc).find? t = (renv Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc).find? t := by
  by_cases hk : t = "clkF"
  · subst hk; rfl
  by_cases hc : t = "clearSrc"
  · subst hc; rfl
  by_cases hs : t = "stF"
  · subst hs; rfl
  have h1 : ("ReadNext" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  have h2 : ("ReadBank" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h')
  have h3 : ("ReadPort" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h'')
  have h4 : ("SyncStage" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm hsy)
  have h5 : ("clkF" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm hk)
  have h6 : ("clearSrc" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm hc)
  have h7 : ("stF" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm hs)
  simp [rdomGateEnv, renv, rdomGraph, AssocList.find?, h1, h2, h3, h4, h5, h6, h7]

theorem wf_rdomGateEnv : ExprLow.wf (rdomGateEnv lat stl Rc).find? rdomLowered := by rfl
theorem wf_renv : ExprLow.wf (renv Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc).find? rdomLowered := by rfl

seal renv in
/-- The reduced timed read domain is the expression-level one. -/
theorem rdomTimed_sigma {α : Type} [Inhabited α] {n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc : Nat} :
    (⟨rdomTimedT α n, rdomTimed α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc⟩ : Σ T, StringModule T) =
      ExprLow.build_module (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? rdomLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

/-- The implementation of the read domain is its reduced form. -/
theorem rdomImpl_refines_timed {α : Type} [Inhabited α]
    {n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc : Nat} :
    rdomImpl α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc ⊑
      rdomTimed α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc :=
  Module.refines_eq' rdomTimed_sigma.symm

/-- **Substitution.**  The read domain as gates refines its implementation. -/
theorem rdomGates_refines_impl (hR6 : 6 ≤ Rc) :
    rdomGates lat stl Rc ⊑ rdomImpl Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc := by
  apply ExprLow.refines_env _ wf_rdomGateEnv wf_renv
  intro i t
  by_cases ht : t = "ReadNext"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ rdomGateEnv_next
      (renv_next Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc) ReadNext.nextImpl_refines
  by_cases hb : t = "ReadBank"
  · subst hb
    exact ExprLow.refines_base_of_refines i _ rdomGateEnv_bank
      (renv_regs Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc)
      (Module.refines_transitive _ ReadBank.gates_refines_exact (ReadBankContract.bankSpec_refines hR6))
  by_cases hd : t = "ReadPort"
  · subst hd
    exact ExprLow.refines_base_of_refines i _ rdomGateEnv_rdat
      (renv_rdat Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc) ReadPortContract.readImpl_refines
  by_cases hs : t = "SyncStage"
  · subst hs
    exact ExprLow.refines_base_of_refines i _ rdomGateEnv_sync
      (renv_sync Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc) (SyncStageContract.syncImpl_refines lat 8 stl)
  · exact ExprLow.refines_base_of_eq i t (rdomGateEnv_find_ne t ht hb hd hs)
end Domain

end Graphiti.AsyncFifo
