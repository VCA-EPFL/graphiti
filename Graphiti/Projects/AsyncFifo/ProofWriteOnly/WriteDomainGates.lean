/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteNext
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteBankContract
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.StorageGates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncStageContract
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Lifting
import Graphiti.Projects.AsyncFifo.TopGates

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

open Batteries (AssocList)
open Contracts Timed

section Domain

variable {lat stl P S R pw Rc : Nat}

theorem wdomGateEnv_next : (wdomGateEnv lat stl Rc).find? "WriteNext" = .some ⟨_, WriteNext.nextImpl⟩ := rfl
theorem wdomGateEnv_bank :
    (wdomGateEnv lat stl Rc).find? "WriteBank" = .some ⟨_, WriteBank.gates⟩ := rfl
theorem wdomGateEnv_sync :
    (wdomGateEnv lat stl Rc).find? "SyncStage" = .some ⟨_, SyncStage.syncImpl lat 8 stl⟩ := rfl

theorem wdomGateEnv_find_ne (t : String) (h : t ≠ "WriteNext") (h' : t ≠ "WriteBank")
    (h'' : t ≠ "SyncStage") :
    (wdomGateEnv lat stl Rc).find? t = (wenv Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc).find? t := by
  by_cases hk : t = "clkF"
  · subst hk; rfl
  by_cases hc : t = "clearSrc"
  · subst hc; rfl
  have h1 : ("WriteNext" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  have h2 : ("WriteBank" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h')
  have h3 : ("SyncStage" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h'')
  have h4 : ("clkF" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm hk)
  have h5 : ("clearSrc" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm hc)
  simp [wdomGateEnv, wenv, wdomGraph, AssocList.find?, h1, h2, h3, h4, h5]

theorem wf_wdomGateEnv : ExprLow.wf (wdomGateEnv lat stl Rc).find? wdomLowered := by rfl
theorem wf_wenv : ExprLow.wf (wenv Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc).find? wdomLowered := by rfl

seal wenv in
/-- The reduced timed write domain is the expression-level one. -/
theorem wdomTimed_sigma {α : Type} [Inhabited α] {n lat kq su stl dmin dmax P pw Rr Rc : Nat} :
    (⟨wdomTimedT α n, wdomTimed α n lat kq su stl dmin dmax P pw Rr Rc⟩ : Σ T, StringModule T) =
      ExprLow.build_module (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? wdomLowered := by
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

/-- The implementation of the write domain is its reduced form. -/
theorem wdomImpl_refines_timed {α : Type} [Inhabited α] {n lat kq su stl dmin dmax P pw Rr Rc : Nat} :
    wdomImpl α n lat kq su stl dmin dmax P pw Rr Rc ⊑ wdomTimed α n lat kq su stl dmin dmax P pw Rr Rc :=
  Module.refines_eq' wdomTimed_sigma.symm

/-- **Substitution.**  The write domain as gates refines its implementation: each block's gates
refine the block's specification, which is what the implementation names. -/
theorem wdomGates_refines_impl (hR6 : 6 ≤ Rc) :
    wdomGates lat stl Rc ⊑ wdomImpl Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc := by
  apply ExprLow.refines_env _ wf_wdomGateEnv wf_wenv
  intro i t
  by_cases ht : t = "WriteNext"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ wdomGateEnv_next
      (wenv_next Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc) WriteNext.nextImpl_refines
  by_cases hb : t = "WriteBank"
  · subst hb
    exact ExprLow.refines_base_of_refines i _ wdomGateEnv_bank
      (wenv_regs Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc)
      (Module.refines_transitive _ WriteBank.gates_refines_exact (WriteBankContract.bankSpec_refines hR6))
  by_cases hs : t = "SyncStage"
  · subst hs
    exact ExprLow.refines_base_of_refines i _ wdomGateEnv_sync
      (wenv_sync Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc) (SyncStageContract.syncImpl_refines lat 8 stl)
  · exact ExprLow.refines_base_of_eq i t (wdomGateEnv_find_ne t ht hb hs)

end Domain

end Graphiti.AsyncFifo
