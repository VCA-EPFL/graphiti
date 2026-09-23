/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteDomainGates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadDomainGates
import Graphiti.Projects.AsyncFifo.TopGates

/-! # The FIFO as gates: the substitution at the top

`asyncFifoGates` is `asyncFifoImpl`'s graph with the two clock domains' specifications replaced
by their gates.  Given that each domain's gates refine its specification, the whole refines the
implementation. -/

namespace Graphiti.AsyncFifo

open Batteries (AssocList)

section Fifo

variable {lat stl Rc rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat}

theorem fifoGateEnv_wdom : (fifoGateEnv lat stl Rc).find? "wdom" = .some ⟨_, wdomGates lat stl Rc⟩ := rfl
theorem fifoGateEnv_rdom : (fifoGateEnv lat stl Rc).find? "rdom" = .some ⟨_, rdomGates lat stl Rc⟩ := rfl

theorem fifoGateEnv_find_ne (t : String) (h : t ≠ "wdom") (h' : t ≠ "rdom") :
    (fifoGateEnv lat stl Rc).find? t =
      (envF Bool 2 lat stl 8 4 rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? t := by
  by_cases ho : t = "oracle_w"
  · subst ho; rfl
  by_cases hr : t = "oracle_r"
  · subst hr; rfl
  have h1 : ("wdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  have h2 : ("rdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h')
  have h3 : ("oracle_w" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm ho)
  have h4 : ("oracle_r" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm hr)
  simp [fifoGateEnv, envF, asyncFifoGraph, AssocList.find?, h1, h2, h3, h4]

theorem wf_fifoGateEnv : ExprLow.wf (fifoGateEnv lat stl Rc).find? asyncFifoLowered := by rfl

/-- **Substitution.**  If each clock domain's gates refine the domain's specification, the FIFO
as gates refines the FIFO's implementation. -/
theorem asyncFifoGates_refines_impl
    (hw : wdomGates lat stl Rc ⊑ wdomSpec Bool 2 lat stl 8 4 P_w S_w R_w pw_w)
    (hr : rdomGates lat stl Rc ⊑ rdomSpec Bool 2 lat stl 8 4 rdly P_r S_r R_r pw_r) :
    asyncFifoGates lat stl Rc ⊑
      asyncFifoImpl Bool 2 lat stl 8 4 rdly P_w P_r S_w S_r R_w R_r pw_w pw_r := by
  apply ExprLow.refines_env _ wf_fifoGateEnv wf_envF
  intro i t
  by_cases ht : t = "wdom"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ fifoGateEnv_wdom
      (envF_wdom Bool 2 lat stl 8 4 rdly P_w P_r S_w S_r R_w R_r pw_w pw_r) hw
  by_cases hr' : t = "rdom"
  · subst hr'
    exact ExprLow.refines_base_of_refines i _ fifoGateEnv_rdom
      (envF_rdom Bool 2 lat stl 8 4 rdly P_w P_r S_w S_r R_w R_r pw_w pw_r) hr
  · exact ExprLow.refines_base_of_eq i t (fifoGateEnv_find_ne t ht hr')

end Fifo

end Graphiti.AsyncFifo
