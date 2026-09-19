/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.GateNextR
import Graphiti.Projects.AsyncFifo.GateBankR
import Graphiti.Projects.AsyncFifo.GateRead
import Graphiti.Projects.AsyncFifo.GateRegs
import Graphiti.Projects.AsyncFifo.GateSync
import Graphiti.Projects.AsyncFifo.GateLifting

/-!
# Plugging the read domain's gate netlists into the FIFO

`GateLifting.lean` for the read domain: the timed read domain `rdomTimed` is the graph
`rdomTimedLowered` read in the environment `renv`; `rdomGates` reads the same graph with the
next-state block implemented by `GateNextR.gateNextR` and the register bank by
`BankR.bankNetlist`.  Componentwise refinement lifts the two block theorems to the domain
(`rdomGates_refines_timed`), and `asyncFifoTimedR_refines` then carries it to the FIFO.

One block of the read domain stays at the timed level: the synchroniser's first stage, because
`Metastability.lean` shows the netlist does not refine it.  Everything else --- the next-state
logic, the whole state, and the read port --- is gates.  The read port's delay window is `[3, 5]`
(`GateRead.mux_refines_rdataBlock`), which is what the read clock must accommodate on top of its
clk-to-q.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

open Batteries (AssocList)
open Timed

/-! ### The read domain with the gate netlists -/

/-- The environment of the timed read domain with its stateful part and its next-state logic as
netlists.  The graph (`rdomTimedLowered`) is unchanged; only what the two nodes stand for.  The
bank fixes the windows it meets, `kq = 4` and `su = 8`. -/
def renvG (lat stl Rc : Nat) : AssocList String (TModule1 String) :=
  AssocList.cons "rdataBlock" ⟨_, ReadMux.muxNetlist⟩
    (AssocList.cons "rregBank" ⟨_, GateRegs.bankRNetlistG⟩
      (AssocList.cons "rnextBlock" ⟨_, GateNextR.gateNextR⟩
        (AssocList.cons "syncReg" ⟨_, SyncStage.stageNetlist lat 8 stl⟩
          (renv Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc))))

/-- **The read domain as gates**: its next-state logic, its whole state and its read port. -/
def rdomGates (lat stl Rc : Nat) := [e| rdomTimedLowered, (renvG lat stl Rc).find? ]

section Domain

variable {lat stl Rc : Nat}

theorem renvG_next : (renvG lat stl Rc).find? "rnextBlock" = .some ⟨_, GateNextR.gateNextR⟩ := rfl
theorem renvG_bank :
    (renvG lat stl Rc).find? "rregBank" = .some ⟨_, GateRegs.bankRNetlistG⟩ := rfl
theorem renvG_rdat : (renvG lat stl Rc).find? "rdataBlock" = .some ⟨_, ReadMux.muxNetlist⟩ := rfl
theorem renvG_sync :
    (renvG lat stl Rc).find? "syncReg" = .some ⟨_, SyncStage.stageNetlist lat 8 stl⟩ := rfl

theorem renvG_find_ne (t : String) (h : t ≠ "rnextBlock") (h' : t ≠ "rregBank")
    (h'' : t ≠ "rdataBlock") (hsy : t ≠ "syncReg") :
    (renvG lat stl Rc).find? t = (renv Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc).find? t := by
  have h1 : ("rnextBlock" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  have h2 : ("rregBank" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h')
  have h3 : ("rdataBlock" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h'')
  have h4 : ("syncReg" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm hsy)
  simp [renvG, AssocList.find?, h1, h2, h3, h4]

theorem wf_renvG : ExprLow.wf (renvG lat stl Rc).find? rdomTimedLowered := by rfl
theorem wf_renv : ExprLow.wf (renv Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc).find? rdomTimedLowered := by rfl

seal renv in
/-- The reduced timed read domain is the expression-level one. -/
theorem rdomTimed_sigma :
    (⟨rdomTimedT Bool 2, rdomTimed Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc⟩ : Σ T, StringModule T) =
      ExprLow.build_module (renv Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc).find? rdomTimedLowered := by
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

/-- The gate-level read domain refines the timed one. -/
theorem rdomGates_refines_timed (hR6 : 6 ≤ Rc) :
    rdomGates lat stl Rc ⊑ rdomTimed Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc := by
  refine Module.refines_transitive _ ?_ (Module.refines_eq' rdomTimed_sigma.symm)
  apply ExprLow.refines_env _ wf_renvG wf_renv
  intro i t
  by_cases ht : t = "rnextBlock"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ renvG_next
      (renv_next Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc) GateNextR.gateNextR_refines
  by_cases hb : t = "rregBank"
  · subst hb
    exact ExprLow.refines_base_of_refines i _ renvG_bank
      (renv_regs Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc)
      (Module.refines_transitive _ GateRegs.bankRG_refines (GateBankR.bankSpec_refines hR6))
  by_cases hd : t = "rdataBlock"
  · subst hd
    exact ExprLow.refines_base_of_refines i _ renvG_rdat
      (renv_rdat Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc) GateRead.mux_refines_rdataBlock
  by_cases hs : t = "syncReg"
  · subst hs
    exact ExprLow.refines_base_of_refines i _ renvG_sync
      (renv_sync Bool 2 lat 4 8 stl 0 8 3 5 12 3 (Rc + 3) Rc) (GateSync.stage_refines lat 8 stl)
  · exact ExprLow.refines_base_of_eq i t (renvG_find_ne t ht hb hd hs)

end Domain

/-! ### The FIFO with both domains as gates -/

/-- The FIFO environment with both clock domains as netlists.  The graph (`asyncFifoLowered`)
is the one every stage of this development shares; only what `wdom` and `rdom` stand for
changes. -/
def envGG (lat stl Rc : Nat) : AssocList String (TModule1 String) :=
  AssocList.cons "wdom" ⟨_, wdomGates lat stl Rc⟩
    (AssocList.cons "rdom" ⟨_, rdomGates lat stl Rc⟩
      (envTR Bool 2 lat stl 8 4 0 8 12 3 (Rc + 3) Rc 0 8 3 5 5 12 3 (Rc + 3) Rc))

/-- **The asynchronous FIFO with both clock domains as gates** (depth `4`, 1-bit data). -/
def asyncFifoGatesRW (lat stl Rc : Nat) :=
  [e| asyncFifoLowered, (envGG lat stl Rc).find? ]

section Fifo

variable {lat stl P_w P_r S_w S_r R_w R_r pw_w pw_r Rc : Nat}

theorem envGG_wdom : (envGG lat stl Rc).find? "wdom" = .some ⟨_, wdomGates lat stl Rc⟩ := rfl
theorem envGG_rdom : (envGG lat stl Rc).find? "rdom" = .some ⟨_, rdomGates lat stl Rc⟩ := rfl

theorem envGG_find_ne (t : String) (h : t ≠ "wdom") (h' : t ≠ "rdom") :
    (envGG lat stl Rc).find? t =
      (envTR Bool 2 lat stl 8 4 0 8 12 3 (Rc + 3) Rc 0 8 3 5 5 12 3 (Rc + 3) Rc).find? t := by
  have h1 : ("wdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  have h2 : ("rdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h')
  simp [envGG, AssocList.find?, h1, h2]

theorem wf_envGG : ExprLow.wf (envGG lat stl Rc).find? asyncFifoLowered := by rfl

/-- The FIFO with both domains as gates refines the FIFO with both domains timed. -/
theorem asyncFifoGatesRW_refines_timedR (hR6 : 6 ≤ Rc) :
    asyncFifoGatesRW lat stl Rc ⊑
      asyncFifoTimedR Bool 2 lat stl 8 4 0 8 12 3 (Rc + 3) Rc 0 8 3 5 5 12 3 (Rc + 3) Rc := by
  apply ExprLow.refines_env _ wf_envGG wf_envTR
  intro i t
  by_cases ht : t = "wdom"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ envGG_wdom envTR_wdom (wdomGates_refines_timed hR6)
  by_cases hr : t = "rdom"
  · subst hr
    exact ExprLow.refines_base_of_refines i _ envGG_rdom envTR_rdom (rdomGates_refines_timed hR6)
  · exact ExprLow.refines_base_of_eq i t (envGG_find_ne t ht hr)

/-- **Main theorem.**  The asynchronous FIFO whose two clock domains are netlists of unit-delay
gates --- every register, the register file, both next-state logics --- refines the FIFO
specification, under the timing assumptions of the two clocks.

The numbers are the netlists': a clk-to-q of `4`, a setup of `8` (the register file's five plus
its decoder's three), a next-state delay window of `[0, 8]`, a clear released by `Rc`, a reset
of `Rc + 3`, a minimum high time of `3` and an internal period budget of `12`.  The read port's own combinational
window is `[3, 5]`, which the read clock accommodates on top of its clk-to-q. -/
theorem asyncFifoGatesRW_refines (hR6 : 6 ≤ Rc)
    (hP1 : 22 ≤ P_w) (hP2 : stl + 18 ≤ P_w) (hS : 17 ≤ S_w) (hR : 17 ≤ R_w) (hRg : Rc + 3 ≤ R_w)
    (hpw : 3 ≤ pw_w)
    (rP1 : 22 ≤ P_r) (rP2 : stl + 18 ≤ P_r) (rS : 17 ≤ S_r) (rR : 17 ≤ R_r) (rRg : Rc + 3 ≤ R_r)
    (rpw : 3 ≤ pw_r) :
    asyncFifoGatesRW lat stl Rc ⊑ fifoSpec Bool P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_transitive _ (asyncFifoGatesRW_refines_timedR hR6)
    (asyncFifoTimedR_refines (by lia) (by lia) (by lia) (Nat.zero_le _) (by lia) (by lia) (by lia) hRg
      (by lia) (by lia) (by lia) (Nat.zero_le _) (by lia) (by lia) (by lia) rRg (by lia)
      (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) (by lia))

end Fifo

end Graphiti.AsyncFifo
