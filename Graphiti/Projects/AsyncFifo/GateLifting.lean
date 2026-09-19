/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.GateNext
import Graphiti.Projects.AsyncFifo.GateBank
import Graphiti.Projects.AsyncFifo.GateRegs
import Graphiti.Projects.AsyncFifo.GateSync
import Graphiti.Projects.AsyncFifo.Lifting

/-!
# Plugging the gate netlist into the FIFO

The timed write domain `wdomTimed` is the graph `wdomTimedLowered` read in the environment
`wenv`; `wdomGates` reads the same graph with the next-state block implemented by the gate
netlist of `GateNext.lean`.  Componentwise refinement lifts `gateNext_refines` to the domain
(`wdomGates_refines`), then the domain into the FIFO (`asyncFifoGates_refines`).

Here the FIFO has depth `4` and 1-bit data; the delay window of the netlist is `[0, 8]`, so
the write clock period must satisfy `kq + su + 10 ≤ P_w` and `stl + su + 10 ≤ P_w`, the write
inputs must be stable `su + 9` instants before an edge, and the first write edge must come
after instant `su + 9`.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

open Batteries (AssocList)
open Timed

/-! ### The write domain with the gate netlist -/

/-- The environment of the timed write domain with both stateful and combinational parts as
netlists: the next-state block is `GateNext.gateNext` and the register bank is
`Bank.bankNetlist`.  The graph itself (`wdomTimedLowered`) is unchanged; only what the
two nodes stand for.  The bank fixes the windows it meets, `kq = 4` and `su = 8` --- the
flip-flop's clock-to-q, and the register file's setup (the cell's five plus the decoder's
three). -/
def wenvG (lat stl Rc : Nat) : AssocList String (TModule1 String) :=
  AssocList.cons "regBank" ⟨_, GateRegs.bankNetlistG⟩
    (AssocList.cons "nextBlock" ⟨_, GateNext.gateNext⟩
      (AssocList.cons "syncReg" ⟨_, SyncStage.stageNetlist lat 8 stl⟩
        (wenv Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc)))

/-- **The write domain as gates**: its next-state logic and its whole state. -/
def wdomGates (lat stl Rc : Nat) := [e| wdomTimedLowered, (wenvG lat stl Rc).find? ]

section Domain

variable {lat stl P S R pw Rc : Nat}

theorem wenvG_next : (wenvG lat stl Rc).find? "nextBlock" = .some ⟨_, GateNext.gateNext⟩ := rfl
theorem wenvG_bank :
    (wenvG lat stl Rc).find? "regBank" = .some ⟨_, GateRegs.bankNetlistG⟩ := rfl
theorem wenvG_sync :
    (wenvG lat stl Rc).find? "syncReg" = .some ⟨_, SyncStage.stageNetlist lat 8 stl⟩ := rfl

theorem wenvG_find_ne (t : String) (h : t ≠ "nextBlock") (h' : t ≠ "regBank")
    (h'' : t ≠ "syncReg") :
    (wenvG lat stl Rc).find? t = (wenv Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc).find? t := by
  have h1 : ("nextBlock" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  have h2 : ("regBank" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h')
  have h3 : ("syncReg" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h'')
  simp [wenvG, AssocList.find?, h1, h2, h3]

theorem wf_wenvG : ExprLow.wf (wenvG lat stl Rc).find? wdomTimedLowered := by rfl
theorem wf_wenv : ExprLow.wf (wenv Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc).find? wdomTimedLowered := by rfl

seal wenv in
/-- The reduced timed write domain is the expression-level one. -/
theorem wdomTimed_sigma :
    (⟨wdomTimedT Bool 2, wdomTimed Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc⟩ : Σ T, StringModule T) =
      ExprLow.build_module (wenv Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc).find? wdomTimedLowered := by
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

/-- The gate-level write domain refines the timed one. -/
theorem wdomGates_refines_timed (hR6 : 6 ≤ Rc) :
    wdomGates lat stl Rc ⊑ wdomTimed Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc := by
  refine Module.refines_transitive _ ?_ (Module.refines_eq' wdomTimed_sigma.symm)
  apply ExprLow.refines_env _ wf_wenvG wf_wenv
  intro i t
  by_cases ht : t = "nextBlock"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ wenvG_next
      (wenv_next Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc) GateNext.gateNext_refines
  by_cases hb : t = "regBank"
  · subst hb
    exact ExprLow.refines_base_of_refines i _ wenvG_bank
      (wenv_regs Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc)
      (Module.refines_transitive _ GateRegs.bankG_refines (GateBank.bankSpec_refines hR6))
  by_cases hs : t = "syncReg"
  · subst hs
    exact ExprLow.refines_base_of_refines i _ wenvG_sync
      (wenv_sync Bool 2 lat 4 8 stl 0 8 12 3 (Rc + 3) Rc) (GateSync.stage_refines lat 8 stl)
  · exact ExprLow.refines_base_of_eq i t (wenvG_find_ne t ht hb hs)

/-- The gate-level write domain refines the filtered write domain. -/
theorem wdomGates_refines (hR6 : 6 ≤ Rc) (hP1 : 22 ≤ P) (hP2 : stl + 18 ≤ P) (hS : 17 ≤ S)
    (hR : 17 ≤ R) (hPg : 12 ≤ P) (hpwg : 3 ≤ pw) (hRg : Rc + 3 ≤ R) :
    wdomGates lat stl Rc ⊑ writeDomainF Bool 2 lat stl 8 4 P S R pw :=
  Module.refines_transitive _ (wdomGates_refines_timed hR6)
    (wdomTimed_refines (by lia) (by lia) (by lia) (Nat.zero_le _) (by lia) hPg hpwg hRg)

end Domain

/-! ### The FIFO with the gate-level write domain -/

/-- The FIFO environment with the gate-level write domain. -/
def envG (lat stl P_r S_r R_r pw_r Rc : Nat) : AssocList String (TModule1 String) :=
  AssocList.cons "wdom" ⟨_, wdomGates lat stl Rc⟩ (envT Bool 2 lat stl 8 4 0 P_r S_r R_r pw_r 0 8 12 3 (Rc + 3) Rc)

/-- **The asynchronous FIFO whose write domain's next-state logic is gates** (depth `4`,
1-bit data), read domain at the filtered level. -/
def asyncFifoGates (lat stl P_r S_r R_r pw_r Rc : Nat) := [e| asyncFifoLowered, (envG lat stl P_r S_r R_r pw_r Rc).find? ]

section Fifo

variable {lat stl P_w P_r S_w S_r R_w R_r pw_w pw_r Rc : Nat}

theorem envG_wdom : (envG lat stl P_r S_r R_r pw_r Rc).find? "wdom" = .some ⟨_, wdomGates lat stl Rc⟩ := rfl

theorem envG_find_ne (t : String) (h : t ≠ "wdom") :
    (envG lat stl P_r S_r R_r pw_r Rc).find? t = (envT Bool 2 lat stl 8 4 0 P_r S_r R_r pw_r 0 8 12 3 (Rc + 3) Rc).find? t := by
  have h1 : ("wdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [envG, AssocList.find?, h1]

theorem wf_envG : ExprLow.wf (envG lat stl P_r S_r R_r pw_r Rc).find? asyncFifoLowered := by rfl

/-- The gate-level FIFO refines the FIFO with the timed write domain. -/
theorem asyncFifoGates_refines_timed (hR6 : 6 ≤ Rc) :
    asyncFifoGates lat stl P_r S_r R_r pw_r Rc ⊑ asyncFifoTimed Bool 2 lat stl 8 4 0 P_r S_r R_r pw_r 0 8 12 3 (Rc + 3) Rc := by
  apply ExprLow.refines_env _ wf_envG wf_envT
  intro i t
  by_cases ht : t = "wdom"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ envG_wdom envT_wdom (wdomGates_refines_timed hR6)
  · exact ExprLow.refines_base_of_eq i t (envG_find_ne t ht)

/-- **Main theorem.**  The FIFO whose write domain's next-state logic is a netlist of unit-delay
gates refines the FIFO specification, under the timing assumptions of the write clock
(period, input setup, reset) and the crossing constraints of both clocks. -/
theorem asyncFifoGates_refines (hR6 : 6 ≤ Rc) (hP1 : 22 ≤ P_w) (hP2 : stl + 18 ≤ P_w)
    (hS : 17 ≤ S_w) (hR : 17 ≤ R_w) (hPg : 12 ≤ P_w) (hpwg : 3 ≤ pw_w) (hRg : Rc + 3 ≤ R_w)
    (hkr : 12 < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r) :
    asyncFifoGates lat stl P_r S_r R_r pw_r Rc ⊑ fifoSpec Bool P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_transitive _ (asyncFifoGates_refines_timed hR6)
    (asyncFifoTimed_refines (by lia) (by lia) (by lia) (Nat.zero_le _) (by lia) hPg hpwg hRg
      (by lia) (by lia) hstlw hstlr (by lia) (by lia) (by lia))

end Fifo

end Graphiti.AsyncFifo
