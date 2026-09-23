/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.FifoGates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.TimedRefinement
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.TimedRefinementR
import Graphiti.Projects.AsyncFifo.TopSpec

/-!
# The theorem

`TopSpec.lean` says what an asynchronous FIFO is; `TopGates.lean` builds one out of gates.  This
file states that the second refines the first, `asyncFifoGates_refines`, and how that follows.

1. **Every component meets its specification** (`X.impl_refines`).  A component's
   implementation is a graph over the *specifications* of the components one level down, so
   each theorem is about one component alone, and a component can be reused through its
   specification.
2. **Substitution** (`wdomGates_refines`, `rdomGates_refines`).  Replacing a node by anything
   that refines it preserves refinement (`ExprLow.refines_env`).  So a component whose children
   are replaced by their gates still refines its specification --- bottom up, until only gates
   remain.
3. **The main theorem** is the top layer, `asyncFifoImpl_refines`, with the two clock domains'
   gates substituted in.

The last `example` is the guard that the theorem is not vacuous: one assignment satisfying all
thirteen hypotheses.  `Evidence/Example.lean` is the other half of that concern --- a run where a
clock *is* too fast and the FIFO does misbehave, so the filters are not idle either.
-/

namespace Graphiti.AsyncFifo

open Contracts Timed

/-! ## 1. Every component meets its specification

Bottom-up, one theorem per component of `components/`.  An implementation built from particular
gates has particular delays, so those theorems fix the parameters the gates realise: a two-bit
address (`n = 2`), one-bit data, a clock-to-q of `4`, a setup of `8` (the register file's five
plus its decoder's three), a next-state window of `[0, 8]` and a read-port window of `[3, 5]`. -/

section Layers

/-- The flip-flop: six NAND gates behave as an edge-triggered register with a clear. -/
theorem Dff.impl_refines : Dff.dffImpl ⊑ Dff.dffSpec := Dff.dffImpl_refines

/-- The three-bit register: three flip-flops. -/
theorem BusReg.impl_refines : BusReg.busImpl ⊑ BusReg.busSpec :=
  Module.refines_transitive _ (Module.refines_eq' BusReg.netlist_sigma.symm) BusReg.reg_refines

/-- The memory cell: a flip-flop behind an enable. -/
theorem EnReg.impl_refines : EnReg.enImpl ⊑ EnReg.enSpec :=
  Module.refines_transitive _ (Module.refines_eq' EnReg.netlist_sigma.symm) EnReg.en_refines

/-- The write domain's state register: seven flip-flops. -/
theorem WriteState.impl_refines : WriteState.stImpl ⊑ WriteState.stSpec :=
  Module.refines_transitive _ (Module.refines_eq' WriteState.netlist_sigma.symm) WriteState.reg_refines

/-- The read domain's state register: seven flip-flops. -/
theorem ReadState.impl_refines : ReadState.stImpl ⊑ ReadState.stSpec :=
  Module.refines_transitive _ (Module.refines_eq' ReadState.netlist_sigma.symm) ReadState.reg_refines

/-- The register file: four memory cells and an address decoder. -/
theorem RegFile.impl_refines : RegFile.memImpl ⊑ RegFile.memSpec :=
  Module.refines_transitive _ (Module.refines_eq' RegFile.netlist_sigma.symm) RegFile.mem_refines

/-- The write domain's register bank --- state register, Gray pointer, register file --- meets
its timed contract. -/
theorem WriteBank.impl_refines {Rc : Nat} (hR : 6 ≤ Rc) :
    WriteBank.bankImpl ⊑ WriteBank.bankSpec Bool (n := 2) 4 8 12 3 (Rc + 3) Rc :=
  Module.refines_transitive _ (Module.refines_eq' WriteBank.netlist_sigma.symm)
    (WriteBankContract.netlist_refines hR)

/-- The read domain's register bank --- state register and Gray pointer --- meets its timed
contract. -/
theorem ReadBank.impl_refines {Rc : Nat} (hR : 6 ≤ Rc) :
    ReadBank.bankImpl ⊑ ReadBank.bankSpec (n := 2) 4 8 12 3 (Rc + 3) Rc :=
  Module.refines_transitive _ (Module.refines_eq' ReadBank.netlist_sigma.symm)
    (ReadBankContract.netlist_refines hR)

/-- The write domain's next-state logic, as gates, within the delay window `[0, 8]`. -/
theorem WriteNext.impl_refines : WriteNext.nextImpl ⊑ WriteNext.nextSpec Bool (n := 2) 0 8 :=
  WriteNext.nextImpl_refines

/-- The read domain's next-state logic, as gates, within the delay window `[0, 8]`. -/
theorem ReadNext.impl_refines : ReadNext.nextImpl ⊑ ReadNext.nextSpec (n := 2) 0 8 :=
  ReadNext.nextImpl_refines

/-- The read port, a multiplexer of gates, within the delay window `[3, 5]`. -/
theorem ReadPort.impl_refines : ReadPort.readImpl ⊑ ReadPort.readSpec Bool (n := 2) 3 5 :=
  ReadPortContract.readImpl_refines

/-- The synchroniser's first stage: three flip-flops, each of which may go metastable
(`settlingDffO`, the one leaf that is assumed rather than built from gates). -/
theorem SyncStage.impl_refines (lat su stl : Nat) :
    SyncStage.syncImpl lat su stl ⊑ SyncStage.syncSpec (n := 2) lat su stl :=
  SyncStageContract.syncImpl_refines lat su stl

/-- **The write domain** --- its bank, next-state logic and synchroniser, each standing for its
specification --- meets the write domain's specification, when the domain's clock period leaves
room for the blocks' windows and the bank's own clock and reset budgets are within the domain's. -/
theorem wdomImpl_refines {α : Type} [Inhabited α] {n lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc : Nat}
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) :
    wdomImpl α n lat kq su stl dmin dmax Pg pwg Rg Rc ⊑ wdomSpec α n lat stl su kq P S R pw :=
  Module.refines_transitive _ wdomImpl_refines_timed
    (wdomTimed_refines hP1 hP2 hS hdd hR hPg hpwg hRg)

/-- **The read domain** --- its bank, next-state logic, synchroniser and read port --- meets the
read domain's specification; additionally the read port's window must fit in `rdly`. -/
theorem rdomImpl_refines {α : Type} [Inhabited α]
    {n lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc : Nat}
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (hkq : 0 < kq) (hrr : ddmin ≤ ddmax)
    (hrw : ddmax ≤ rdly) (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) :
    rdomImpl α n lat kq su stl dmin dmax ddmin ddmax Pg pwg Rg Rc ⊑
      rdomSpec α n lat stl su kq rdly P S R pw :=
  Module.refines_transitive _ rdomImpl_refines_timed
    (rdomTimed_refines hP1 hP2 hS hdd hR hkq hrr hrw hPg hpwg hRg)

/-- **The top layer.**  The FIFO's implementation --- its two clock domains, each standing for its
specification, and the two oracles --- refines the FIFO specification, whenever each clock's
period leaves room for its clock-to-q and setup, the synchroniser settles within a period, and
the read data is ready in time. -/
theorem asyncFifoImpl_refines {α : Type} [Inhabited α]
    {n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat}
    (hkw : kq + su < P_w) (hkr : kq + su < P_r)
    (hstlw : stl < P_w) (hstlr : stl < P_r) (hkrd : kq + rdly < P_r)
    (hrd : kq + rdly ≤ P_r + lat + 1) (hrdR : rdly ≤ R_r) :
    asyncFifoImpl α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r ⊑
      fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_transitive _ (asyncFifoF_expr_refines α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r)
    (refinesF hkw hkr hstlw hstlr hkrd hrd hrdR)

end Layers

/-! ## 2. Substitution

`X.gates` (`TopGates.lean`) is `X`'s implementation with every specification in it replaced by
gates.  It refines `X`'s implementation --- each replaced node refines what it replaces --- and so
`X`'s specification.  The storage blocks' versions (`WriteBank.gates_refines_exact`, ...) are in
`ProofWriteOnly/StorageGates.lean`; the two clock domains' are these. -/

section Gates

variable {lat stl P S R pw Rc : Nat}

/-- The write domain as gates meets the write domain's specification. -/
theorem wdomGates_refines (hR6 : 6 ≤ Rc) (hP1 : 22 ≤ P) (hP2 : stl + 18 ≤ P) (hS : 17 ≤ S)
    (hR : 17 ≤ R) (hRg : Rc + 3 ≤ R) (hpw : 3 ≤ pw) :
    wdomGates lat stl Rc ⊑ wdomSpec Bool 2 lat stl 8 4 P S R pw :=
  Module.refines_transitive _ (wdomGates_refines_impl hR6)
    (wdomImpl_refines (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) hpw hRg)

/-- The read domain as gates meets the read domain's specification, with the read port's
`rdly = 5`. -/
theorem rdomGates_refines (hR6 : 6 ≤ Rc) (hP1 : 22 ≤ P) (hP2 : stl + 18 ≤ P) (hS : 17 ≤ S)
    (hR : 17 ≤ R) (hRg : Rc + 3 ≤ R) (hpw : 3 ≤ pw) :
    rdomGates lat stl Rc ⊑ rdomSpec Bool 2 lat stl 8 4 5 P S R pw :=
  Module.refines_transitive _ (rdomGates_refines_impl hR6)
    (rdomImpl_refines (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) (by lia)
      (by lia) hpw hRg)

end Gates

/-! ## 3. The main theorem -/

section Fifo

variable {lat stl P_w P_r S_w S_r R_w R_r pw_w pw_r Rc : Nat}

/-- **Main theorem.**  The asynchronous FIFO whose two clock domains are netlists of unit-delay
gates --- every register, the register file, both next-state logics, the read port --- refines
the FIFO specification, under the timing assumptions of the two clocks.

The numbers are the netlists': a clk-to-q of `4`, a setup of `8` (the register file's five plus
its decoder's three), a next-state delay window of `[0, 8]`, a clear released by `Rc`, a reset
of `Rc + 3`, a minimum high time of `3` and an internal period budget of `12`.  The read port's
own combinational window is `[3, 5]`, which the read clock accommodates on top of its clk-to-q. -/
theorem asyncFifoGates_refines (hR6 : 6 ≤ Rc)
    (hP1 : 22 ≤ P_w) (hP2 : stl + 18 ≤ P_w) (hS : 17 ≤ S_w) (hR : 17 ≤ R_w) (hRg : Rc + 3 ≤ R_w)
    (hpw : 3 ≤ pw_w)
    (rP1 : 22 ≤ P_r) (rP2 : stl + 18 ≤ P_r) (rS : 17 ≤ S_r) (rR : 17 ≤ R_r) (rRg : Rc + 3 ≤ R_r)
    (rpw : 3 ≤ pw_r) :
    asyncFifoGates lat stl Rc ⊑ fifoSpec Bool P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_transitive _
    (asyncFifoGates_refines_impl (wdomGates_refines hR6 hP1 hP2 hS hR hRg hpw)
      (rdomGates_refines hR6 rP1 rP2 rS rR rRg rpw))
    (asyncFifoImpl_refines (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) (by lia))

/-- **The main theorem is not vacuous.**  It carries thirteen hypotheses about the two clocks,
and a refinement whose hypotheses cannot all hold at once proves nothing at all; this is one
assignment that satisfies them --- the clear released at `6`, both clocks of period `30`, a
settling time of `1` --- so there is a circuit and a pair of clocks the theorem actually speaks
about.  `Example.lean` is the other half of the same concern: it exhibits a run where the read
clock *is* too fast and the FIFO does misbehave, so the filters are not idle either. -/
example : asyncFifoGates 0 1 6 ⊑ fifoSpec Bool 30 30 17 17 17 17 3 3 :=
  asyncFifoGates_refines (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

end Fifo

end Graphiti.AsyncFifo
