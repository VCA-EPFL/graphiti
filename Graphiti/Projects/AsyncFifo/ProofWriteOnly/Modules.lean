/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Filtered
import Graphiti.Projects.AsyncFifo.TopSpec
import Graphiti.Projects.AsyncFifo.components.level8.Fifo
import Graphiti.Projects.AsyncFifo.components.level3.Oracle
import Graphiti.Projects.AsyncFifo.components.level7.WriteDomain
import Graphiti.Projects.AsyncFifo.components.level7.ReadDomain

namespace Graphiti.AsyncFifo

section Circuit

variable (α : Type) [Inhabited α] (n lat stl su : Nat)

/-! ### The FIFO's graph over the two domains' specifications, reduced -/

variable (kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat)

@[drenv] theorem envF_wdom : (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? "wdom" =
  .some ⟨_, wdomSpec α n lat stl su kq P_w S_w R_w pw_w⟩ := rfl
@[drenv] theorem envF_rdom : (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? "rdom" =
  .some ⟨_, rdomSpec α n lat stl su kq rdly P_r S_r R_r pw_r⟩ := rfl
@[drenv] theorem envF_orcw : (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? "oracle_w" = .some ⟨_, oracle n⟩ := rfl
@[drenv] theorem envF_orcr : (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? "oracle_r" = .some ⟨_, oracle n⟩ := rfl

abbrev asyncFifoFT : Type := Unit × RStateF α n × WStateF α n × Unit

seal envF in
def_module asyncFifoFT' : Type :=
  [T| asyncFifoLowered, (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

/-- A compiled check, not a step of any proof: the type `def_module` reduces the graph to
is the one written by hand above, so the hand-written `abbrev` — which every statement below
names — cannot drift from the graph. -/
theorem asyncFifoFT_eq : asyncFifoFT' α n = asyncFifoFT α n := rfl

seal envF in
def_module asyncFifoF : StringModule (asyncFifoFT α n) :=
  [e| asyncFifoLowered, (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? ]

end Circuit

end Graphiti.AsyncFifo
