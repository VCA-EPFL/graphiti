/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.DomainsRefine
import Graphiti.Projects.AsyncFifo.Refinement
import Graphiti.Projects.AsyncFifo.TimedRefinementR

/-!
# Plugging refined blocks into the FIFO

All three circuits — register-level (`env`), filtered (`envF`) and with the timed write
domain (`envT`) — are the same lowered graph `asyncFifoLowered` read in different
environments.  `ExprLow.refines_env` lifts componentwise refinements to the whole graph,
which gives the two end-to-end theorems:

* `asyncFifoTimed_refines`: the FIFO whose write domain is built from timed blocks refines
  `fifoSpec`, under the delay constraints of `TimedRefinement.lean` on the write clock and the
  crossing constraints of `Invariant.lean` on both clocks;
* `asyncFifo_refines`: the register-level FIFO refines `fifoSpec` (the special case `kq = 0`),
  recovering the earlier direct proof.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

open Batteries (AssocList)

/-! ### Refinement of a lowered expression across environments -/

/-- If every base component refines its counterpart in the other environment, so does the whole
expression. -/
theorem ExprLow.refines_env {Ident Typ : Type} [DecidableEq Ident] {ε₁ ε₂ : Env Ident Typ} :
    ∀ (e : ExprLow Ident Typ), ExprLow.wf ε₁ e → ExprLow.wf ε₂ e →
      (∀ (i : PortMapping Ident) (t : Typ), [e| .base i t, ε₁ ] ⊑ [e| .base i t, ε₂ ]) →
      [e| e, ε₁ ] ⊑ [e| e, ε₂ ]
  | .base i t, _, _, hb => hb i t
  | .product a b, hwf₁, hwf₂, hb =>
    have ⟨h1, h2⟩ := ExprLow.wf_product.mp hwf₁
    have ⟨h3, h4⟩ := ExprLow.wf_product.mp hwf₂
    ExprLow.refines_product h1 h2 h3 h4 (ExprLow.refines_env a h1 h3 hb) (ExprLow.refines_env b h2 h4 hb)
  | .connect c e, hwf₁, hwf₂, hb =>
    ExprLow.refines_connect (ExprLow.wf_connect.mp hwf₁) (ExprLow.wf_connect.mp hwf₂)
      (ExprLow.refines_env e (ExprLow.wf_connect.mp hwf₁) (ExprLow.wf_connect.mp hwf₂) hb)

/-- Two environments agreeing on a type give equal base modules. -/
theorem ExprLow.refines_base_of_eq {Ident Typ : Type} [DecidableEq Ident] {ε₁ ε₂ : Env Ident Typ}
    (i : PortMapping Ident) (t : Typ) (h : ε₁ t = ε₂ t) : [e| .base i t, ε₁ ] ⊑ [e| .base i t, ε₂ ] := by
  apply Module.refines_eq'
  simp only [ExprLow.build_module, ExprLow.build_module', h]

/-- A base component whose implementations refine each other. -/
theorem ExprLow.refines_base_of_refines {Ident Typ : Type} [DecidableEq Ident] {ε₁ ε₂ : Env Ident Typ}
    (i : PortMapping Ident) (t : Typ) {T₁ T₂ : Type} {m₁ : Module Ident T₁} {m₂ : Module Ident T₂}
    (h₁ : ε₁ t = some ⟨T₁, m₁⟩) (h₂ : ε₂ t = some ⟨T₂, m₂⟩) (h : m₁ ⊑ m₂) :
    [e| .base i t, ε₁ ] ⊑ [e| .base i t, ε₂ ] := by
  have e₁ : ExprLow.build_module ε₁ (.base i t) = ⟨T₁, m₁.renamePorts i⟩ := by
    unfold ExprLow.build_module ExprLow.build_module'; rw [h₁]; rfl
  have e₂ : ExprLow.build_module ε₂ (.base i t) = ⟨T₂, m₂.renamePorts i⟩ := by
    unfold ExprLow.build_module ExprLow.build_module'; rw [h₂]; rfl
  show (ExprLow.build_module ε₁ (.base i t)).2 ⊑ (ExprLow.build_module ε₂ (.base i t)).2
  rw [e₁, e₂]
  exact Module.refines_renamePorts h

section Circuit

variable (α : Type) [Inhabited α] (n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat)

/-! ### The reduced filtered circuit is the expression-level one -/

seal envF in
theorem asyncFifoF_sigma :
    (⟨asyncFifoFT α n, asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r⟩ : Σ T, StringModule T) =
      ExprLow.build_module (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? asyncFifoLowered := by
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

theorem asyncFifoF_expr_refines :
    [e| asyncFifoLowered, (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? ] ⊑ asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_eq' (asyncFifoF_sigma α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).symm

end Circuit

/-! ### The circuit with the timed write domain -/

def asyncFifoGraphT (α : Type) [Inhabited α] (n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc : Nat) := [graphEnv|
    wclk [type="io"];
    winc [type="io"];
    wdata [type="io"];
    rclk [type="io"];
    rinc [type="io"];
    full [type="io"];
    empty [type="io"];
    rdata [type="io"];

    wdom [type="wdom", typeImp=$(⟨_, Timed.wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc⟩)];
    rdom [type="rdom", typeImp=$(⟨_, readDomainF α n lat stl su kq rdly P_r S_r R_r pw_r⟩)];
    orcw [type="oracle_w", typeImp=$(⟨_, oracle n⟩)];
    orcr [type="oracle_r", typeImp=$(⟨_, oracle n⟩)];

    wclk -> wdom [to="clk"];
    winc -> wdom [to="inc"];
    wdata -> wdom [to="data"];
    rclk -> rdom [to="clk"];
    rinc -> rdom [to="inc"];

    wdom -> rdom [from="gray", to="wgray"];
    rdom -> wdom [from="gray", to="rgray"];
    wdom -> rdom [from="mem", to="mem"];
    orcw -> wdom [from="bits", to="orc"];
    orcr -> rdom [from="bits", to="orc"];

    wdom -> full [from="full"];
    rdom -> empty [from="empty"];
    rdom -> rdata [from="rdata"];
  ]

theorem asyncFifoGraphT_lower :
    (asyncFifoGraphT Unit 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0).1.lower_TR = (asyncFifoGraph Unit 0 0 0 0).1.lower_TR := rfl

def envT (α : Type) [Inhabited α] (n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc : Nat) :=
  (asyncFifoGraphT α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc).2

section Timed

variable {α : Type} [Inhabited α] {n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r dmin dmax Pg pwg Rg Rc : Nat}

@[drenv] theorem envT_wdom : (envT α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc).find? "wdom" =
  .some ⟨_, Timed.wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc⟩ := rfl
@[drenv] theorem envT_rdom : (envT α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc).find? "rdom" =
  .some ⟨_, readDomainF α n lat stl su kq rdly P_r S_r R_r pw_r⟩ := rfl

end Timed

/-- **The asynchronous FIFO with the timed write domain plugged in**: the same graph as
`asyncFifoGraph`, read in the environment `envT`. -/
def asyncFifoTimed (α : Type) [Inhabited α] (n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc : Nat) :=
  [e| asyncFifoLowered, (envT α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc).find? ]

section Timed

variable {α : Type} [Inhabited α] {n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r dmin dmax Pg pwg Rg Rc : Nat}

theorem envT_find_ne (t : String) (h : t ≠ "wdom") :
    (envT α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc).find? t = (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? t := by
  unfold envT envF asyncFifoGraphT asyncFifoGraphF
  have h1 : ("wdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  rcases Bool.eq_false_or_eq_true ("oracle_w" == t) with hw | hw <;>
    rcases Bool.eq_false_or_eq_true ("rdom" == t) with hr | hr <;>
    rcases Bool.eq_false_or_eq_true ("oracle_r" == t) with ho | ho <;>
    simp [List.toAssocList, h1, hw, hr, ho]

theorem env_find_ne (t : String) (h₁ : t ≠ "wdom") (h₂ : t ≠ "rdom") :
    (env α n lat stl su).find? t = (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? t := by
  unfold env envF asyncFifoGraph asyncFifoGraphF
  have h1 : ("wdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h₁)
  have h2 : ("rdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h₂)
  rcases Bool.eq_false_or_eq_true ("oracle_w" == t) with hw | hw <;>
    rcases Bool.eq_false_or_eq_true ("oracle_r" == t) with ho | ho <;>
    simp [List.toAssocList, h1, h2, hw, ho]

theorem wf_envF : ExprLow.wf (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? asyncFifoLowered := by rfl
theorem wf_envT : ExprLow.wf (envT α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc).find? asyncFifoLowered := by rfl
theorem wf_env : ExprLow.wf (env α n lat stl su).find? asyncFifoLowered := by rfl

/-- The timed circuit refines the filtered circuit. -/
theorem asyncFifoTimed_refines_F (hP1 : kq + su + dmax + 2 ≤ P_w) (hP2 : stl + su + dmax + 2 ≤ P_w)
    (hS : su + dmax + 1 ≤ S_w) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R_w)
    (hPg : Pg ≤ P_w) (hpwg : pwg ≤ pw_w) (hRg : Rg ≤ R_w) :
    asyncFifoTimed α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc ⊑
      [e| asyncFifoLowered, (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? ] := by
  apply ExprLow.refines_env _ wf_envT wf_envF
  intro i t
  by_cases ht : t = "wdom"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ envT_wdom (envF_wdom α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r)
      (Timed.wdomTimed_refines hP1 hP2 hS hdd hR hPg hpwg hRg)
  · exact ExprLow.refines_base_of_eq i t (envT_find_ne t ht)

/-- **Main theorem.**  The asynchronous FIFO whose write domain is built from timed blocks
refines the FIFO specification, provided the write clock period accommodates a clk-to-q window,
the next-state delay and a setup window (`kq + su + dmax + 2 ≤ P_w`), likewise the
synchroniser settling time (`stl + su + dmax + 2 ≤ P_w`), the write inputs are stable for
`su + dmax + 1` instants before each edge, and both clocks satisfy the crossing constraints
(`kq + su < P`, `stl < P`). -/
theorem asyncFifoTimed_refines (hP1 : kq + su + dmax + 2 ≤ P_w) (hP2 : stl + su + dmax + 2 ≤ P_w)
    (hS : su + dmax + 1 ≤ S_w) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R_w)
    (hPg : Pg ≤ P_w) (hpwg : pwg ≤ pw_w) (hRg : Rg ≤ R_w)
    (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
    (hkrd : kq + rdly < P_r) (hrd : kq + rdly ≤ P_r + lat + 1) (hrdR : rdly ≤ R_r) :
    asyncFifoTimed α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc ⊑ fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_transitive _ (asyncFifoTimed_refines_F hP1 hP2 hS hdd hR hPg hpwg hRg)
    (Module.refines_transitive _ (asyncFifoF_expr_refines α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r)
      (refinesF hkw hkr hstlw hstlr hkrd hrd hrdR))

/-! ### The circuit with both domains timed -/

/-- The same graph again, with the read domain timed as well.  The filtered read domain's
parameters disappear here: a timed domain does not take them. -/
def asyncFifoGraphTR (α : Type) [Inhabited α]
    (n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc : Nat) := [graphEnv|
    wclk [type="io"];
    winc [type="io"];
    wdata [type="io"];
    rclk [type="io"];
    rinc [type="io"];
    full [type="io"];
    empty [type="io"];
    rdata [type="io"];

    wdom [type="wdom", typeImp=$(⟨_, Timed.wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc⟩)];
    rdom [type="rdom", typeImp=$(⟨_, Timed.rdomTimed α n lat kq su stl rdmin rdmax rpmin rpmax rPg rpwg rRg rRc⟩)];
    orcw [type="oracle_w", typeImp=$(⟨_, oracle n⟩)];
    orcr [type="oracle_r", typeImp=$(⟨_, oracle n⟩)];

    wclk -> wdom [to="clk"];
    winc -> wdom [to="inc"];
    wdata -> wdom [to="data"];
    rclk -> rdom [to="clk"];
    rinc -> rdom [to="inc"];

    wdom -> rdom [from="gray", to="wgray"];
    rdom -> wdom [from="gray", to="rgray"];
    wdom -> rdom [from="mem", to="mem"];
    orcw -> wdom [from="bits", to="orc"];
    orcr -> rdom [from="bits", to="orc"];

    wdom -> full [from="full"];
    rdom -> empty [from="empty"];
    rdom -> rdata [from="rdata"];
  ]


def envTR (α : Type) [Inhabited α]
    (n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc : Nat) :=
  (asyncFifoGraphTR α n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc).2

/-- **The asynchronous FIFO with both domains timed.** -/
def asyncFifoTimedR (α : Type) [Inhabited α]
    (n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc : Nat) :=
  [e| asyncFifoLowered,
      (envTR α n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc).find? ]

section TimedR

variable {α : Type} [Inhabited α]
  {n lat stl su kq P_w P_r S_w S_r R_w R_r pw_w pw_r dmin dmax Pg pwg Rg Rc
   rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc : Nat}

@[drenv] theorem envTR_rdom :
    (envTR α n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc).find? "rdom" =
      .some ⟨_, Timed.rdomTimed α n lat kq su stl rdmin rdmax rpmin rpmax rPg rpwg rRg rRc⟩ := rfl

@[drenv] theorem envTR_wdom :
    (envTR α n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc).find? "wdom" =
      .some ⟨_, Timed.wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc⟩ := rfl

theorem envTR_find_ne (t : String) (h : t ≠ "rdom") :
    (envTR α n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc).find? t =
      (envT α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc).find? t := by
  unfold envTR envT asyncFifoGraphTR asyncFifoGraphT
  have h1 : ("rdom" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  rcases Bool.eq_false_or_eq_true ("wdom" == t) with hw | hw <;>
    rcases Bool.eq_false_or_eq_true ("oracle_w" == t) with ho | ho <;>
    rcases Bool.eq_false_or_eq_true ("oracle_r" == t) with hr | hr <;>
    simp [List.toAssocList, h1, hw, ho, hr]

theorem wf_envTR : ExprLow.wf
    (envTR α n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc).find?
    asyncFifoLowered := by rfl

/-- The circuit with both domains timed refines the one with only the write domain timed. -/
theorem asyncFifoTimedR_refines_T (hP1 : kq + su + rdmax + 2 ≤ P_r) (hP2 : stl + su + rdmax + 2 ≤ P_r)
    (hS : su + rdmax + 1 ≤ S_r) (hdd : rdmin ≤ rdmax) (hR : rdmax + su + 1 ≤ R_r) (hkq : 0 < kq)
    (hrr : rpmin ≤ rpmax) (hrw : rpmax ≤ rdly)
    (hPg : rPg ≤ P_r) (hpwg : rpwg ≤ pw_r) (hRg : rRg ≤ R_r) :
    asyncFifoTimedR α n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc ⊑
      asyncFifoTimed α n lat stl su kq rdly P_r S_r R_r pw_r dmin dmax Pg pwg Rg Rc := by
  apply ExprLow.refines_env _ wf_envTR wf_envT
  intro i t
  by_cases ht : t = "rdom"
  · subst ht
    exact ExprLow.refines_base_of_refines i _ envTR_rdom envT_rdom
      (Timed.rdomTimed_refines hP1 hP2 hS hdd hR hkq hrr hrw hPg hpwg hRg)
  · exact ExprLow.refines_base_of_eq i t (envTR_find_ne t ht)

/-- **Both domains timed, refining the FIFO specification.** -/
theorem asyncFifoTimedR_refines
    (hP1 : kq + su + dmax + 2 ≤ P_w) (hP2 : stl + su + dmax + 2 ≤ P_w) (hS : su + dmax + 1 ≤ S_w)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R_w) (hPg : Pg ≤ P_w) (hpwg : pwg ≤ pw_w)
    (hRg : Rg ≤ R_w)
    (rP1 : kq + su + rdmax + 2 ≤ P_r) (rP2 : stl + su + rdmax + 2 ≤ P_r) (rS : su + rdmax + 1 ≤ S_r)
    (rdd : rdmin ≤ rdmax) (rR : rdmax + su + 1 ≤ R_r) (rPg' : rPg ≤ P_r) (rpwg' : rpwg ≤ pw_r)
    (rRg' : rRg ≤ R_r) (hkq : 0 < kq) (hrr : rpmin ≤ rpmax) (hrw : rpmax ≤ rdly)
    (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
    (hkrd : kq + rdly < P_r) (hrd : kq + rdly ≤ P_r + lat + 1) (hrdR : rdly ≤ R_r) :
    asyncFifoTimedR α n lat stl su kq dmin dmax Pg pwg Rg Rc rdmin rdmax rpmin rpmax rdly rPg rpwg rRg rRc ⊑
      fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_transitive _
    (asyncFifoTimedR_refines_T (P_r := P_r) (S_r := S_r) (R_r := R_r) (pw_r := pw_r)
      rP1 rP2 rS rdd rR hkq hrr hrw rPg' rpwg' rRg')
    (asyncFifoTimed_refines hP1 hP2 hS hdd hR hPg hpwg hRg hkw hkr hstlw hstlr hkrd hrd hrdR)

end TimedR

/-! ### The register-level circuit, recovered -/

/-- The register-level circuit refines the filtered circuit (with any window `kq`). -/
theorem asyncFifo_expr_refines_F :
    [e| asyncFifoLowered, (env α n lat stl su).find? ] ⊑
      [e| asyncFifoLowered, (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? ] := by
  apply ExprLow.refines_env _ wf_env wf_envF
  intro i t
  by_cases hw : t = "wdom"
  · subst hw
    exact ExprLow.refines_base_of_refines i _ (env_wdom α n lat stl su) (envF_wdom α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r)
      writeDomain_refines
  by_cases hr : t = "rdom"
  · subst hr
    exact ExprLow.refines_base_of_refines i _ (env_rdom α n lat stl su) (envF_rdom α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r)
      readDomain_refines
  · exact ExprLow.refines_base_of_eq i t (env_find_ne t hw hr)

/-- **The register-level asynchronous FIFO refines the FIFO specification** whenever the
synchroniser settling time and the sampling window fit in both clock periods. -/
theorem asyncFifo_refines (hsw : su < P_w) (hsr : su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r) :
    [e| asyncFifoLowered, (env α n lat stl su).find? ] ⊑ fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  Module.refines_transitive _ (asyncFifo_expr_refines_F (kq := 0) (P_w := P_w) (P_r := P_r) (S_w := S_w) (S_r := S_r) (R_w := R_w) (R_r := R_r))
    (Module.refines_transitive _ (asyncFifoF_expr_refines α n lat stl su 0 0 P_w P_r S_w S_r R_w R_r pw_w pw_r)
      (refinesF (kq := 0) (rdly := 0) (by lia) (by lia) hstlw hstlr (by lia) (by lia) (by lia)))

end Timed

end Graphiti.AsyncFifo
