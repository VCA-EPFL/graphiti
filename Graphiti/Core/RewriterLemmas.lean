/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Rewriter
import Graphiti.Core.Environment
import Graphiti.Core.WellTyped

open Batteries (AssocList)

namespace Graphiti

structure WellFormedEnv (ε : FinEnv String (String × Nat)) (max_type : Nat) : Prop where
  h_wf : ε.toEnv.well_formed
  max_is_max : ε.max_typeD <= max_type

class Environment {n} (lhs : Vector Nat n → ExprLow String (String × Nat)) where
  ε : FinEnv String (String × Nat)
  max_type : Nat
  types : Vector Nat n
  h_wf : WellFormedEnv ε max_type
  h_lhs_wt : (lhs types).well_typed ε.toEnv
  h_lhs_wf : (lhs types).well_formed ε.toEnv

theorem EStateM.bind_eq_ok {ε σ α β} {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s v s'} :
  x.bind f s = .ok v s' →
  ∃ (x_int : α) (s_int : σ),
    x s = .ok x_int s_int ∧ f x_int s_int = .ok v s' := by
  unfold EStateM.bind; split <;> tauto

theorem ofOption_eq_ok {ε σ α} {e : ε} {o : Option α} {o' : α} {s s' : σ} :
  ofOption e o s = EStateM.Result.ok o' s' →
  o = o' ∧ s = s' := by
  unfold ofOption
  split <;> (intros h; cases h)
  constructor <;> rfl

theorem liftError_eq_ok {σ α} {o : Except String α} {o' : α} {s s' : σ} :
  liftError o s = EStateM.Result.ok o' s' →
  o = .ok o' ∧ s = s' := by
  unfold liftError; split <;> (intros h; cases h)
  constructor <;> rfl

theorem guard_eq_ok {ε σ} {e : ε} {b : Bool} {o' : Unit} {s s' : σ} :
  EStateM.guard e b s = EStateM.Result.ok o' s' →
  b = true ∧ s = s' := by
  unfold EStateM.guard; split <;> (intros h; cases h)
  subst b; constructor <;> rfl

theorem EStateM.map_eq_ok {ε σ α β} {f : α → β} {o : EStateM ε σ α} {o' : β} {s s' : σ} :
  EStateM.map f o s = .ok o' s' →
  ∃ o'' s'', o s = .ok o'' s'' ∧ s' = s'' ∧ o' = f o'' := by
  unfold EStateM.map; split <;> (intros h; cases h)
  constructor; constructor; and_intros <;> solve | assumption | rfl

axiom refines_higherSS {e : ExprLow String String} {e' : ExprHigh String String} :
  e.higherSS = .some e' →
  e'.lower = .some e

theorem higher_correct_products_correct {Ident Typ} {f} {e₂ : ExprLow Ident Typ} {v'} :
  e₂.higher_correct_products f = some v' →
  List.foldr ExprHigh.generate_product none v'.toList = some e₂ := by
  induction e₂ generalizing v' with
  | base inst typ =>
    intro hc
    dsimp [ExprLow.higher_correct_products] at hc; cases hc; rfl
  | product e₁ e₂ ih1 ih2 =>
    intro hc
    cases e₁ <;> dsimp [ExprLow.higher_correct_products] at hc <;> (try contradiction)
    rw [Option.bind_eq_some] at hc
    obtain ⟨v', ha', hb'⟩ := hc; cases hb'
    dsimp
    rw [ih2]
    rfl; assumption
  | connect c e ihe =>
    intro hc
    dsimp [ExprLow.higher_correct_products] at hc; contradiction

theorem refines_higher_correct_connections {Ident Typ} {f} {e : ExprLow Ident Typ} {e' : ExprHigh Ident Typ} :
  e.higher_correct_connections f = .some e' →
  e'.lower = .some e := by
  induction e generalizing e' with
  | base inst typ =>
    intro h
    dsimp [ExprLow.higher_correct_connections] at h
    rw [Option.bind_eq_some] at h
    obtain ⟨v, ha, hb⟩ := h
    cases hb
    dsimp [ExprHigh.lower, ExprHigh.lower']
    dsimp [ExprLow.higher_correct_products] at ha; cases ha; rfl
  | connect c e ihe =>
    intro h
    dsimp [ExprLow.higher_correct_connections] at h
    rw [Option.bind_eq_some] at h
    obtain ⟨v, ha, hb⟩ := h
    cases hb
    dsimp [ExprHigh.lower, ExprHigh.lower']
    specialize ihe ha
    unfold ExprHigh.lower at ihe
    split at ihe <;> try contradiction
    cases ihe; congr
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro h
    dsimp [ExprLow.higher_correct_connections] at h
    rw [Option.bind_eq_some] at h
    obtain ⟨v, ha, hb⟩ := h
    cases hb
    dsimp [ExprHigh.lower, ExprHigh.lower']
    cases e₁ <;> (try dsimp [ExprLow.higher_correct_products] at ha <;> contradiction)
    rename_i map1 typ1
    dsimp [ExprLow.higher_correct_products] at ha
    rw [Option.bind_eq_some] at ha
    obtain ⟨v', ha', hb'⟩ := ha; cases hb'
    dsimp; rw [Batteries.AssocList.toList_toAssocList]
    congr
    rw [higher_correct_products_correct]
    dsimp; rfl; assumption

theorem higher_correct_eq {Ident Typ} [DecidableEq Ident] [DecidableEq Typ] {f} {e : ExprLow Ident Typ} {e' : ExprHigh Ident Typ} :
  e.higher_correct f = .some e' →
  e'.lower = .some (ExprLow.comm_bases (ExprLow.get_all_products e) e) :=
  refines_higher_correct_connections

theorem refines_higher_correct {Ident Typ} [DecidableEq Ident] [DecidableEq Typ] {f} {ε g} {e : ExprLow Ident Typ} :
  e.higher_correct f = .some g →
  ExprLow.well_formed ε e = true →
  [Ge| g, ε ] ⊑ ([e| e, ε ]) := by
  intro higher
  unfold ExprLow.higher_correct at higher
  unfold ExprHigh.build_module_expr ExprHigh.build_module ExprHigh.build_module'
  rw [refines_higher_correct_connections] <;> try assumption
  apply ExprLow.refines_comm_bases

structure VerifiedRewrite (rewrite : DefiniteRewrite String (String × Nat)) (ε : FinEnv String (String × Nat)) where
  ε_ext : FinEnv String (String × Nat)
  ε_ext_wf : ε_ext.toEnv.well_formed
  ε_independent : Env.independent ε_ext.toEnv ε.toEnv
  rhs_wf : rewrite.output_expr.well_formed ε_ext.toEnv
  rhs_wt : rewrite.output_expr.well_typed ε_ext.toEnv
  lhs_locally_wf : rewrite.input_expr.locally_wf
  refinement : [e| rewrite.output_expr, (ε ++ ε_ext).toEnv ] ⊑ [e| rewrite.input_expr, ε.toEnv ]

theorem run'_implies_pattern {g b st g' _st' rw}:
  Rewrite.run' g rw b st = .ok g' _st' →
  ∃ out, rw.pattern g = .ok out := by
  intro hrewrite
  repeat
    rename (EStateM.bind _ _ _ = .ok _ _) => hrewrite
    replace hrewrite := EStateM.bind_eq_ok hrewrite
    let ⟨_, _, _, hrewrite'⟩ := hrewrite
    clear hrewrite; have hrewrite := hrewrite'; clear hrewrite'
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (ofOption _ _ _ = .ok _ _) => hofOption
    replace hofOption := ofOption_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (liftError _ _ = .ok _ _) => hofOption
    replace hofOption := liftError_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.guard _ _ _ = .ok _ _) => hofOption
    replace hofOption := guard_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.map _ _ _ = .ok _ _) => hofOption
    replace hofOption := EStateM.map_eq_ok hofOption
    let ⟨_, _, _, _, _⟩ := hofOption; clear hofOption
  rename (rw.pattern _).runWithState _ = _ => Hpattern
  cases heq : (rw.pattern g)
  · rw [heq] at Hpattern; dsimp [RewriteResultSL.runWithState] at Hpattern; cases Hpattern
  · constructor; rfl

theorem run'_implies_wt_lhs {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {grph} :
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  grph = (rw.rewrite types st.fresh_type).input_expr →
  grph.locally_wf →
  grph.well_typed ε_global.toEnv := by
  unfold Rewrite.run'; simp; intro hpat hlower_some hwf hwt hrewrite _ hloc
  subst grph
  dsimp [Bind.bind, Monad.toBind, EStateM.instMonad] at *
  repeat
    rename (EStateM.bind _ _ _ = .ok _ _) => hrewrite
    replace hrewrite := EStateM.bind_eq_ok hrewrite
    let ⟨_, _, _, hrewrite'⟩ := hrewrite
    clear hrewrite; have hrewrite := hrewrite'; clear hrewrite'
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (ofOption _ _ _ = .ok _ _) => hofOption
    replace hofOption := ofOption_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (liftError _ _ = .ok _ _) => hofOption
    replace hofOption := liftError_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.guard _ _ _ = .ok _ _) => hofOption
    replace hofOption := guard_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.map _ _ _ = .ok _ _) => hofOption
    replace hofOption := EStateM.map_eq_ok hofOption
    let ⟨_, _, _, _, _⟩ := hofOption; clear hofOption
  rename ExprHigh.lower g = _ => hverylower
  rw [hlower_some] at hverylower
  cases hverylower
  subst_vars
  repeat cases ‹Unit›
  rename RewriteState => rewrite_info
  rename g.extract _ = _ => Hextract
  rename ExprHigh.lower _ = _ => Hlower
  rename ExprLow.higher_correct _ _ = _ => Hrewrite
  rename ExprLow.weak_beq _ _ = _ => Hweakbeq
  rename (rw.pattern _).runWithState _ = _ => Hpattern
  rename PortMapping String × PortMapping String => ioPortMap
  rename ExprLow String (String × Nat) => lowered
  repeat clear ‹portmappingToNameRename' _ _ _ = _›
  repeat clear ‹addRewriteInfo _ _ = _›
  repeat clear ‹updRewriteInfo _ _ = _›
  rename ExprHigh String (String × Nat) × ExprHigh String (String × Nat) => extractedGraphs
  rename List String × Vector Nat rw.params => pattern
  rename ExprHigh String (String × Nat) => outGraph
  rw [hpat] at Hpattern
  dsimp [RewriteResultSL.runWithState] at Hpattern
  cases Hpattern
  cases ‹EStateM.get _ = _›
  rename_i wo wi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have wi_wf : ExprLow.well_formed ε_global.toEnv wi = true := by
    apply ExprLow.refines_comm_connections'_well_formed2
    · apply ExprLow.replacement_well_formed2; rotate_left 1
      · assumption
      · apply ExprLow.refines_comm_connections'_well_formed
        apply ExprLow.refines_comm_bases_well_formed
        assumption
  have rw_input_wf : ExprLow.well_formed ε_global.toEnv (rw.rewrite types st.fresh_type).input_expr = true := by
    apply ExprLow.mapPorts2_well_formed2; rotate_left 2
    . apply hloc
    · apply wi_wf
    · assumption
    · apply AssocList.bijectivePortRenaming_bijective
    · apply AssocList.bijectivePortRenaming_bijective
  apply ExprLow.renamePorts_well_typed; assumption; assumption
  apply ExprLow.comm_connections_well_typed; assumption
  apply ExprLow.replacement_well_typed; rotate_left; assumption
  apply ExprLow.wt_comm_connections2'
  apply ExprLow.refines_comm_bases_well_formed
  assumption
  apply ExprLow.wt_comm_bases
  assumption
  assumption

theorem run'_implies_wf_lhs {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {grph} :
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  grph = (rw.rewrite types st.fresh_type).input_expr →
  grph.locally_wf →
  grph.well_formed ε_global.toEnv := by
  unfold Rewrite.run'; simp; intro hpat hlower_some hwf hwt hrewrite hgrph hloc
  dsimp [Bind.bind, Monad.toBind, EStateM.instMonad] at *
  repeat
    rename (EStateM.bind _ _ _ = .ok _ _) => hrewrite
    replace hrewrite := EStateM.bind_eq_ok hrewrite
    let ⟨_, _, _, hrewrite'⟩ := hrewrite
    clear hrewrite; have hrewrite := hrewrite'; clear hrewrite'
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (ofOption _ _ _ = .ok _ _) => hofOption
    replace hofOption := ofOption_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (liftError _ _ = .ok _ _) => hofOption
    replace hofOption := liftError_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.guard _ _ _ = .ok _ _) => hofOption
    replace hofOption := guard_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.map _ _ _ = .ok _ _) => hofOption
    replace hofOption := EStateM.map_eq_ok hofOption
    let ⟨_, _, _, _, _⟩ := hofOption; clear hofOption
  rename ExprHigh.lower g = _ => hverylower
  rw [hlower_some] at hverylower
  cases hverylower
  subst_vars
  repeat cases ‹Unit›
  rename RewriteState => rewrite_info
  rename g.extract _ = _ => Hextract
  rename ExprHigh.lower _ = _ => Hlower
  rename ExprLow.higher_correct _ _ = _ => Hrewrite
  rename ExprLow.weak_beq _ _ = _ => Hweakbeq
  rename (rw.pattern _).runWithState _ = _ => Hpattern
  rename PortMapping String × PortMapping String => ioPortMap
  rename ExprLow String (String × Nat) => lowered
  repeat clear ‹portmappingToNameRename' _ _ _ = _›
  repeat clear ‹addRewriteInfo _ _ = _›
  repeat clear ‹updRewriteInfo _ _ = _›
  rename ExprHigh String (String × Nat) × ExprHigh String (String × Nat) => extractedGraphs
  rename List String × Vector Nat rw.params => pattern
  rename ExprHigh String (String × Nat) => outGraph
  rw [hpat] at Hpattern
  dsimp [RewriteResultSL.runWithState] at Hpattern
  cases Hpattern
  cases ‹EStateM.get _ = _›
  rename_i wo wi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have wi_wf : ExprLow.well_formed ε_global.toEnv wi = true := by
    apply ExprLow.refines_comm_connections'_well_formed2
    · apply ExprLow.replacement_well_formed2; rotate_left 1
      · assumption
      · apply ExprLow.refines_comm_connections'_well_formed
        apply ExprLow.refines_comm_bases_well_formed
        assumption
  apply ExprLow.mapPorts2_well_formed2; rotate_left 2
  . assumption
  · apply wi_wf
  · assumption
  · apply AssocList.bijectivePortRenaming_bijective
  · apply AssocList.bijectivePortRenaming_bijective

theorem run'_refines {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {vrw : VerifiedRewrite (rw.rewrite types st.fresh_type) ε_global}:
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  [Ge| g', (ε_global ++ vrw.ε_ext).toEnv ] ⊑ [Ge| g, ε_global.toEnv ] := by
  unfold Rewrite.run'; simp; intro hpat hlower_some hwf hwt hrewrite
  dsimp [Bind.bind, Monad.toBind, EStateM.instMonad] at *
  repeat
    rename (EStateM.bind _ _ _ = .ok _ _) => hrewrite
    replace hrewrite := EStateM.bind_eq_ok hrewrite
    let ⟨_, _, _, hrewrite'⟩ := hrewrite
    clear hrewrite; have hrewrite := hrewrite'; clear hrewrite'
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (ofOption _ _ _ = .ok _ _) => hofOption
    replace hofOption := ofOption_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (liftError _ _ = .ok _ _) => hofOption
    replace hofOption := liftError_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.guard _ _ _ = .ok _ _) => hofOption
    replace hofOption := guard_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.map _ _ _ = .ok _ _) => hofOption
    replace hofOption := EStateM.map_eq_ok hofOption
    let ⟨_, _, _, _, _⟩ := hofOption; clear hofOption
  rename ExprHigh.lower g = _ => hverylower
  rw [hlower_some] at hverylower
  cases hverylower
  subst_vars
  repeat cases ‹Unit›
  rename RewriteState => rewrite_info
  rename g.extract _ = _ => Hextract
  rename ExprHigh.lower _ = _ => Hlower
  rename ExprLow.higher_correct _ _ = _ => Hrewrite
  rename ExprLow.weak_beq _ _ = _ => Hweakbeq
  rename (rw.pattern _).runWithState _ = _ => Hpattern
  rename PortMapping String × PortMapping String => ioPortMap
  rename ExprLow String (String × Nat) => lowered
  repeat clear ‹portmappingToNameRename' _ _ _ = _›
  repeat clear ‹addRewriteInfo _ _ = _›
  repeat clear ‹updRewriteInfo _ _ = _›
  rename ExprHigh String (String × Nat) × ExprHigh String (String × Nat) => extractedGraphs
  rename List String × Vector Nat rw.params => pattern
  rename ExprHigh String (String × Nat) => outGraph
  rw [hpat] at Hpattern
  dsimp [RewriteResultSL.runWithState] at Hpattern
  cases Hpattern
  cases ‹EStateM.get _ = _›
  rename_i wo wi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have wi_wf : ExprLow.well_formed ε_global.toEnv wi = true := by
    apply ExprLow.refines_comm_connections'_well_formed2
    · apply ExprLow.replacement_well_formed2; rotate_left 1
      · assumption
      · apply ExprLow.refines_comm_connections'_well_formed
        apply ExprLow.refines_comm_bases_well_formed
        assumption
  have rw_input_wf : ExprLow.well_formed ε_global.toEnv (rw.rewrite types st.fresh_type).input_expr = true := by
    apply ExprLow.mapPorts2_well_formed2; rotate_left 2
    . apply vrw.lhs_locally_wf
    · apply wi_wf
    · assumption
    · apply AssocList.bijectivePortRenaming_bijective
    · apply AssocList.bijectivePortRenaming_bijective
  have lhs_wt : (rw.rewrite types st.fresh_type).input_expr.well_typed ε_global.toEnv := by
    apply ExprLow.renamePorts_well_typed; assumption; assumption
    apply ExprLow.comm_connections_well_typed; assumption
    apply ExprLow.replacement_well_typed; rotate_left; assumption
    apply ExprLow.wt_comm_connections2'
    apply ExprLow.refines_comm_bases_well_formed
    assumption
    apply ExprLow.wt_comm_bases
    assumption
    assumption
  have rw_output_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv (rw.rewrite types st.fresh_type).output_expr = true := by
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.independent_subset_of_union
    apply Env.independent_symm
    apply vrw.ε_independent
    apply vrw.rhs_wf
  have wo_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv wo = true := by
    solve_by_elim [ExprLow.refines_renamePorts_well_formed]
  have lowered_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv lowered = true := by
    solve_by_elim [ExprLow.refines_renamePorts_well_formed]
  apply Module.refines_transitive
  dsimp [ExprHigh.build_module_expr, ExprHigh.build_module, ExprHigh.build_module']
  apply refines_higher_correct; assumption
  · rw [ExprLow.force_replace_eq_replace]; apply ExprLow.replacement_well_formed
    · apply ExprLow.refines_comm_connections'_well_formed
      apply ExprLow.refines_comm_bases_well_formed
      apply ExprLow.refines_subset_well_formed
      apply FinEnv.subset_of_union
      assumption
    · assumption
  apply Module.refines_transitive
  rw [ExprLow.force_replace_eq_replace]
  apply ExprLow.replacement
  · apply ExprLow.well_formed_implies_wf
    apply ExprLow.refines_comm_connections'_well_formed
    apply ExprLow.refines_comm_bases_well_formed
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption
  · apply ExprLow.well_formed_implies_wf; assumption
  apply Module.refines_transitive (imod' := ([e| wi, (ε_global ++ vrw.ε_ext).toEnv ]))
  · apply Module.refines_transitive
    apply ExprLow.refines_renamePorts_2'; rotate_left 1; assumption; rotate_right 1
    · assumption
    rw [ExprLow.ensureIOUnmodified_correct] <;> try assumption
    apply Module.refines_transitive
    apply ExprLow.refines_renamePorts_2'; rotate_left 1; assumption; rotate_right 1
    · assumption
    apply Module.refines_transitive
    apply Module.refines_renamePorts
    apply vrw.refinement
    apply Module.refines_transitive
    apply Module.refines_renamePorts
    apply ExprLow.refines_subset_left
    apply FinEnv.subset_of_union (ε₂ := vrw.ε_ext)
    assumption
    apply ExprLow.refines_renamePorts_1'; rotate_left 1; assumption; rotate_right 1
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption
  apply ExprLow.refines_comm_connections2'
  · apply ExprLow.refines_renamePorts_well_formed
    · assumption
    · apply ExprLow.refines_subset_well_formed
      apply FinEnv.subset_of_union
      assumption
  apply Module.refines_transitive
  apply ExprLow.refines_comm_connections'
  · apply ExprLow.refines_comm_bases_well_formed
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption
  apply Module.refines_transitive
  apply ExprLow.refines_comm_bases
  · apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption
  unfold ExprHigh.build_module_expr ExprHigh.build_module ExprHigh.build_module'
  rw [‹g.lower = _›]
  apply ExprLow.refines_subset_right
  apply FinEnv.subset_of_union
  assumption

theorem run'_preserves_well_formed {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {vrw : VerifiedRewrite (rw.rewrite types st.fresh_type) ε_global}:
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  ∃ e_g', g'.lower = some e_g' ∧ e_g'.well_formed (ε_global ++ vrw.ε_ext).toEnv := by
  unfold Rewrite.run'; simp; intro hpat hlower_some hwf hwt hrewrite
  dsimp [Bind.bind, Monad.toBind, EStateM.instMonad] at *
  repeat
    rename (EStateM.bind _ _ _ = .ok _ _) => hrewrite
    replace hrewrite := EStateM.bind_eq_ok hrewrite
    let ⟨_, _, _, hrewrite'⟩ := hrewrite
    clear hrewrite; have hrewrite := hrewrite'; clear hrewrite'
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (ofOption _ _ _ = .ok _ _) => hofOption
    replace hofOption := ofOption_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (liftError _ _ = .ok _ _) => hofOption
    replace hofOption := liftError_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.guard _ _ _ = .ok _ _) => hofOption
    replace hofOption := guard_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.map _ _ _ = .ok _ _) => hofOption
    replace hofOption := EStateM.map_eq_ok hofOption
    let ⟨_, _, _, _, _⟩ := hofOption; clear hofOption
  rename ExprHigh.lower g = _ => hverylower
  rw [hlower_some] at hverylower
  cases hverylower
  subst_vars
  repeat cases ‹Unit›
  rename RewriteState => rewrite_info
  rename g.extract _ = _ => Hextract
  rename ExprHigh.lower _ = _ => Hlower
  rename ExprLow.higher_correct _ _ = _ => Hrewrite
  rename ExprLow.weak_beq _ _ = _ => Hweakbeq
  rename (rw.pattern _).runWithState _ = _ => Hpattern
  rename PortMapping String × PortMapping String => ioPortMap
  rename ExprLow String (String × Nat) => lowered
  repeat clear ‹portmappingToNameRename' _ _ _ = _›
  repeat clear ‹addRewriteInfo _ _ = _›
  repeat clear ‹updRewriteInfo _ _ = _›
  rename ExprHigh String (String × Nat) × ExprHigh String (String × Nat) => extractedGraphs
  rename List String × Vector Nat rw.params => pattern
  rename ExprHigh String (String × Nat) => outGraph
  rw [hpat] at Hpattern
  dsimp [RewriteResultSL.runWithState] at Hpattern
  cases Hpattern
  cases ‹EStateM.get _ = _›
  rename_i wo wi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have rw_output_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv (rw.rewrite types st.fresh_type).output_expr = true := by
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.independent_subset_of_union
    apply Env.independent_symm
    apply vrw.ε_independent
    apply vrw.rhs_wf
  have wi_wf : ExprLow.well_formed ε_global.toEnv wi = true := by
    apply ExprLow.refines_comm_connections'_well_formed2
    · apply ExprLow.replacement_well_formed2; rotate_left 1
      · assumption
      · apply ExprLow.refines_comm_connections'_well_formed
        apply ExprLow.refines_comm_bases_well_formed
        assumption
  have rw_input_wf : ExprLow.well_formed ε_global.toEnv (rw.rewrite types st.fresh_type).input_expr = true := by
    apply ExprLow.mapPorts2_well_formed2; rotate_left 2
    . apply vrw.lhs_locally_wf
    · apply wi_wf
    · assumption
    · apply AssocList.bijectivePortRenaming_bijective
    · apply AssocList.bijectivePortRenaming_bijective
  have wo_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv wo = true := by
    solve_by_elim [ExprLow.refines_renamePorts_well_formed]
  have lowered_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv lowered = true := by
    solve_by_elim [ExprLow.refines_renamePorts_well_formed]
  constructor; and_intros
  · solve_by_elim [higher_correct_eq]
  · apply ExprLow.refines_comm_bases_well_formed
    rw [ExprLow.force_replace_eq_replace]
    apply ExprLow.replacement_well_formed
    apply ExprLow.refines_comm_connections'_well_formed
    apply ExprLow.refines_comm_bases_well_formed
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption
    assumption

theorem run'_preserves_well_typed {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {vrw : VerifiedRewrite (rw.rewrite types st.fresh_type) ε_global}:
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  ∃ e_g', g'.lower = some e_g' ∧ e_g'.well_typed (ε_global ++ vrw.ε_ext).toEnv := by
  unfold Rewrite.run'; simp; intro hpat hlower_some hwf hwt hrewrite
  dsimp [Bind.bind, Monad.toBind, EStateM.instMonad] at *
  repeat
    rename (EStateM.bind _ _ _ = .ok _ _) => hrewrite
    replace hrewrite := EStateM.bind_eq_ok hrewrite
    let ⟨_, _, _, hrewrite'⟩ := hrewrite
    clear hrewrite; have hrewrite := hrewrite'; clear hrewrite'
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (ofOption _ _ _ = .ok _ _) => hofOption
    replace hofOption := ofOption_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (liftError _ _ = .ok _ _) => hofOption
    replace hofOption := liftError_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.guard _ _ _ = .ok _ _) => hofOption
    replace hofOption := guard_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.map _ _ _ = .ok _ _) => hofOption
    replace hofOption := EStateM.map_eq_ok hofOption
    let ⟨_, _, _, _, _⟩ := hofOption; clear hofOption
  rename ExprHigh.lower g = _ => hverylower
  rw [hlower_some] at hverylower
  cases hverylower
  subst_vars
  repeat cases ‹Unit›
  rename RewriteState => rewrite_info
  rename g.extract _ = _ => Hextract
  rename ExprHigh.lower _ = _ => Hlower
  rename ExprLow.higher_correct _ _ = _ => Hrewrite
  rename ExprLow.weak_beq _ _ = _ => Hweakbeq
  rename (rw.pattern _).runWithState _ = _ => Hpattern
  rename PortMapping String × PortMapping String => ioPortMap
  rename ExprLow String (String × Nat) => lowered
  repeat clear ‹portmappingToNameRename' _ _ _ = _›
  repeat clear ‹addRewriteInfo _ _ = _›
  repeat clear ‹updRewriteInfo _ _ = _›
  rename ExprHigh String (String × Nat) × ExprHigh String (String × Nat) => extractedGraphs
  rename List String × Vector Nat rw.params => pattern
  rename ExprHigh String (String × Nat) => outGraph
  rw [hpat] at Hpattern
  dsimp [RewriteResultSL.runWithState] at Hpattern
  cases Hpattern
  cases ‹EStateM.get _ = _›
  rename_i wo wi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have rw_output_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv (rw.rewrite types st.fresh_type).output_expr = true := by
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.independent_subset_of_union
    apply Env.independent_symm
    apply vrw.ε_independent
    apply vrw.rhs_wf
  have wi_wf : ExprLow.well_formed ε_global.toEnv wi = true := by
    apply ExprLow.refines_comm_connections'_well_formed2
    · apply ExprLow.replacement_well_formed2; rotate_left 1
      · assumption
      · apply ExprLow.refines_comm_connections'_well_formed
        apply ExprLow.refines_comm_bases_well_formed
        assumption
  have rw_input_wf : ExprLow.well_formed ε_global.toEnv (rw.rewrite types st.fresh_type).input_expr = true := by
    apply ExprLow.mapPorts2_well_formed2; rotate_left 2
    . apply vrw.lhs_locally_wf
    · apply wi_wf
    · assumption
    · apply AssocList.bijectivePortRenaming_bijective
    · apply AssocList.bijectivePortRenaming_bijective
  have wo_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv wo = true := by
    solve_by_elim [ExprLow.refines_renamePorts_well_formed]
  have lowered_wf : ExprLow.well_formed (ε_global ++ vrw.ε_ext).toEnv lowered = true := by
    solve_by_elim [ExprLow.refines_renamePorts_well_formed]
  constructor; and_intros
  · solve_by_elim [higher_correct_eq]
  · apply ExprLow.wt_comm_bases
    rw [ExprLow.force_replace_eq_replace]
    apply ExprLow.replacement_well_formed
    apply ExprLow.refines_comm_connections'_well_formed
    apply ExprLow.refines_comm_bases_well_formed
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption
    assumption
    rw [ExprLow.force_replace_eq_replace]
    apply ExprLow.wt_replacement

    apply Module.refines_transitive (imod' := ([e| wi, (ε_global ++ vrw.ε_ext).toEnv ]))
    · apply Module.refines_transitive
      apply ExprLow.refines_renamePorts_2'; rotate_left 1; assumption; rotate_right 1
      · assumption
      rw [ExprLow.ensureIOUnmodified_correct] <;> try assumption
      apply Module.refines_transitive
      apply ExprLow.refines_renamePorts_2'; rotate_left 1; assumption; rotate_right 1
      · assumption
      apply Module.refines_transitive
      apply Module.refines_renamePorts
      apply vrw.refinement
      apply Module.refines_transitive
      apply Module.refines_renamePorts
      apply ExprLow.refines_subset_left
      apply FinEnv.subset_of_union (ε₂ := vrw.ε_ext)
      assumption
      apply ExprLow.refines_renamePorts_1'; rotate_left 1; assumption; rotate_right 1
      apply ExprLow.refines_subset_well_formed
      apply FinEnv.subset_of_union
      assumption

    apply ExprLow.refines_comm_connections2'
    · apply ExprLow.refines_renamePorts_well_formed
      · assumption
      · apply ExprLow.refines_subset_well_formed
        apply FinEnv.subset_of_union
        assumption

    apply ExprLow.refines_comm_connections'_well_formed
    apply ExprLow.refines_comm_bases_well_formed
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption

    assumption

    apply ExprLow.wt_comm_connections2'
    apply ExprLow.refines_comm_bases_well_formed
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption
    apply ExprLow.wt_comm_bases
    apply ExprLow.refines_subset_well_formed
    apply FinEnv.subset_of_union
    assumption
    apply ExprLow.subset_well_typed
    apply FinEnv.subset_of_union
    assumption
    apply ExprLow.renamePorts_well_typed2
    apply wo_wf
    assumption
    apply ExprLow.renamePorts_well_typed2

    apply ExprLow.refines_subset_well_formed
    apply FinEnv.independent_subset_of_union
    apply Env.independent_symm
    apply vrw.ε_independent
    apply vrw.rhs_wf
    assumption
    apply ExprLow.subset_well_typed
    apply FinEnv.independent_subset_of_union
    apply Env.independent_symm
    apply vrw.ε_independent
    apply vrw.rhs_wt

#print axioms run'_preserves_well_typed

end Graphiti
