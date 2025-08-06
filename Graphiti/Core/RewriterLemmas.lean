/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Rewriter
import Graphiti.Core.Environment
import Graphiti.Core.WellTyped

open Batteries (AssocList)

namespace Graphiti

structure CorrectRewrite (ε_global : Env String String) where
  pattern : Pattern String String
  rewrite : DefiniteRewrite String String
  ε_left : Env String String
  ε_right : Env String String
  consistent : ε_left.subsetOf ε_global ∧ ε_right.subsetOf ε_global
  wf : rewrite.input_expr.well_formed ε_left ∧ rewrite.output_expr.well_formed ε_right
  refines :
    [e| rewrite.output_expr, ε_right ] ⊑ ([e| rewrite.input_expr, ε_left ])

structure VerifiedRewrite (ε_global ε_left ε_right : Env String String) (rw : DefiniteRewrite String String) : Prop where
  consistent : ε_left.subsetOf ε_global ∧ ε_right.subsetOf ε_global
  wf : rw.input_expr.well_formed ε_left ∧ rw.output_expr.well_formed ε_right
  refines :
    [e| rw.output_expr, ε_right ] ⊑ ([e| rw.input_expr, ε_left ])

def toRewrite {ε} (rw : CorrectRewrite ε) : Rewrite String String :=
  {pattern := rw.pattern, rewrite := λ _ => pure rw.rewrite}

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

theorem refines_higher_correct {Ident Typ} [DecidableEq Ident] [DecidableEq Typ] {f} {ε g} {e : ExprLow Ident Typ} :
  e.higher_correct f = .some g →
  ExprLow.well_formed ε e = true →
  [Ge| g, ε ] ⊑ ([e| e, ε ]) := by
  intro higher
  unfold ExprLow.higher_correct at higher
  unfold ExprHigh.build_module_expr ExprHigh.build_module ExprHigh.build_module'
  rw [refines_higher_correct_connections] <;> try assumption
  apply ExprLow.refines_comm_bases

-- /--
-- Generate a reverse rewrite from a rewrite and the RewriteInfo associated with the execution.
-- -/
-- def reverse_rewrite_correct {ε_global} (rw : CorrectRewrite ε_global) (rinfo : RewriteInfo) := do
--   let (_nodes, l) ← rw.pattern rinfo.input_graph
--   let def_rewrite ← ofOption (.error "could not generate rewrite") <| rw.rewrite l
--   reverse_rewrite' def_rewrite rinfo

theorem Rewrite_run'_correct {b} {ε_global : Env String String} {g g' : ExprHigh String String} {e_g : ExprLow String String}
        {_st _st'} {rw : CorrectRewrite ε_global} :
  g.lower = some e_g →
  e_g.well_formed ε_global →
  Rewrite.run' g (toRewrite rw) b _st = .ok g' _st' →
  ([Ge| g', ε_global ]) ⊑ ([Ge| g, ε_global ]) := by

  unfold Rewrite.run'; simp; intro hlower_some hwell_formed_global hrewrite
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
  -- rename (Option.bind _ ExprLow.higher_correct = some _) => hrewrite
  -- have hrewrite'' := Option.bind_eq_some.mp hrewrite
  -- obtain ⟨_, _, Hhighering⟩ := hrewrite''
  -- clear hrewrite
  rename ExprHigh.lower g = _ => hverylower
  rw [hlower_some] at hverylower
  cases hverylower
  subst_vars
  repeat cases ‹Unit›
  rename RewriteState => rewrite_info
  rename g.extract _ = _ => Hextract
  rename ExprHigh.lower _ = _ => Hlower
  rename (toRewrite rw).rewrite _ = _ => Hrewrite
  rename ExprLow.weak_beq _ _ = _ => Hweakbeq
  rename (toRewrite rw).pattern _ _ = _ => Hpattern
  rename PortMapping String × PortMapping String => ioPortMap
  rename ExprLow String String => lowered
  repeat clear ‹portmappingToNameRename' _ _ _ = _›
  repeat clear ‹addRewriteInfo _ _ = _›
  repeat clear ‹updRewriteInfo _ _ = _›
  rename ExprHigh String String × ExprHigh String String => extractedGraphs
  rename List String × List String => pattern
  rename DefiniteRewrite String String => defrw
  rename ExprHigh String String => outGraph
  dsimp [toRewrite] at Hrewrite
  cases Hrewrite
  rename_i wo wi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have rw_output_wf : ExprLow.well_formed ε_global rw.rewrite.output_expr = true := by
    apply ExprLow.refines_subset_well_formed
    apply rw.consistent.2
    apply rw.wf.2
  have rw_input_wf : ExprLow.well_formed ε_global rw.rewrite.input_expr = true := by
    apply ExprLow.refines_subset_well_formed
    apply rw.consistent.1
    apply rw.wf.1
  have wo_wf : ExprLow.well_formed ε_global wo = true := by
    solve_by_elim [ExprLow.refines_renamePorts_well_formed]
  have lowered_wf : ExprLow.well_formed ε_global lowered = true := by
    solve_by_elim [ExprLow.refines_renamePorts_well_formed]
  apply Module.refines_transitive
  dsimp [ExprHigh.build_module_expr, ExprHigh.build_module, ExprHigh.build_module']
  apply refines_higher_correct; assumption
  · rw [ExprLow.force_replace_eq_replace]; apply ExprLow.replacement_well_formed
    · apply ExprLow.refines_comm_connections'_well_formed
      apply ExprLow.refines_comm_bases_well_formed
      assumption
    · assumption
  apply Module.refines_transitive
  rw [ExprLow.force_replace_eq_replace]
  apply ExprLow.replacement
  · apply ExprLow.well_formed_implies_wf
    apply ExprLow.refines_comm_connections'_well_formed
    apply ExprLow.refines_comm_bases_well_formed
    assumption
  · apply ExprLow.well_formed_implies_wf; assumption
  apply Module.refines_transitive (imod' := ([e| wi, ε_global ]))
  · apply Module.refines_transitive
    apply ExprLow.refines_renamePorts_2'; rotate_left 1; assumption; rotate_right 1
    · assumption
    rw [ExprLow.ensureIOUnmodified_correct] <;> try assumption
    apply Module.refines_transitive
    apply ExprLow.refines_renamePorts_2'; rotate_left 1; assumption; rotate_right 1
    · assumption
    apply Module.refines_transitive
    apply Module.refines_renamePorts
    apply ExprLow.refines_subset
    apply rw.consistent.2
    apply rw.consistent.1
    apply rw.wf.2
    apply rw.wf.1
    solve_by_elim [rw.refines]
    apply ExprLow.refines_renamePorts_1'; rotate_left 1; assumption; rotate_right 1
    · assumption
  apply ExprLow.refines_comm_connections2'
  · apply ExprLow.refines_renamePorts_well_formed
    · assumption
    · apply ExprLow.refines_subset_well_formed
      apply rw.consistent.1
      apply rw.wf.1
  apply Module.refines_transitive
  apply ExprLow.refines_comm_connections'
  · apply ExprLow.refines_comm_bases_well_formed; assumption
  apply Module.refines_transitive
  apply ExprLow.refines_comm_bases
  · assumption
  unfold ExprHigh.build_module_expr ExprHigh.build_module ExprHigh.build_module'
  rw [‹g.lower = _›]
  apply Module.refines_reflexive

/--
info: 'Graphiti.Rewrite_run'_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewrite_run'_correct

structure CorrectRewrite2
    (ε : FinEnv String (String × Nat))
    (h_wf : ∀ s, Env.well_formed ε.find? s)
where
  rewrite : Rewrite String (String × Nat)
  ε_extension : FinEnv String (String × Nat)
  ε_extension_conservative :
  refinement : ∀ l rw st st',
    (rewrite.rewrite l).run st = .ok rw st' →
    (h_wt : rw.input_expr.well_typed ε.find?) →
    [e| rw.output_expr, (ε ++ ε_extension).find? ] ⊑ [e| rw.input_expr, (ε ++ ε_extension).find? ]

theorem Rewrite_run'_correct2 {b} {ε_global : Env String (String × Nat)} {g g' : ExprHigh String (String × Nat)} {e_g : ExprLow String (String × Nat)}
        {_st _st'} :
  g.lower = some e_g →
  e_g.well_formed ε_global →
  Rewrite.run' g (toRewrite rw) b _st = .ok g' _st' →
  ([Ge| g', ε_global ]) ⊑ ([Ge| g, ε_global ]) := by

end Graphiti
