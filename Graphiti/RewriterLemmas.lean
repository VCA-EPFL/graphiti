/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.ExprHighLemmas
import Graphiti.Rewriter
import Graphiti.Environment

open Batteries (AssocList)

namespace Graphiti

structure CorrectRewrite (ε_global : Env) where
  pattern : Pattern String
  rewrite : DefiniteRewrite String
  ε_left : Env
  ε_right : Env
  consistent : ε_left.subsetOf ε_global ∧ ε_right.subsetOf ε_global
  wf : rewrite.input_expr.well_formed ε_left ∧ rewrite.output_expr.well_formed ε_right
  refines :
    [e| rewrite.output_expr, ε_right ] ⊑ ([e| rewrite.input_expr, ε_left ])

def toRewrite {ε} (rw : CorrectRewrite ε) : Rewrite String :=
  {pattern := rw.pattern, rewrite := λ _ => some rw.rewrite}

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

axiom refines_higherSS {e : ExprLow String} {e' : ExprHigh String} :
  e.higherSS = .some e' →
  e'.lower = .some e

-- #eval (ExprLow.connect ⟨⟨.internal "a", "b"⟩, ⟨.internal "a", "b"⟩⟩ (.connect ⟨⟨.internal "C", "b"⟩, ⟨.internal "C", "b"⟩⟩ (.product (.base (⟨AssocList.nil |>.cons ⟨.top, "b"⟩ ⟨.internal "a", "b"⟩, AssocList.nil |>.cons ⟨.top, "b"⟩ ⟨.internal "a", "b"⟩⟩) "A") (.product (.base ⟨AssocList.nil |>.cons ⟨.top, "b"⟩ ⟨.internal "a", "b"⟩, AssocList.nil |>.cons ⟨.top, "b"⟩ ⟨.internal "b", "b"⟩⟩ "B") (.base ⟨AssocList.nil |>.cons ⟨.top, "b"⟩ ⟨.internal "a", "b"⟩, AssocList.nil |>.cons ⟨.top, "b"⟩ ⟨.internal "c", "b"⟩⟩ "C"))))).higher_correct_connections |>.get rfl |>.lower

theorem higher_correct_products_correct {f} {e₂ : ExprLow String} {v'} :
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

theorem refines_higher_correct_connections {f} {e : ExprLow String} {e' : ExprHigh String} :
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

theorem refines_higher_correct {f} {ε e g} :
  e.higher_correct f = .some g →
  ExprLow.well_formed ε e = true →
  [Ge| g, ε ] ⊑ ([e| e, ε ]) := by
  intro higher
  unfold ExprLow.higher_correct at higher
  unfold ExprHigh.build_module_expr ExprHigh.build_module ExprHigh.build_module'
  rw [refines_higher_correct_connections] <;> try assumption
  apply ExprLow.refines_comm_bases

theorem Rewrite_run'_correct {b} {ε_global : Env} {g g' : ExprHigh String} {e_g : ExprLow String}
        {s _st _st'} {rw : CorrectRewrite ε_global} :
  g.lower = some e_g →
  e_g.well_formed ε_global →
  Rewrite.run' s g (toRewrite rw) b _st = .ok g' _st' →
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
  rename List RewriteInfo => rewrite_info
  rename g.extract _ = _ => Hextract
  rename ExprHigh.lower _ = _ => Hlower
  rename (toRewrite rw).rewrite _ = _ => Hrewrite
  rename ExprLow.weak_beq _ _ = _ => Hweakbeq
  rename (toRewrite rw).pattern _ _ = _ => Hpattern
  rename PortMapping String × PortMapping String => ioPortMap
  rename ExprLow String => lowered
  repeat clear ‹portmappingToNameRename' _ _ _ = _›
  repeat clear ‹addRewriteInfo _ _ = _›
  repeat clear ‹updRewriteInfo _ _ = _›
  rename ExprHigh String × ExprHigh String => extractedGraphs
  rename List String × List String => pattern
  rename DefiniteRewrite String => defrw
  rename ExprHigh String => outGraph
  dsimp [toRewrite] at Hrewrite
  cases Hrewrite
  cases hrewrite
  rename_i wo wi _ _ _ _ _ _ _ _ _ _
  have lowered_wf : ExprLow.well_formed ε_global lowered = true := by
    with_reducible split at ‹ite _ _ _ = _›
    · apply ExprLow.refines_renamePorts_well_formed
      assumption
      apply ExprLow.refines_renamePorts_well_formed
      assumption
      apply ExprLow.refines_subset_well_formed
      apply rw.consistent.2
      apply rw.wf.2
    · cases ‹some _ = some _›
      apply ExprLow.refines_renamePorts_well_formed
      assumption
      apply ExprLow.refines_subset_well_formed
      apply rw.consistent.2
      apply rw.wf.2
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
  · with_reducible split at ‹ite _ _ _ = _›
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
    · cases ‹some _ = some _›
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

-- theorem Rewrite_abstraction_correct {g g' : ExprHigh String} {s a c} :
--   Abstraction.run s g a = .ok (g', c) →
--   ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

-- theorem Rewrite_concretisation_correct {g g' : ExprHigh String} {s c} :
--   Concretisation.run s g c = .ok g' →
--   ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

-- theorem Rewrite_run_correct {g g' : ExprHigh String} {s rw} :
--   Rewrite.run s g rw = .ok g' →
--   ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

-- theorem rewrite_loop_correct {g g' : ExprHigh String} {s rws n} :
--   rewrite_loop s g rws n = .ok g' →
--   ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

end Graphiti
