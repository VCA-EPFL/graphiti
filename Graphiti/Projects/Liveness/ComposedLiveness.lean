/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier, Lorenzo Padrini
-/

import Graphiti.Core.ModuleLemmas
import Graphiti.Core.StateTransition
import Graphiti.Projects.Liveness.ComposedModule
import Graphiti.Projects.Liveness.StateTransitionLiveness
import Graphiti.Core.Trace

-- general liveness theorem sketch, as described in "Defining Liveness" paper
-- (∀α: α ∈ S* : (∃β : β ∈ Sω : αβ respects P))
-- theorem liveness (P : Trace → Prop)  :
--   α ∈ (List Trace) → ∃β : β ∈ Sω → P αβ := by
--     sorry


open Graphiti
open Graphiti.Module

/-
New approach: using behaviours is too limiting, I decided to do a secondary proof exclusively on star and prove behaviour
depending on it. For the moment it works well

-/
def gcompf_P {T} (t: Trace Nat)(f g: T → T) : Prop :=
  ∀ in1, .input 0 ⟨ T, in1 ⟩ ∈ t → .output 0 ⟨ T, g (f (in1)) ⟩ ∈ t


theorem gcompf_lemm_in {T f g}: ∀ t0 t s s0 e, (∀ x, .input 0 ⟨T, x⟩ ∉ t0)
→ gcompf_P (t ++ t0) f g
→ @star _ _ (state_transition (NatModule.gcompf T f g)) s t0 s0
→ gcompf_P (t ++ [.input 0 ⟨T, e⟩  ] ++ t0 ++ [.output 0 ⟨ T, g (f e) ⟩ ]) f g
:= by
  intro t0 t s s0 e prop compPrev star
  simp [gcompf_P] at *
  simp [prop] at compPrev
  intro in1 assum
  cases assum
  . rename_i p1
    have compEval := compPrev in1 p1
    cases compEval
    rename_i a
    left
    exact a
    rename_i a
    right; left
    exact a
  . rename_i a
    cases a
    rename_i subProp
    subst subProp
    right; right
    simp
    rename_i abs
    exfalso
    simp [prop] at abs



theorem gcompf_lemm_out {T f g}: ∀ t0 t s s0 e, (∀ x, .input 0 ⟨T, x⟩ ∉ t0)
→ gcompf_P (t ++ t0) f g
→ @star _ _ (state_transition (NatModule.gcompf T f g)) s t0 s0
→ ∃ t0', gcompf_P (t ++ [.output 0 ⟨ T, e ⟩] ++ t0') f g
∧ t0 = ([.output 0 ⟨ T, e ⟩] ++ t0'):= by
  intro t0 t1 s1 s0 e iProp star
  sorry






theorem gcompf_P_trans {T} (f g: T → T) (l1 l2 l3: List (IOEvent ℕ)): ((gcompf_P (l1 ++ (l3 ++ l2)) f g) ∧ ∀ (x : T), ¬IOEvent.input 0 ⟨T, x⟩ ∈ l3 ++ l2) → gcompf_P (l1 ++ l3) f g := by
  intro iH
  rcases iH with ⟨gcompf, empty⟩
  simp [gcompf_P] at *
  intro in1
  intro imp
  sorry


theorem input_not_in_conc_implies_inpup_not_in_list {T} (l1 l2: List (IOEvent ℕ)) : (∀ (x : T), ¬IOEvent.input 0 ⟨T, x⟩ ∈ l1 ++ l2) → (∀ (x : T), ¬IOEvent.input 0 ⟨T, x⟩ ∈ l1) ∧ (∀ (x : T), ¬IOEvent.input 0 ⟨T, x⟩ ∈ l2) := by
  intro iH
  simp at iH
  constructor
  . intro x
    have iHEval := iH x
    exact iHEval.left
  . intro x
    have iHEval := iH x
    exact iHEval.right

theorem gcompf_reachness_empty {T f g} : ∀ t s', @reachable _ _ (state_transition (NatModule.gcompf T f g)) t s'
→ ∀ s'' t0, ( ∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s' t0 s''
→ gcompf_P (t ++ t0) f g
→ ∀ s''', @step _ _ _ s' [] s'''
→ ∃ sn tn, gcompf_P (t ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s''' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  intro l1 s1 reachP s2 l2 emptyAndStar gcP s3 emptStep
  rcases emptyAndStar with ⟨empty, star⟩
  rcases emptStep
  rename_i arrow state2 arrowIsInternal arrowTrans
  simp [] at *
  have starConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 l2).mp star
  induction starConv
  . exists  { state := state2, module := s1.module }
    exists []
    constructor
    exact gcP
    simp at *
    clear empty
    have cc := @Graphiti.star.refl _ _ (state_transition (NatModule.gcompf T f g)) { state := state2, module := s1.module }
    exact cc
  . rename_i s3 s4 l3 l4 step starConv iH
    have star2 := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s3 l3).mpr starConv
    have imp := iH (@gcompf_P_trans T f g l1 l4 l3 (And.intro gcP empty))
    clear iH
    have iH := imp (@input_not_in_conc_implies_inpup_not_in_list  T l3 l4 empty).left star2
    rcases iH
    rename_i s5 iH
    rcases iH
    rename_i l5 iH
    clear imp
    rcases iH with ⟨iH1, iH2⟩
    exists s5
    exists l5



theorem gcompf_reachness_input {T f g} : ∀ t s', @reachable _ _ (state_transition (NatModule.gcompf T f g)) t s'
→ ∀ s'' t0, ( ∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s' t0 s''
→ gcompf_P (t ++ t0) f g
→ ∀ x s''', @step _ _ _ s' [IOEvent.input 0 ⟨T, x⟩] s'''
→ ∃ sn tn, gcompf_P (t ++ [IOEvent.input 0 ⟨T, x⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s''' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  intro l1 s1 reachP s2 l2  noInpiInL2 gcomfProp io s3 step
  sorry

/--
theorem gcompf_reachness_output { T f g} : ∀ t s', @reachable _ _ (state_transition (NatModule.gcompf T f g)) t  ⟨ s', (NatModule.gcompf T f g)⟩
→ ∀ s'' t0 ,( ∀ x, .input 0 ⟨T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s', (NatModule.gcompf T f g)⟩ t0 s''
→ gcompf_P (t ++ t0) f g
→ ∀ io s''', @step _ _ _ ⟨ s', (NatModule.gcompf T f g)⟩ [IOEvent.output 0 ⟨ T, io⟩]  s'''
→ ∃ sn tn, gcompf_P (t ++ [IOEvent.output 0 ⟨T, io ⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s''' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  intro l1 s1 reachP s2 l2 noInpiInL2 gcomfProp io s3 step
  cases step
  rename_i s' v a a'
  simp at *
  rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  sorry
-/
theorem gcompf_reachness_output { T f g} : ∀ t s', @reachable _ _ (state_transition (NatModule.gcompf T f g)) t  s'
→ ∀ s'' t0 ,( ∀ x, .input 0 ⟨T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s' t0 s''
→ gcompf_P (t ++ t0) f g
→ ∀ io s''', @step _ _ _ s' [IOEvent.output 0 ⟨ T, io⟩]  s'''
→ ∃ sn tn, gcompf_P (t ++ [IOEvent.output 0 ⟨T, io ⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s''' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  intro l1 s1 reachP s2 l2 noInpiInL2 gcomfProp io s3 step
  cases step
  rename_i s' v a a'
  simp at *
  rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  sorry


theorem gcompf_liveness_simp {t : Trace Nat} {T f g}
(h_in: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_out: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(s1 s2: State _ _)
(h: @StateTransition.init _ _ (state_transition (NatModule.gcompf T f g)) s1 ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s1 t s2):
  ∃ t' s3, gcompf_P (t ++ t') f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s2 t' s3 ∧ (∀ x, .input 0 ⟨T, x⟩ ∉ t'):= by
    have starConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 t).mp h.right
    induction starConv
    . exists []
      simp [gcompf_P]
      exists s1
      exact h.right
    . rename_i s3 s4 l1 l2 step star iH
      have starConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s3 l1).mpr star
      clear star
      simp at h_in h_out
      have h_in_new : (∀ (G : Type) (x : G) (n : InternalPort ℕ), IOEvent.input n ⟨G, x⟩ ∈ l1 → n = 0 ∧ G = T) := by {
        intro G x n exp
        have h_in_up := h_in G x n
        apply h_in_up
        constructor
        assumption
      }
      have h_out_new : (∀ (G : Type) (x : G) (n : InternalPort ℕ), IOEvent.output n ⟨G, x⟩ ∈ l1 → n = 0 ∧ G = T) := by {
        intro G x n exp
        have h_out_up := h_out G x n
        apply h_out_up
        constructor
        assumption
      }
      have iHRes := iH h_in_new h_out_new (And.intro h.left starConv)
      clear iH
      cases iHRes
      rename_i tr iH
      cases iH
      rename_i s5 iH
      have keepStep := step
      cases step
      . rename_i IntN LTPair s3Fst TT s3Snd TTEq
        have finalRes := @gcompf_reachness_input T f g l1 s3
        simp [reachable] at finalRes
        have finalResT := finalRes s1 h.left starConv s5 tr iH.right.right iH.right.left iH.left
        cases TT
        rename_i TT inp
        have h_in_assum := h_in TT inp IntN
        simp at h_in_assum
        clear finalRes
        rcases h_in_assum with ⟨ nEq, TypeEq ⟩
        subst nEq
        subst TypeEq
        have finalRes := finalResT inp { state := LTPair, module := s3.module } keepStep
        cases finalRes
        rename_i s4 finalRes
        cases finalRes
        rename_i tn final
        exists tn
        exists s4
        simp at *
        exact final
      . rename_i IntN LTPair s3Fst TT s3Snd TTEq
        have finalRes :=@ gcompf_reachness_output T f g l1 s3
        simp [reachable] at finalRes
        have finalResT := finalRes s1 h.left starConv s5 tr iH.right.right iH.right.left iH.left
        cases TT
        rename_i TT inp
        have h_out_assum := h_out TT inp IntN
        simp at h_out_assum
        clear finalRes
        rcases h_out_assum with ⟨ nEq, TypeEq ⟩
        subst nEq
        subst TypeEq
        have finalRes := finalResT inp { state := LTPair, module := s3.module } keepStep
        cases finalRes
        rename_i s4 finalRes
        cases finalRes
        rename_i tn final
        exists tn
        exists s4
        simp at *
        exact final
      . rename_i RelTT LtLt RelTTInt RelTTState
        have finalRes :=@ gcompf_reachness_empty T f g l1 s3
        simp [reachable] at finalRes
        have finalResT := finalRes s1 h.left starConv s5 tr iH.right.right iH.right.left iH.left
        clear finalRes
        have finalRes := finalResT { state := LtLt, module := s3.module } keepStep
        cases finalRes
        rename_i s4 finalRes
        cases finalRes
        rename_i tn final
        exists tn
        exists s4
        simp at *
        exact final




theorem gcompf_liveness2 {t : Trace Nat} {T f g}(h_steps: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t)
(h_in: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_out: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T)):
  ∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') ∧ ∀ x, .input 0 ⟨T, x⟩ ∉ t' := by
    simp [behaviour] at h_steps
    cases h_steps
    rename_i s1 beh
    cases beh
    rename_i p1 beh
    cases beh
    rename_i s2 star
    have mainProof := gcompf_liveness_simp h_in h_out s1 s2 (And.intro p1 star)
    cases mainProof
    rename_i t' mainProof
    cases mainProof
    rename_i s3 mainProof
    exists t'
    constructor
    . exact mainProof.left
    . constructor
      . simp [behaviour]
        have starComb := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 s3 t t' mainProof.right.left
        exists s1
        constructor
        . exact p1
        . exists s3
      . exact mainProof.right.right
