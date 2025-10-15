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
open List
-- namespace Module
-- namespace NatModule

-- #check NatModule.gfmodule

-- if `f(x)` is in the module, then it can be output (through steps `t'`, leading to new state `s'` which is empty)
/-
lemma gcompf_flushability {T} (f g: T → T):
  ∀ (x: T) (s: State _ _), s.module = (NatModule.gcompf T f g) ∧ (f x) ∈ s.state.fst
  → ∃ t' s', (@star _ _ (state_transition s.module) ⟨s.state,  s.module⟩ t' ⟨s', s.module⟩)
  ∧ .output 0 ⟨ T, g (f x) ⟩ ∈ t'
  ∧ s' = (∅, ∅) := by
    intros x s h
    have ⟨ h1, h2 ⟩ := h
    -- step internal, get s2 with internal state (∅, ∀x∈s -> g(f(x)))
    have h_int: ∃ s2, step s [] ⟨s2, s.module⟩ := by rw [h1]; sorry -- use h2
    -- step output
    have h_out: ∃ s3 v', step s [.output 0 v'] ⟨s3, s.module⟩ := by sorry
    -- gotta prove that v' = g(f(x)) and that s3 = s'
    sorry


lemma gcompfp_lemma2 {t t': Trace Nat} {T f g} : -- rename it to `gcompf_stuck_input` ?
  ∀ x (s: State _ _) s', s.module = (NatModule.gcompf T f g)
  -- ∧ @reachable _ _ (state_transition s.module) t' s
  ∧ @star _ _ (state_transition s.module) s t s'
  ∧ .input 0 ⟨ T, x ⟩ ∈ t ∧ .output 0 ⟨ T, g (f x) ⟩ ∉ t
  → (f x) ∈ s.state.fst ∨ g (f x) ∈ s.state.snd := by
    sorry

-- if some input `x` was fed to g∘f module, but output `g(f(x))` is not out, then `x` is currently *in* the module, either in the first list (as `f(x)`) or in the second list (as `g(f(x))`)
lemma gcompfp_lemma {t t0: Trace Nat} {T f g} : -- rename it to `gcompf_stuck_input` ?
  ∀ x (s: State _ _) s', @star _ _ (state_transition s.module) s t s'
  → s.module = (NatModule.gcompf T f g)
  → @reachable _ _ (state_transition s.module) t0 s
  → .input 0 ⟨ T, x ⟩ ∈ (t0 ++ t) → .output 0 ⟨ T, g (f x) ⟩ ∉ (t0 ++ t)
  → (f x) ∈ s.state.fst ∨ g (f x) ∈ s.state.snd := by
    -- try to get away from beh asap, so you don't have to start at init state which is empty since we can't induct over that
    intros x s s' h
    revert x t0
    generalize heq: state_transition s.module = n at * -- will need to prove that module stays constant (exist lemma)
    induction h
    case refl => sorry
    case step => sorry





def gcompf_P {T} (t: Trace Nat)(f g: T → T) : Prop :=
  ∀ in1, .input 0 ⟨ T, in1 ⟩ ∈ t → .output 0 ⟨ T, g (f (in1)) ⟩ ∈ t

--theorem gcompf_inp {T f g} : ∀ t t0 x, .input 0 ⟨T, x ⟩ ∉ t0 ∧ gcompf_P (t ++ t0) f g ∧ ∃ s s0, @star _ _ (state_transition s.module) s t0 s0
--:= by sorry

theorem gcompf_reachness {T f g} : ∀ t s s', @star _ _ (state_transition (NatModule.gcompf T f g)) s t s'
  → ∀ t0, (∀ x, .input 0 ⟨ T, x ⟩ ∉ t0)
  → gcompf_P (t ++ t0) f g
  → ∀ e s'', @star _ _ (state_transition (NatModule.gcompf T f g)) s' [e] s''
  → ∃ sn tn,gcompf_P (t ++ [e] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s'' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by sorry


-- if 0 steps holds, if n steps have to check the reachabilty + */// lemmas: is input included, is output included
-- with module gcompf, if "in1" in trace α, then there exist a β where eventually "out1 = g∘f(in1)" in trace αβ
theorem gcompf_liveness {t : Trace Nat} {T f g} (h_steps: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t)  :
  ∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') ∧ ∀ x, .input 0 ⟨T, x⟩ ∉ t' := by
    cases h_steps
    rename_i s1 behUnfolded
    have helpNext := (s1.module.state_transition = (state_transition (NatModule.gcompf T f g)))
    cases behUnfolded
    rename_i s2 behUnfolded
    have starRevConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 t).mp behUnfolded.right
    induction starRevConv
    . exists []
      simp [gcompf_P]
      exists s1
      exists s1
    . rename_i s3 s4 l1 l2 stepP starP iH
      have starConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s3 l1).mpr starP
      have iHEval := iH (And.intro behUnfolded.left starConv)
      cases iHEval
      clear iH
      rename_i l2 iH
      have stepPP := stepP
      cases stepP
      . rename_i ip LxL firstInputV firstInputTpe secondInputV firstInputEq
        have behConv := iH.right.left
        simp [behaviour_tight] at behConv
        cases behConv
        rename_i s4 behConv
        cases behConv
        rename_i s5 behConv
        cases behConv
        rename_i stateInits5 cc
        have lemmaUse :=  @gcompf_reachness T f g
        simp [reachable] at lemmaUse
        have stepToStar := @star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) s3 ({ state := LxL, module := s3.module }) ([IOEvent.input ip firstInputTpe]) stepPP
        have lemmaUse1 := lemmaUse l1 s1 s3 starConv l2 iH.right.right iH.left (IOEvent.input ip firstInputTpe) ({ state := LxL, module := s3.module }) stepToStar
        cases lemmaUse1
        rename_i s6 lemma1
        cases lemma1
        rename_i l3 indLemma
        exists l3
        constructor
        . simp at *
          exact indLemma.left
        . constructor
          . simp [behaviour]
            exists s1
            constructor
            . exact behUnfolded.left
            . clear lemmaUse
              exists s6
              have firstSteps := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) s1 s3 ({ state := LxL, module := s3.module }) l1 [IOEvent.input ip firstInputTpe] starConv
              have firstSteps1 := firstSteps stepToStar
              have secondSteps := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) s1 { state := LxL, module := s3.module } s6 (l1 ++ [IOEvent.input ip firstInputTpe]) l3 firstSteps1 indLemma.right.left
              simp at *
              assumption
          . exact indLemma.right.right
      . rename_i ip LxL firstInputV firstInputTpe secondInputV firstInputEq
        have behConv := iH.right.left
        simp [behaviour_tight] at behConv
        cases behConv
        rename_i s4 behConv
        cases behConv
        rename_i s5 behConv
        cases behConv
        rename_i stateInits5 cc
        have lemmaUse :=  @gcompf_reachness T f g
        simp [reachable] at lemmaUse
        have stepToStar := @star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) s3 ({ state := LxL, module := s3.module }) ([IOEvent.output ip firstInputTpe]) stepPP
        have lemmaUse1 := lemmaUse l1 s1 s3 starConv l2 iH.right.right iH.left (IOEvent.output ip firstInputTpe) ({ state := LxL, module := s3.module }) stepToStar
        cases lemmaUse1
        rename_i s6 lemma1
        cases lemma1
        rename_i l3 indLemma
        exists l3
        constructor
        . simp at *
          exact indLemma.left
        . constructor
          . simp [behaviour]
            exists s1
            constructor
            . exact behUnfolded.left
            . clear lemmaUse
              exists s6
              have firstSteps := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) s1 s3 ({ state := LxL, module := s3.module }) l1 [IOEvent.output ip firstInputTpe] starConv
              have firstSteps1 := firstSteps stepToStar
              have secondSteps := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) s1 { state := LxL, module := s3.module } s6 (l1 ++ [IOEvent.output ip firstInputTpe]) l3 firstSteps1 indLemma.right.left
              simp at *
              assumption
          . exact indLemma.right.right
      . rename_i RLL LL RLLInS3 RLLS
        exists l2
        simp at *
        assumption
-/



/-
New approach: using behaviours is too limiting, I decided to do a secondary proof exclusively on star and prove behaviour
depending on it. For the moment it works well

-/
def gcompf_P {T} (t: Trace Nat)(f g: T → T) : Prop :=
  ∀ in1, .input 0 ⟨ T, in1 ⟩ ∈ t → .output 0 ⟨ T, g (f (in1)) ⟩ ∈ t

/-
if t1 respects P and t2 respects P then t1++t2 respects P
-/
theorem gcompf_P_concat {T}(f g: T → T):
  ∀ t0 t1, gcompf_P t0 f g ∧ gcompf_P t1 f g → gcompf_P (t0++t1) f g := by
    intros t0 t1 h
    unfold gcompf_P at *
    have ⟨ h1, h2 ⟩ := h
    intros in1 h_in_concat
    -- List.mem_append : a ∈ L₁ ++ L₂ ↔ a ∈ L₁ ∨ a ∈ L₂
    rcases (mem_append.mp h_in_concat) with h_in_t0 | h_in_t1
    case inl =>
      have h_out_t0 : IOEvent.output 0 ⟨T, g (f in1)⟩ ∈ t0 := h1 in1 h_in_t0
      exact mem_append_left t1 h_out_t0
    case inr =>
      have h_out_t1 : IOEvent.output 0 ⟨T, g (f in1)⟩ ∈ t1 := h2 in1 h_in_t1
      exact mem_append_right t0 h_out_t1


theorem gcompf_lemm_in {T f g}: ∀ t0 t s s0 e, (∀ x, .input 0 ⟨T, x⟩ ∉ t0)
→ gcompf_P (t ++ t0) f g
→ @star _ _ (state_transition (NatModule.gcompf T f g)) s t0 s0
→ gcompf_P (t ++ [.input 0 ⟨T, e⟩ ] ++ t0 ++ [.output 0 ⟨ T, g (f e) ⟩ ]) f g -- why is t0 in between the in and out? is it useful ?
  := by
    intros t1 t0 s0 s1 e h_noInpInT1 h_concatP h_star
    -- gcompf_P_concat
    simp [gcompf_P, h_noInpInT1] at *
    intro x h_x
    cases h_x
    case inl h =>
      have h1 := h_concatP x h
      cases h1
      case inl h2 =>
        exact Or.inl h2
      case inr h2 =>
        refine or_assoc.mp ?_
        exact Or.intro_left (g (f x) = g (f e)) (h_concatP x h)
    case inr h =>
      rw [h]
      right
      right
      rfl

-- the module is deterministic
theorem gcompf_lemm_out {T f g}: ∀ t0 t s s0 e, (∀ x, .input 0 ⟨T, x⟩ ∉ t0)
→ gcompf_P (t ++ t0) f g
→ @star _ _ (state_transition (NatModule.gcompf T f g)) s t0 s0
→ ∃ t0', gcompf_P (t ++ [.output 0 ⟨ T, e ⟩] ++ t0') f g
∧ t0 = ([.output 0 ⟨ T, e ⟩] ++ t0'):= by sorry

theorem gcompf_reachness_empty {T f g} : ∀ t s', @reachable _ _ (state_transition (NatModule.gcompf T f g)) t s'
→ ∀ s'' t0, ( ∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s' t0 s''
→ gcompf_P (t ++ t0) f g
→ ∀ s''', @star _ _ (state_transition (NatModule.gcompf T f g)) s' [] s'''
→ ∃ sn tn, gcompf_P (t ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s''' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by sorry


theorem gcompf_reachness_elem {T f g} : ∀ t s', @reachable _ _ (state_transition (NatModule.gcompf T f g)) t s'
→ ∀ s'' t0, ( ∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s' t0 s''
→ gcompf_P (t ++ t0) f g
→ ∀ e s''', @step _ _ _ s' [e] s'''
→ ∃ sn tn, gcompf_P (t ++ [e] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s''' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  intro l1 s1 reachP s2 l2 noInpiInL2 gcomfProp io s3 step
  cases step
  . rename_i Ip currState s1Fst tt s1Snd s1FstEq
    rw [s1FstEq]
    cases tt
    rename_i T e
    injection s1FstEq with h_fst h_snd
    sorry
  . sorry



theorem gcompf_reachness_input {T f g} : ∀ t s', @reachable _ _ (state_transition (NatModule.gcompf T f g)) t s'
→ ∀ s'' t0, ( ∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s' t0 s''
→ gcompf_P (t ++ t0) f g
→ ∀ x s''', @step _ _ _ s' [.input 0 ⟨ T, x ⟩] s'''
→ ∃ sn tn, gcompf_P (t ++ [.input 0 ⟨ T, x ⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s''' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by

  sorry

theorem gcompf_reachness_output {T f g} : ∀ t s', @reachable _ _ (state_transition (NatModule.gcompf T f g)) t s'
→ ∀ s'' t0, ( ∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s' t0 s''
→ gcompf_P (t ++ t0) f g
→ ∀ x s''', @step _ _ _ s' [.output 0 ⟨ T, x ⟩] s'''
→ ∃ sn tn, gcompf_P (t ++ [.output 0 ⟨ T, x ⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s''' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by sorry



-- diff with liveness: steps for given s1 s2 & ∃s3, s2-[t']*>s3 instead of behavior (t++t')
theorem gcompf_liveness_simp {t : Trace Nat} {T f g} (s1 s2: State _ _) (h: @StateTransition.init _ _ (state_transition (NatModule.gcompf T f g)) s1 ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s1 t s2):
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
      have iHRes := iH (And.intro h.left starConv)
      clear iH
      cases iHRes
      rename_i tr iH
      cases iH
      rename_i s5 iH
      have keepStep := step
      cases step
      . rename_i IntN LTPair s3Fst TT s3Snd TTEq
        have finalRes :=@ gcompf_reachness_elem T f g l1 s3
        simp [reachable] at finalRes
        generalize pq: IOEvent.input IntN TT = io at *
        have finalResT := finalRes s1 h.left starConv s5 tr iH.right.right iH.right.left iH.left io
        clear finalRes
        have finalRes := finalResT { state := LTPair, module := s3.module } keepStep
        cases finalRes
        rename_i s4 finalRes
        cases finalRes
        rename_i tn final
        exists tn
        exists s4
        simp at *
        exact final
      . rename_i IntN LTPair s3Fst TT s3Snd TTEq
        have finalRes :=@ gcompf_reachness_elem T f g l1 s3
        simp [reachable] at finalRes
        generalize pq: IOEvent.output IntN TT = io at *
        have finalResT := finalRes s1 h.left starConv s5 tr iH.right.right iH.right.left iH.left io
        clear finalRes
        have stepToStar := @star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) s3 ({ state := LTPair, module := s3.module }) ([io]) keepStep
        have finalRes := finalResT { state := LTPair, module := s3.module } keepStep
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
        have stepToStar := @star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) s3 ({ state := LtLt, module := s3.module }) [] keepStep
        have finalRes := finalResT { state := LtLt, module := s3.module } stepToStar
        cases finalRes
        rename_i s4 finalRes
        cases finalRes
        rename_i tn final
        exists tn
        exists s4
        simp at *
        exact final




theorem gcompf_liveness2 {t : Trace Nat} {T f g} (h_steps: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t)  :
  ∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') ∧ ∀ x, .input 0 ⟨T, x⟩ ∉ t' := by
    simp [behaviour] at h_steps
    cases h_steps
    rename_i s1 beh
    cases beh
    rename_i p1 beh
    cases beh
    rename_i s2 star
    have mainProof := gcompf_liveness_simp s1 s2 (And.intro p1 star)
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
