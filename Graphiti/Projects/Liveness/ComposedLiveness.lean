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
-- namespace Module
-- namespace NatModule

-- #check NatModule.gfmodule

-- if `f(x)` is in the module, then it can be output (through steps `t'`, leading to new state `s'` which is empty)
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
