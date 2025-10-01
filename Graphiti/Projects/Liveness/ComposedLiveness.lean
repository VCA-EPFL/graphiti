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

theorem gcompf_reachness {T f g} : ∀ s t, @reachable _ _ (state_transition (NatModule.gcompf T f g)) t s
  → ∃ t' s', @star _ _ (state_transition s.module) s t s'
  → ∀ x, ∃ t0, .input 0 ⟨ T, x ⟩ ∉ t0
  → ∃ s'', gcompf_P (t ++ t' ++ t0) f g ∧ @star _ _ (state_transition s.module) s t0 s''
  → ∀ e, @star _ _ (state_transition s.module) s' [e] s''
  → ∃ sn tn,gcompf_P (t ++ t' ++ [e] ++ tn) f g ∧ @star _ _ (state_transition s.module) s'' tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by sorry

-- if 0 steps holds, if n steps have to check the reachabilty + */// lemmas: is input included, is output included
-- with module gcompf, if "in1" in trace α, then there exist a β where eventually "out1 = g∘f(in1)" in trace αβ
theorem gcompf_liveness {t : Trace Nat} {T f g} (h_steps: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t)  :
  ∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') ∧ ∀ x, .input 0 ⟨T, x⟩ ∉ t' := by
    cases h_steps
    rename_i s1 behUnfolded
    cases behUnfolded
    rename_i s2 behUnfolded
    have starRevConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 t).mp behUnfolded.right
    induction starRevConv
    . exists []
      simp [behaviour, gcompf_P] at *
      exists s1
      constructor
      . exact behUnfolded.left
      . exists s1
        exact behUnfolded.right
    . rename_i s3 s4 s5 l1 l2 stepP starP
      sorry
