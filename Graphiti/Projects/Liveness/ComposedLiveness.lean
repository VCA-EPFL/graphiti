/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier
-/

import Graphiti.Core.ModuleLemmas
import Graphiti.Core.StateTransition
import Graphiti.Projects.Liveness.ComposedModule
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
  ∧ .output ⟨ T, g (f x) ⟩ ∈ t'
  ∧ s' = (∅, ∅) := by
    intros x s h
    have ⟨ h1, h2 ⟩ := h
    -- step internal, get s2 with internal state (∅, ∀x∈s -> g(f(x)))
    have h_int: ∃ s2, step s [] ⟨s2, s.module⟩ := by rw [h1]; sorry -- use h2
    -- step output
    have h_out: ∃ s3 v', step s [.output v'] ⟨s3, s.module⟩ := by sorry
    -- gotta prove that v' = g(f(x)) and that s3 = s'
    sorry


lemma gcompfp_lemma2 {t t': List Trace} {T f g} : -- rename it to `gcompf_stuck_input` ?
  ∀ x (s: State _ _) s', s.module = (NatModule.gcompf T f g)
  -- ∧ @reachable _ _ (state_transition s.module) t' s
  ∧ @star _ _ (state_transition s.module) s t s'
  ∧ .input ⟨ T, x ⟩ ∈ t ∧ .output ⟨ T, g (f x) ⟩ ∉ t
  → (f x) ∈ s.state.fst ∨ g (f x) ∈ s.state.snd := by
    sorry


-- if some input `x` was fed to g∘f module, but output `g(f(x))` is not out, then `x` is currently *in* the module, either in the first list (as `f(x)`) or in the second list (as `g(f(x))`)
lemma gcompfp_lemma {t t0: List Trace} {T f g} : -- rename it to `gcompf_stuck_input` ?
  ∀ x (s: State _ _) s', @star _ _ (state_transition s.module) s t s'
  → s.module = (NatModule.gcompf T f g)
  → @reachable _ _ (state_transition s.module) t0 s
  → .input ⟨ T, x ⟩ ∈ (t0 ++ t) → .output ⟨ T, g (f x) ⟩ ∉ (t0 ++ t)
  → (f x) ∈ s.state.fst ∨ g (f x) ∈ s.state.snd := by
    -- try to get away from beh asap, so you don't have to start at init state which is empty since we can't induct over that
    intros x s s' h
    revert x t0
    generalize heq: state_transition s.module = n at * -- will need to prove that module stays constant (exist lemma)
    induction h
    case refl => sorry
    case step => sorry

    -- obtain ⟨ h_mod, h_behv, h_in, h_out ⟩ := h
    -- rcases h_behv with ⟨ s0, s', h_init, h_star ⟩
    -- -- unfold StateTransition.init at h_init;
    -- revert h_init h_in h_out h_mod x
    -- induction h_star
    -- case intro.intro.intro.refl s1 =>
    --   exfalso
    --   absurd h_in
    --   exact List.not_mem_nil
    -- case intro.intro.intro.step s1 s2 s3 t1 t2 step1 star2 ih =>



def gcompf_P {T} (t: List Trace)(f g: T → T) : Prop :=
  ∀ in1, .input ⟨ T, in1 ⟩ ∈ t → .output ⟨ T, g (f (in1)) ⟩ ∈ t


-- maibye try doing reachability + star on main theorem if stuck

-- if 0 steps holds, if n steps have to check the reachabilty + */// lemmas: is input included, is output included
-- with module gcompf, if "in1" in trace α, then there exist a β where eventually "out1 = g∘f(in1)" in trace αβ
theorem gcompf_liveness {t : List Trace} {T f g} (h_steps: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t) (h_in: ∃ in1, .input ⟨ T, in1 ⟩ ∈ t) : --TODO: remove h_in
  ∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') := by
    -- check behavior and check that init works then that star works
    -- but ppty we're trying to prove is not inductive so it'll be problematic to prove
    -- try to transform the ppty into an "inductive one" -> either out is already in t, or it's in the module : then it's either in the left list and can be processed through internal rule then output, or it's in the right list and can be output
    -- lemma to prove to prove this big thm:
    -- beh of t ∧ inp x ∈ t ∧ out g(f(x)) ∉ t → f(x) ∈ gf.s.1 ∨ g(f(x)) ∈ gf.s.2 --try to get away from beh asap, so you don't have to start at init state which is empty since we can't induct over that
    -- f(x) ∈ gf.s.1 → ∃ t' s', s -t'-*-> s' ∧ out g(f(x)) ∈ t ∧ s' = (∅, ∅)
  -- OOOK I am used to do the bottom up but here makes more sense to have a top down approach to keep objectives in mind
  have h_beh := h_steps
  simp [behaviour] at h_steps --opening the internals of the inductive hypotesis
  cases h_steps -- removng the existentials that bothers
  rename_i s1 iH
  -- Opening the two informations given from the behaviour
  cases iH
  rename_i initProp starProp
  -- Removing the existential from the star prop
  cases starProp
  rename_i s2 trans
  -- proving that an input has been inserted
  cases h_in
  rename_i x xInT
  cases initProp
  rename_i init_mod modNat
  -- induce over *, show that P is inductive (P s and s →* s' then P s')
  by_cases ¬ .output ⟨T, g (f x)⟩ ∈ t
  . rename_i notOutput
    -- have lemma1 := gcompfp_lemma t f g x s1
    -- simp [modNat, xInT, h_beh, notOutput] at lemma1
    -- have lemma2 := gcompf_flushability f g x
    sorry
  . rename_i outputInT
    simp at outputInT
    exists []
    simp [gcompf_P, behaviour]
    constructor
    . intro in1 tInT
      sorry
    . sorry







  /-
  constructor
  . constructor
    . sorry
    . simp [behaviour]
      simp [behaviour] at h_steps
      cases h_steps
      rename_i s iH
      exists s
      constructor
      . apply And.left iH
      . have rightSide := And.right iH
        cases rightSide
        rename_i x trans
        constructor-/







-- end NatModule
-- end Module
