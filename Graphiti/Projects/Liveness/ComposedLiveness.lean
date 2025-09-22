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
lemma gcompf_flushability {T} {f g: T → T}:
  ∀ (x: T) (s: State _ _), s.module = (NatModule.gcompf T f g) ∧ (f x) ∈ s.state.fst
  → ∃ t' s', (@star _ _ (state_transition s.module) ⟨s.state,  s.module⟩ t' ⟨s', s.module⟩)
  ∧ .output ⟨ T, g (f x) ⟩ ∈ t'
  ∧ s' = (∅, ∅) := by
    sorry

-- if some input `x` was fed to g∘f module, but output `g(f(x))` is not out, then `x` is currently *in* the module, either in the first list (as `f(x)`) or in the second list (as `g(f(x))`)
lemma gcompfp_lemma {t: List Trace} {T f g} : -- rename it to `gcompf_stuck_input` ?
  ∀ x (s: State _ _), s.module = (NatModule.gcompf T f g)
  ∧  @behaviour _ _ (state_transition s.module) t
  ∧ .input ⟨ T, x ⟩ ∈ t ∧ .output ⟨ T, g (f x) ⟩ ∉ t
  → (f x) ∈ s.state.fst ∨ g (f x) ∈ s.state.snd := by
    -- try to get away from beh asap, so you don't have to start at init state which is empty since we can't induct over that
    sorry

def gcompf_P {T} (t: List Trace)(f g: T → T) : Prop :=
  ∀ in1, .input ⟨ T, in1 ⟩ ∈ t → .output ⟨ T, g (f (in1)) ⟩ ∈ t

-- with module gcompf, if "in1" in trace α, then there exist a β where eventually "out1 = g∘f(in1)" in trace αβ
theorem gcompf_liveness {t : List Trace} {T f g} (h_steps: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t) (h_in: ∀in1, .input ⟨ T, in1 ⟩ ∈ t) :
  ∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') :=
    -- check behavior and check that init works then that star works
    -- but ppty we're trying to prove is not inductive so it'll be problematic to prove
    -- try to transform the ppty into an "inductive one" -> either out is already in t, or it's in the module : then it's either in the left list and can be processed through internal rule then output, or it's in the right list and can be output
    -- lemma to prove to prove this big thm:
    -- beh of t ∧ inp x ∈ t ∧ out g(f(x)) ∉ t → f(x) ∈ gf.s.1 ∨ g(f(x)) ∈ gf.s.2 --try to get away from beh asap, so you don't have to start at init state which is empty since we can't induct over that
    -- f(x) ∈ gf.s.1 → ∃ t' s', s -t'-*-> s' ∧ out g(f(x)) ∈ t ∧ s' = (∅, ∅)

    sorry


-- end NatModule
-- end Module
