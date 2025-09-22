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

#check NatModule.gfmodule


lemma gcompfp_lemma {t: List Trace} {T f g} :
∀ x, @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t ∧ .input ⟨T, x⟩ ∈ t ∧ .output ⟨ T, g (f x) ⟩ ∉ t
→ (f x) ∈ NatModule.gcompf.inputs ∨ g (f x) ∈ Natmodule.gfmodule.outputs:= by sorry

def gcompfP {T} (t: List Trace)(f g: T → T) : Prop :=
  ∀ in1 , .input ⟨ T, in1 ⟩ ∈ t → .output ⟨ T, g (f (in1)) ⟩ ∈ t

-- with module gcompf, if "in1" in trace α, then there exist a β where eventually "out1 = g∘f(in1)" in trace αβ
-- theorem gcompf_liveness {i1 e i2} (module : Graphiti.NatModule.gcompf) (h: @star _ _ (state_transition imp) i1 e i2) :
-- theorem gcompf_liveness {i1 t i2}(h: @star _ _ (state_transition imp) i1 t i2) :
-- theorem gcompf_liveness {i1 t i2} (module : NatModule.gfmodule) (h: @star _ _ (state_transition module) i1 t i2) : -- use behavior instead
theorem gcompf_liveness {t : List Trace} {T f g} (h: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t) :
  -- ∀ t in1, t = (valid List Trace) → in1 ∈ t → (∃ out1, out1 = g(f(in1)), out1 ∈ t')
  -- ∀ in1, in1 ∈ t → out1 ∉ t → ∃ t', out1 ∈ t' -- with out1 = g(f(in1))
  -- ∀ in1, in1 ∈ t → module.g(module.f(in1)) ∉ t → ∃ t', out1 ∈ t' -- with out1 = g(f(in1))
  -- ∀ in1, in1 ∈ t → module.outputs ∉ t → ∃ t', out1 ∈ t' :=
  ∃ t', gcompfP (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') :=
    -- check behavior and check that init works then that star works
    -- but ppty we're trying to prove is not inductive so it'll be problematic to prove
    -- try to transform the ppty into an "inductive one" -> either out is already in t, or it's in the module : then it's either in the left list and can be processed through internal rule then output, or it's in the right list and can be output
    -- lemma to prove to prove this big thm
    -- beh of t ∧ inp x ∈ t ∧ out g(f(x)) ∉ t → f(x) ∈ gf.s.1 ∨ g(f(x)) ∈ gf.s.2 --try to get away from beh asap, so you don't have to start at init state which is empty since we can't induct over that
    -- f(x) ∈ gf.s.1 → ∃ t' s', s -t'-*-> s' ∧ out g(f(x)) ∈ t ∧ s' = (∅, ∅)
    sorry


-- end NatModule
-- end Module
