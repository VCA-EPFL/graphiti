/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier, Lorenzo Padrini
-/

import Graphiti.Core.ModuleLemmas
import Graphiti.Core.StateTransition
import Graphiti.Projects.Liveness.ComposedModuleHist
import Graphiti.Projects.Liveness.StateTransitionLiveness
import Graphiti.Core.Trace


open Graphiti
open Graphiti.Module


-- COMPUTATION: different functions to compute the weight of the state

-- Calc #inputs - #outputs in history
def count_in_out (history : List (IOEvent Nat)) : Nat :=
  history.foldl (fun acc event =>
    match event with
    | IOEvent.input _ _ => acc + 1
    | IOEvent.output _ _ => acc - 1
  ) 0

def gcompfHistWeight {T} (f g : T -> T) (s : Graphiti.Module.State Nat ((List T) × ((List T) × (Trace Nat)))) : Nat :=
  let s_stt := s.state;
  2 * List.length s_stt.fst + List.length s_stt.snd.fst + count_in_out s_stt.snd.snd


--PROPERTIES: properties that need to be followed at various stages of the proof for the system to be live

def gcompf_P {T} (t: Trace Nat)(f g: T → T) : Prop :=
  ∀ in1, .input 0 ⟨ T, in1 ⟩ ∈ t → .output 0 ⟨ T, g (f (in1)) ⟩ ∈ t

def gcompf_wf_P {T} (f g: T → T) (z: Nat) :=
   ∀ (s: Graphiti.Module.State ℕ (List T × List T × Trace Nat)), @gcompfHistWeight _ f g s = z
   → (∃ t, @reachable _ _  (Module.state_transition (NatModule.gcompfHist T f g)) t s)
   → ∃ s' t0, (@gcompfHistWeight _ f g s' = 0) ∧  @star _ _ (Module.state_transition (NatModule.gcompfHist T f g)) s t0 s' ∧ ∀ io n, (IOEvent.input io n) ∉ t0
