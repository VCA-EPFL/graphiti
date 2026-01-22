/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier, Lorenzo Padrini
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.StateTransition
import Graphiti.Projects.Liveness.ComposedModuleHist
import Graphiti.Projects.Liveness.StateTransitionLiveness
import Graphiti.Core.Trace


open Graphiti

-- Calc #inputs - #outputs in history
def count_in_out (history : List (IOEvent Nat)) : Nat :=
  history.foldl (fun acc event =>
    match event with
    | IOEvent.input _ _ => acc + 1
    | IOEvent.output _ _ => acc - 1
  ) 0

def gcompfHistWeight {T} {f g : T -> T} (s : Graphiti.Module.State Nat ((List T) × ((List T) × (Trace Nat)))) : Nat :=
  let s_stt := s.state;
  2 * List.length s_stt.fst + List.length s_stt.snd.fst + count_in_out s_stt.snd.snd
