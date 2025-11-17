/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier
-/

import Graphiti.Core.Module
import Graphiti.Core.AssocList.Basic
import Graphiti.Core.Trace

namespace Graphiti.NatModule

-- g ∘ f. state = (f(in), g(f(in)), trace_history [new, old])
@[drunfold, drcomponents] def gcompfHist (T : Type)(f g : T -> T) : NatModule ((List T) × (List T) × (Trace Nat)) :=
  {
    inputs := [(0, ⟨ T, λ s tt s' => s' = (s.fst.concat (f tt), s.snd.fst, (.input 0 ⟨T, tt⟩) :: s.snd.snd) ⟩)].toAssocList,
    internals := [λ s s' => s' = (∅, s.snd.fst ++ s.fst.map g, s.snd.snd)],
    outputs := [(0, ⟨ T, λ s tt s' => (s.fst, s.snd.fst, (.output 0 ⟨T, tt⟩) :: s.snd.snd) = (s'.fst, tt :: s'.snd.fst, s'.snd.snd) ⟩)].toAssocList,
    init_state := λ s => s = ([], [], []),
  }

-- def gfmodule : NatModule (List Nat) := gcompf Nat (fun a => a + 1) (fun a => a + 1)

end Graphiti.NatModule
