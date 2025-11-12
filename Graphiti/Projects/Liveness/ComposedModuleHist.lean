/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier
-/

import Graphiti.Core.Module
import Graphiti.Core.AssocList.Basic

namespace Graphiti.NatModule

-- g ∘ f. state = (f(in), g(f(in)), trace_history)
@[drunfold, drcomponents] def gcompf (T : Type)(f g : T -> T) : NatModule ((List T) × (List T) × (List T)) :=
  {
    inputs := [(0, ⟨ T, λ s tt s' => s' = (s.fst.concat (f tt), s.snd.fst, tt :: s.snd.snd) ⟩)].toAssocList,
    internals := [λ s s' => s' = (∅, s.snd.fst ++ s.fst.map g, s.snd.snd)],
    outputs := [(0, ⟨ T, λ s tt s' => (s.fst, s.snd.fst, tt :: s.snd.snd) = (s'.fst, tt :: s'.snd.fst, s'.snd.snd) ⟩)].toAssocList,
    init_state := λ s => s = ([], [], []),
  }

-- def gfmodule : NatModule (List Nat) := gcompf Nat (fun a => a + 1) (fun a => a + 1)

end Graphiti.NatModule
