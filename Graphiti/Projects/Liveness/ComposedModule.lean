/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier
-/

import Graphiti.Core.Module
import Graphiti.Core.AssocList.Basic

namespace Graphiti.NatModule

-- g ∘ f
@[drunfold, drcomponents] def gcompf (T : Type)(f g : T -> T) : NatModule (List T) :=
  {
    inputs := [(0, ⟨ T, λ s tt s' => s' = s.concat (f tt) ⟩)].toAssocList,
    internals := [λ s s' => s' = (s.map g)], -- could apply infinitely g -- should have two list with f(x) and one with g(f(x))
    outputs := [(0, ⟨ T, λ s tt s' => s = tt :: s' ⟩)].toAssocList,
    init_state := λ s => s = [],
  }

def gfmodule : NatModule (List Nat) := gcompf Nat (fun a => a + 1) (fun a => a + 1)

end Graphiti.NatModule
