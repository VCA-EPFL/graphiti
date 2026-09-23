/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level2.Domains

/-!
# The oracle

A source of arbitrary streams.  It makes the resolution of a synchroniser's metastability an
explicit --- and adversarial --- input of the circuit rather than hidden nondeterminism, so
the refinement theorem quantifies over every way it could resolve.
-/

namespace Graphiti.AsyncFifo

variable (n : Nat)

/-- An oracle: a source of arbitrary streams, used to make the metastability resolution of a
synchroniser an explicit (adversarial) input of the circuit. -/
@[drcomponents]
def oracle : StringModule Unit :=
  { inputs := ∅
    outputs := [ (↑"bits", ⟨List (Orc n), fun s _ s' => s' = s⟩) ].toAssocList
    internals := []
    init_state := fun _ => True }

end Graphiti.AsyncFifo
