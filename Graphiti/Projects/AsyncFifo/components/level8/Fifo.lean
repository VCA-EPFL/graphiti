/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level3.Oracle
import Graphiti.Projects.AsyncFifo.components.level7.ReadDomain
import Graphiti.Projects.AsyncFifo.components.level7.WriteDomain

/-!
# The FIFO, as a layer

The top of the hierarchy, built like every other component: an implementation over the
*specifications* of the parts below it.  Two clock domains, each standing for its specification
(`wdomSpec`, `rdomSpec`), and the two oracles that resolve their synchronisers, wired by
the Gray pointers that cross between them and the memory the read domain addresses.

Its specification is `fifoSpec` (`TopSpec.lean`), and `asyncFifoImpl_refines` in
`TopRefinement.lean` is this layer's theorem.
-/

namespace Graphiti.AsyncFifo

section Fifo

variable (α : Type) [Inhabited α] (n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat)

/-- **The asynchronous FIFO**: two clock domains by their specifications, and two oracles. -/
def asyncFifoGraph := [graphEnv|
    wclk [type="io"];
    winc [type="io"];
    wdata [type="io"];
    rclk [type="io"];
    rinc [type="io"];
    full [type="io"];
    empty [type="io"];
    rdata [type="io"];

    wdom [type="wdom", typeImp=$(⟨_, wdomSpec α n lat stl su kq P_w S_w R_w pw_w⟩)];
    rdom [type="rdom", typeImp=$(⟨_, rdomSpec α n lat stl su kq rdly P_r S_r R_r pw_r⟩)];
    orcw [type="oracle_w", typeImp=$(⟨_, oracle n⟩)];
    orcr [type="oracle_r", typeImp=$(⟨_, oracle n⟩)];

    wclk -> wdom [to="clk"];
    winc -> wdom [to="inc"];
    wdata -> wdom [to="data"];
    rclk -> rdom [to="clk"];
    rinc -> rdom [to="inc"];

    wdom -> rdom [from="gray", to="wgray"];
    rdom -> wdom [from="gray", to="rgray"];
    wdom -> rdom [from="mem", to="mem"];
    orcw -> wdom [from="bits", to="orc"];
    orcr -> rdom [from="bits", to="orc"];

    wdom -> full [from="full"];
    rdom -> empty [from="empty"];
    rdom -> rdata [from="rdata"];
  ]

/-- The lowered graph (topology only, independent of the parameters). -/
@[drunfold_defs]
def asyncFifoLowered := (asyncFifoGraph Unit 0 0 0 0 0 0 0 0 0 0 0 0 0 0).1.lower_TR |>.get rfl

/-- What each node of the graph is. -/
def envF := (asyncFifoGraph α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).2

/-- **The FIFO's implementation**: the graph, each domain standing for its specification. -/
def asyncFifoImpl := [e| asyncFifoLowered, (envF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r).find? ]

end Fifo

end Graphiti.AsyncFifo
