/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Module
import Graphiti.Examples.Noc.Lang

namespace Graphiti.Noc

  structure Mesh2D where
    sizeX : Nat
    sizeY : Nat

  -- TODO: Harder than Torus because topology is less regular (edges)

end Graphiti.Noc
