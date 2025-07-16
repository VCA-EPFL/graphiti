/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Graphiti.Module
import Graphiti.ModuleLemmas
import Graphiti.Component
import Graphiti.ExprHigh
import Graphiti.ExprLow
import Graphiti.Examples.Noc.Lang
import Graphiti.Examples.Noc.Router
import Graphiti.Examples.Noc.Spec
import Graphiti.Examples.Noc.Topology.Torus
import Graphiti.Examples.Noc.BuildExpr
import Graphiti.Examples.Noc.BuildModule

namespace Graphiti.Noc.Examples

  abbrev Data : Type := Nat

  def dt : DirectedTorus :=
    {
      size_x := 2
      size_y := 2
    }

  def topo := dt.to_topology

  def n : Noc Data dt.netsz :=
    {
      topology := topo
      routing_pol := dt.AbsoluteRoutingPolicy Data
      routers := Router.Unbounded.bag dt.netsz (dt.AbsoluteFlit Data)
    }

  -- If we want to extract to hardware, we have to implement a router
  --  * Router require inputs which all goes to a bag. mkhead does not require
  --    extra care
  --  * A second arbiter takes values from the bag and compare the destination
  --  `rid` with the current `rid`, output a decision id
  --  * We have an output component which takes an output direction and a Flit,
  --  and output it to the correct `Flit`

  -- The n.router is special in our cases because it is very simple:
  -- It does not require a MkHead (The head is exactly the destination)
  -- Which mean the implementation of a Router should be quite easy?

  def arbiter (rid : n.RouterID) : ExprLow String :=
    -- First split
    -- Then we need two check `isLt`
    sorry

  def router (rid : n.RouterID) : ExprLow String :=
    -- We need `n` inputs which all go to a nbag,
    -- and then an arbiter which takes elements of this bag and route them to
    -- the proper output
    -- Then we need
    sorry

  def tmp := n.build_expr |> ExprLow.higher

  #eval! (tmp.modules)
  #eval! (tmp |> toString)

end Graphiti.Noc.Examples
