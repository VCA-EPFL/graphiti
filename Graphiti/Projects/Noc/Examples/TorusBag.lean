/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Graphiti.Core.Component
import Graphiti.Core.ExprHigh
import Graphiti.Core.ExprLow
import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.Buffer
import Graphiti.Projects.Noc.Topology.Torus
import Graphiti.Projects.Noc.BuildExpr
import Graphiti.Projects.Noc.BuildModule

namespace Graphiti.Projects.Noc.Examples

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
      routing_policy := dt.AbsoluteRoutingPolicy Data
      buffer := Buffer.Unbounded.bag dt.netsz (dt.AbsoluteFlit Data)
      DataS := "Nat"
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

  def tmp := n.build_expr

  #eval! tmp
  #eval! tmp |> toString |> IO.print

  def tmp' := n.build_expr

  #eval! tmp' |> toString |> IO.print


end Graphiti.Projects.Noc.Examples
