/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Core.Module
import Graphiti.Core.Component
import Graphiti.Projects.Noc.Utils
import Graphiti.Projects.Noc.Lang

open Batteries (AssocList)

namespace Graphiti.Projects.Noc

  variable {Data : Type} [ToString Data] [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  -- Internal name of router port
  @[drcomponents]
  def router_name (n : Noc Data netsz) (rid : n.RouterID) :=
    s!"Router_{rid}"

  -- Name of router type in environment
  @[drcomponents]
  def router_type_name (n : Noc Data netsz) (rid : n.RouterID) :=
    s!"Router {n.DataS} {rid}"

  @[drcomponents]
  def router_inp (n : Noc Data netsz) (rid : n.RouterID) (dir : n.Dir_inp rid) : InternalPort String :=
    { inst := .internal (router_name n rid), name := NatModule.stringify_input dir }

  @[drcomponents]
  def router_out (n : Noc Data netsz) (rid : n.RouterID) (dir : n.Dir_out rid) : InternalPort String :=
    { inst := .internal (router_name n rid), name := NatModule.stringify_output dir }

  @[drunfold_defs]
  def Noc.build_expr (n : Noc Data netsz) : ExprLow String String :=

    let mkrouter (rid : n.RouterID) : ExprLow String String :=
      .base
      {
        input :=
          .cons (NatModule.stringify_input 0) (router_inp n rid 0)
          (List.mapFinIdx
            (n.topology.neigh_inp rid)
            (λ dir _ hdir => ⟨
              NatModule.stringify_input (dir + 1),
              router_inp n rid (n.topology.mkDir_inp rid dir hdir)
            ⟩)
          |>.toAssocList),
        output :=
          .cons (NatModule.stringify_output 0) (router_out n rid 0)
          (List.mapFinIdx
            (n.topology.neigh_out rid)
            (λ dir _ hdir => ⟨
              NatModule.stringify_output (dir + 1),
              router_out n rid (n.topology.mkDir_out rid dir hdir)
            ⟩)
          |>.toAssocList),
      }
      (router_type_name n rid)

    let mkrouters (acc : ExprLow String String) : ExprLow String String :=
      List.foldr (λ i acc => .product (mkrouter i) acc) acc (fin_range netsz)

    let mkconns (acc : ExprLow String String) : ExprLow String String :=
      List.foldr
        (λ c acc =>
          let rid_out := c.1.1
          let dir_out := c.1.2
          let rid_inp := c.2.1
          let dir_inp := c.2.2
          .connect
            {
              output  := router_out n rid_out dir_out
              input   := router_inp n rid_inp dir_inp
            }
          acc)
        acc n.topology.conns

    .base { input := .cons "" { inst := .internal "empty", name := "" } .nil, output := .nil } "empty"
    |> mkrouters
    |> mkconns

end Graphiti.Projects.Noc
