/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Core.Module
import Graphiti.Projects.Noc.Lang

namespace Graphiti.Projects.Noc

  variable (Data : Type) [BEq Data] [LawfulBEq Data]

  -- Topology --------------------------------------------------------------------

  structure DirectedTorus where
    size_x  : Nat
    size_y  : Nat

  abbrev DirectedTorus.pos_x (d : DirectedTorus) : Type :=
    Fin d.size_x

  abbrev DirectedTorus.pos_y (d : DirectedTorus) : Type :=
    Fin d.size_y

  def DirectedTorus.netsz (d : DirectedTorus) : Netsz :=
    d.size_x * d.size_y

  abbrev DirectedTorus.RouterID (d : DirectedTorus) :=
    RouterID' d.netsz

  def DirectedTorus.Neigh (d : DirectedTorus) :=
    Neigh' d.netsz

  @[drcomponents]
  def DirectedTorus.get_x (d : DirectedTorus) (i : d.RouterID) : d.pos_x :=
    -- TODO
    ⟨i.toNat % d.size_x, by sorry⟩

  @[drcomponents]
  def DirectedTorus.get_y (d : DirectedTorus) (i : d.RouterID) : d.pos_y :=
    -- TODO
    ⟨(i.toNat / d.size_x) % d.size_y, by sorry⟩

  @[drcomponents]
  def DirectedTorus.get_rid (d : DirectedTorus) (x : d.pos_x) (y : d.pos_y) : d.RouterID :=
    -- TODO
    ⟨y * d.size_x + x, by sorry⟩

  @[drcomponents]
  def DirectedTorus.get_succ_x (d : DirectedTorus) (x : d.pos_x) : d.pos_x :=
    -- TODO
    ⟨(x.1 + 1) % d.size_x, by sorry⟩

  @[drcomponents]
  def DirectedTorus.get_succ_y (d : DirectedTorus) (y : d.pos_y) : d.pos_y :=
    -- TODO
    ⟨(y.1 + 1) % d.size_y, by sorry⟩

  @[drcomponents]
  def DirectedTorus.get_pred_x (d : DirectedTorus) (x : d.pos_x) : d.pos_x :=
    ⟨if x.1 == 0 then d.size_x - 1 else x.1 - 1, by sorry⟩

  @[drcomponents]
  def DirectedTorus.get_pred_y (d : DirectedTorus) (y : d.pos_y) : d.pos_y :=
    ⟨if y.1 == 0 then d.size_y - 1 else y.1 - 1, by sorry⟩

  @[drcomponents]
  def DirectedTorus.neigh_out (d : DirectedTorus) : d.Neigh :=
    λ src =>
      let src_x := d.get_x src
      let src_y := d.get_y src
      [
        d.get_rid (d.get_succ_x src_x) src_y,
        d.get_rid src_x (d.get_succ_y src_y),
      ]

  @[drcomponents]
  def DirectedTorus.neigh_inp (d : DirectedTorus) : d.Neigh :=
    λ src =>
      let src_x := d.get_x src
      let src_y := d.get_y src
      [
        d.get_rid (d.get_pred_x src_x) src_y,
        d.get_rid src_x (d.get_pred_y src_y),
      ]

  theorem DirectedTorus.neigh_ok (d : DirectedTorus) : Neigh_ok' d.netsz d.neigh_inp d.neigh_out := by
    intro rid rid'
    dsimp [drcomponents]
    -- TODO
    sorry

  @[drunfold_defs]
  def DirectedTorus.to_topology (d : DirectedTorus) : Topology d.netsz :=
    {
      neigh_out := d.neigh_out
      neigh_inp := d.neigh_inp
      neigh_ok  := d.neigh_ok
    }

  theorem DirectedTorus.neigh_out_uniform (d : DirectedTorus) (src : d.RouterID) :
    (d.neigh_out src).length = 2 := by simpa [DirectedTorus.neigh_out]

  theorem DirectedTorus.neigh_inp_uniform (d : DirectedTorus) (src : d.RouterID) :
    (d.neigh_inp src).length = 2 := by simpa [DirectedTorus.neigh_inp]

  abbrev DirectedTorus.DirX_out (d : DirectedTorus) {src} : d.to_topology.Dir_out src :=
    ⟨1, by simp [DirectedTorus.neigh_out_uniform, drunfold_defs]⟩

  abbrev DirectedTorus.DirY_out (d : DirectedTorus) {src} : d.to_topology.Dir_out src :=
    ⟨2, by simpa [DirectedTorus.neigh_out_uniform, drunfold_defs]⟩

  def DirectedTorus.DirLocal_out (d : DirectedTorus) {src} : d.to_topology.Dir_out src :=
    ⟨0, by simpa⟩

  -- Absolute Header, XY Routing Policy ------------------------------------------

  abbrev DirectedTorus.AbsoluteHeader (d : DirectedTorus) : Type :=
    d.RouterID

  abbrev DirectedTorus.AbsoluteFlit (d : DirectedTorus) : Type :=
    Data × d.AbsoluteHeader

  abbrev DirectedTorus.AbsoluteRoute (d : DirectedTorus) : Type :=
    Route' d.to_topology (d.AbsoluteFlit Data)

  def DirectedTorus.absolute_route_xy (d : DirectedTorus) : d.AbsoluteRoute Data :=
    λ cur flit =>
      if d.get_x cur != d.get_x flit.2 then (d.DirX_out, flit)
      else if d.get_y cur != d.get_y flit.2 then (d.DirY_out, flit)
      else (d.DirLocal_out, flit)

  @[drunfold_defs]
  def DirectedTorus.AbsoluteRoutingPolicy (d : DirectedTorus) : RoutingPolicy d.to_topology Data :=
    {
      FlitHeader  := d.AbsoluteHeader,
      route       := d.absolute_route_xy Data
      mkhead      := λ _ dst _ => dst
    }

  -- Relative Header, XY Routing Policy ------------------------------------------

  structure DirectedTorus.RelativeHeader (d : DirectedTorus) where
    diff_x : Nat
    diff_y : Nat
  deriving BEq

  abbrev DirectedTorus.RelativeFlit (d : DirectedTorus) : Type :=
    Data × d.RelativeHeader

  abbrev DirectedTorus.RelativeRoute (d : DirectedTorus) : Type :=
    Route' d.to_topology (d.RelativeFlit Data)

  def DirectedTorus.relative_route_xy (d : DirectedTorus) : d.RelativeRoute Data :=
    λ cur flit =>
      if 0 < flit.2.diff_x then (d.DirX_out, flit)
      else if 0 < flit.2.diff_y then (d.DirY_out, flit)
      else (d.to_topology.DirLocal_out, flit)

  @[drunfold_defs]
  def DirectedTorus.relative_mkhead (d : DirectedTorus) : MkHead' d.to_topology Data d.RelativeHeader :=
    λ cur dst data =>
      {
        diff_x := d.get_x cur - d.get_x dst,
        diff_y := d.get_y cur - d.get_y dst,
      }

  @[drunfold_defs]
  def DirectedTorus.RelativeRoutingPolicy (d : DirectedTorus) : RoutingPolicy d.to_topology Data :=
    {
      FlitHeader  := d.RelativeHeader,
      route       := d.relative_route_xy Data
      mkhead      := d.relative_mkhead Data
    }

end Graphiti.Projects.Noc
