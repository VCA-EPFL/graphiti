/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Module
import Graphiti.Component
import Graphiti.Examples.Noc.Utils

set_option autoImplicit false
set_option linter.all false

open Batteries (AssocList)

namespace Graphiti.Noc

  -- Topology definition -------------------------------------------------------

  abbrev Netsz : Type :=
    Nat

  @[simp]
  abbrev RouterID' (netsz : Netsz) : Type :=
    Fin netsz

  @[simp]
  abbrev Neigh' (netsz : Netsz) : Type :=
    RouterID' netsz → List (RouterID' netsz)

  @[simp]
  abbrev Neigh_ok' (netsz : Netsz) (inp : Neigh' netsz) (out : Neigh' netsz) :=
    ∀ rid rid', List.count rid' (out rid) = List.count rid (inp rid')

  structure Topology (netsz : Netsz) where
    neigh_inp : Neigh' netsz
    neigh_out : Neigh' netsz
    neigh_ok  : Neigh_ok' netsz neigh_inp neigh_out

  variable {netsz : Netsz}

  abbrev Topology.RouterID (t : Topology netsz) :=
    RouterID' netsz

  abbrev Topology.Neigh (t : Topology netsz) :=
    Neigh' netsz

  @[simp]
  abbrev Topology.Dir_out (t : Topology netsz) (rid : t.RouterID) : Type :=
    Fin ((t.neigh_out rid).length + 1)

  @[simp]
  abbrev Topology.Dir_inp (t : Topology netsz) (rid : t.RouterID) : Type :=
    Fin ((t.neigh_inp rid).length + 1)

  abbrev Topology.mkDir_out (t : Topology netsz) (rid : t.RouterID) (i : Nat) (h : i < (t.neigh_out rid).length) : t.Dir_out rid :=
    ⟨i + 1, by simpa only [Nat.add_lt_add_iff_right]⟩

  abbrev Topology.mkDir_inp (t : Topology netsz) (rid : t.RouterID) (i : Nat) (h : i < (t.neigh_inp rid).length) : t.Dir_inp rid :=
    ⟨i + 1, by simpa only [Nat.add_lt_add_iff_right]⟩

  def Topology.DirLocal_out (t : Topology netsz) {rid : t.RouterID} : t.Dir_out rid :=
    ⟨0, by simpa only [Nat.zero_lt_succ]⟩

  def Topology.DirLocal_inp (t : Topology netsz) {rid : t.RouterID} : t.Dir_inp rid :=
    ⟨0, by simpa only [Nat.zero_lt_succ]⟩

  abbrev Topology.out_len (t : Topology netsz) (rid : t.RouterID) : Nat :=
    (t.neigh_out rid).length

  abbrev Topology.inp_len (t : Topology netsz) (rid : t.RouterID) : Nat :=
    (t.neigh_inp rid).length

  abbrev Topology.Conn_out (t : Topology netsz) :=
    Σ (rid : t.RouterID), t.Dir_out rid

  abbrev Topology.Conn_out' (t : Topology netsz) :=
    Σ (rid : t.RouterID), t.Dir_out rid × t.RouterID

  abbrev Topology.Conn_inp (t : Topology netsz) :=
    Σ (rid : t.RouterID), t.Dir_inp rid

  abbrev Topology.Conn_inp' (t : Topology netsz) :=
    Σ (rid : t.RouterID), t.Dir_inp rid × t.RouterID

  abbrev Topology.Conn (t : Topology netsz) :=
    t.Conn_out × t.Conn_inp

  def Topology.conns_out (t : Topology netsz) (rid : t.RouterID) : List t.Conn_out' :=
    (t.neigh_out rid).mapFinIdx (λ d rid' h => ⟨rid, t.mkDir_out rid d h, rid'⟩)

  def Topology.conns_inp (t : Topology netsz) (rid : t.RouterID) : List t.Conn_inp' :=
    (t.neigh_inp rid).mapFinIdx (λ d rid' h => ⟨rid, t.mkDir_inp rid d h, rid'⟩)

  def Topology.conns (t : Topology netsz) : List t.Conn :=
    let conns_out := (fin_range netsz).map t.conns_out |>.flatten
    let conns_inp := (fin_range netsz).map t.conns_inp |>.flatten
    (List.foldl
      (λ (conns_inp, conns) conn_out =>
        let conn_inp_idx :=
          List.findFinIdx?
            (λ c => c.1 = conn_out.2.2 && c.2.2 = conn_out.1)
            conns_inp
        match conn_inp_idx with
        | .some conn_inp_idx =>
            let conn_inp := conns_inp[conn_inp_idx]
            let conn := ⟨
              ⟨conn_out.1, conn_out.2.1⟩,
              ⟨conn_inp.1, conn_inp.2.1⟩
            ⟩
            (conns_inp.eraseIdx conn_inp_idx, conn :: conns)
        | .none => (conns_inp, conns) -- TODO: Provably unreachable
      )
      (conns_inp, [])
      conns_out).2

  -- Arbiter (Routing policy) --------------------------------------------------

  @[simp]
  abbrev Route' (t : Topology netsz) (Flit : Type) : Type :=
    (cur : t.RouterID) → (flit : Flit) → (t.Dir_out cur × Flit)

  @[simp]
  abbrev Flit' (Data : Type) (FlitHeader : Type) : Type :=
    Data × FlitHeader

  @[simp]
  abbrev MkHead' (t : Topology netsz) (Data : Type) (FlitHeader : Type) : Type :=
    (cur dst : t.RouterID) → (data : Data) → FlitHeader

  structure Arbiter (t : Topology netsz) (Data : Type) where
    FlitHeader  : Type
    route       : Route' t (Flit' Data FlitHeader)
    mkhead      : MkHead' t Data FlitHeader

  variable {t : Topology netsz} {Data : Type}

  abbrev Arbiter.Flit (rp : Arbiter t Data) :=
    Flit' Data rp.FlitHeader

  abbrev Arbiter.Route (rp : Arbiter t Data) :=
    Route' t rp.Flit

  abbrev Arbiter.MkHead (rp : Arbiter t Data) :=
    MkHead' t Data rp.FlitHeader

  -- Router --------------------------------------------------------------------

  -- TODO: RouterRel' could have a `Dir_inp rid` as a parameter so we know where
  -- we got the message from
  @[simp]
  abbrev RouterRel' (netsz : Netsz) (Flit RouterState : Type) :=
    (rid : RouterID' netsz) → (old_s : RouterState) → (val : Flit) → (old_s : RouterState) → Prop

  structure Router (netsz : Netsz) (Flit : Type) where
    State       : Type
    init_state  : State
    input_rel   : RouterRel' netsz Flit State
    output_rel  : RouterRel' netsz Flit State

  abbrev Router.Rel {netsz : Netsz} {Flit : Type} (r : Router netsz Flit) :=
    RouterRel' netsz Flit r.State

  -- Noc -----------------------------------------------------------------------

  structure Noc (Data : Type) [BEq Data] [LawfulBEq Data] (netsz : Netsz) where
    topology  : Topology netsz
    arbiter   : Arbiter topology Data
    routers   : Router netsz arbiter.Flit
    DataS     : String

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  @[simp]
  abbrev Noc.State (n : Noc Data netsz) :=
    Vector n.routers.State netsz

  @[simp]
  abbrev Noc.RouterID (n : Noc Data netsz) :=
    n.topology.RouterID

  @[simp]
  abbrev Noc.Dir_out (n : Noc Data netsz) :=
    n.topology.Dir_out

  @[simp]
  abbrev Noc.Dir_inp (n : Noc Data netsz) :=
    n.topology.Dir_inp

  @[simp]
  abbrev Noc.Flit (n : Noc Data netsz) :=
    n.arbiter.Flit

  @[simp]
  abbrev Noc.Rel_out (n : Noc Data netsz) (T : Type) :=
    (rid : n.RouterID) → (dir : n.Dir_out rid) → (old_s : n.State) → (val : T) → (old_s : n.State) → Prop

  @[simp]
  abbrev Noc.Rel_inp (n : Noc Data netsz) (T : Type) :=
    (rid : n.RouterID) → (dir : n.Dir_inp rid) → (old_s : n.State) → (val : T) → (old_s : n.State) → Prop

end Graphiti.Noc
