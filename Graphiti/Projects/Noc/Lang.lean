/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Core.Module
import Graphiti.Core.Component
import Graphiti.Projects.Noc.Utils

set_option autoImplicit false
set_option linter.all false

open Batteries (AssocList)

namespace Graphiti.Projects.Noc

  -- Topology definition -------------------------------------------------------

  @[simp]
  abbrev Netsz : Type :=
    Nat

  @[simp]
  abbrev RouterID' (netsz : Netsz) : Type :=
    Fin netsz

  @[simp]
  abbrev Neigh' (netsz : Netsz) : Type :=
    RouterID' netsz → List (RouterID' netsz)

  -- The neighbor function is correct if if the input neighbor and output
  -- neighbor are bijective
  @[simp]
  abbrev Neigh_ok' (netsz : Netsz) (inp : Neigh' netsz) (out : Neigh' netsz) :=
    ∀ rid rid', List.count rid' (out rid) = List.count rid (inp rid')

  structure Topology (netsz : Netsz) where
    neigh_inp : Neigh' netsz
    neigh_out : Neigh' netsz
    neigh_ok  : Neigh_ok' netsz neigh_inp neigh_out

  variable {netsz : Netsz}

  @[simp]
  abbrev Topology.RouterID (t : Topology netsz) :=
    RouterID' netsz

  @[simp]
  abbrev Topology.Neigh (t : Topology netsz) :=
    Neigh' netsz

  @[simp]
  abbrev Topology.out_len (t : Topology netsz) (rid : t.RouterID) : Nat :=
    (t.neigh_out rid).length

  @[simp]
  abbrev Topology.inp_len (t : Topology netsz) (rid : t.RouterID) : Nat :=
    (t.neigh_inp rid).length

  -- An output direction can either be any neighbor, or 0 wich corresponds to a
  -- local output
  @[simp]
  abbrev Topology.Dir_out (t : Topology netsz) (rid : t.RouterID) : Type :=
    Fin ((t.out_len rid) + 1)

  -- An input direction can either be any neighbor, or 0 wich corresponds to a
  -- local input
  @[simp]
  abbrev Topology.Dir_inp (t : Topology netsz) (rid : t.RouterID) : Type :=
    Fin ((t.inp_len rid) + 1)

  -- The local output is always zero
  def Topology.DirLocal_out (t : Topology netsz) {rid : t.RouterID} : t.Dir_out rid :=
    ⟨0, by simpa only [Nat.zero_lt_succ]⟩

  -- The local input is always zero
  def Topology.DirLocal_inp (t : Topology netsz) {rid : t.RouterID} : t.Dir_inp rid :=
    ⟨0, by simpa only [Nat.zero_lt_succ]⟩

  -- An output direction corresponds to a connection to another router if it is
  -- not the local output
  @[simp]
  def Topology.isConnDir_out (t : Topology netsz) {rid : t.RouterID} (dir : t.Dir_out rid) : Prop :=
    0 < dir.toNat

  -- An output direction corresponds to a connection to another router if it is
  -- not the local output
  def Topology.getConnDir_out (t : Topology netsz) {rid : t.RouterID} {dir : t.Dir_out rid} (Hdir : t.isConnDir_out dir) : t.RouterID :=
    -- TODO: Clean this horrible proof
    let dir' : Fin (t.out_len rid) := ⟨dir.1 - 1, by
      obtain ⟨v, h⟩ := dir;
      rw [←Nat.add_lt_add_iff_right (k := 1)]
      induction v <;> simp
      · simp at Hdir
      · simp at h; exact h
    ⟩
    (t.neigh_out rid)[dir']

  -- TODO:
  -- def Topology.getConnDir_inp (t : Topology netsz) {rid : t.RinperID} {dir : t.Dir_inp rid} (Hdir : t.isConnDir_inp dir) : t.RouterID :=
  --   sorry

  -- An input direction corresponds to a connection to another router if it is
  -- not the local input
  @[simp]
  def Topology.isConnDir_inp (t : Topology netsz) {rid : t.RouterID} (dir : t.Dir_inp rid) : Prop :=
    0 < dir.toNat

  -- Utils to make a connection output direction
  def Topology.mkDir_out (t : Topology netsz) (rid : t.RouterID) (i : Nat) (h : i < (t.out_len rid)) : t.Dir_out rid :=
    ⟨i + 1, by simpa only [Nat.add_lt_add_iff_right]⟩

  -- Utils to make a connection input direction
  def Topology.mkDir_inp (t : Topology netsz) (rid : t.RouterID) (i : Nat) (h : i < (t.inp_len rid)) : t.Dir_inp rid :=
    ⟨i + 1, by simpa only [Nat.add_lt_add_iff_right]⟩

  -- An output connection is a router id and an output port on this router
  @[simp]
  abbrev Topology.Conn_out (t : Topology netsz) : Type :=
    Σ (rid : t.RouterID), t.Dir_out rid

  -- A more complete Conn_out where we also know the ID of the router we are
  -- connected to
  @[simp]
  abbrev Topology.Conn_out' (t : Topology netsz) : Type :=
    Σ (rid : t.RouterID), t.Dir_out rid × t.RouterID

  -- An input connection is a router id and an input port on this router
  @[simp]
  abbrev Topology.Conn_inp (t : Topology netsz) : Type :=
    Σ (rid : t.RouterID), t.Dir_inp rid

  -- A more complete Conn_inp where we also know the ID of the router we are
  -- connected to
  @[simp]
  abbrev Topology.Conn_inp' (t : Topology netsz) : Type :=
    Σ (rid : t.RouterID), t.Dir_inp rid × t.RouterID

  -- A full connection
  @[simp]
  abbrev Topology.Conn (t : Topology netsz) : Type :=
    t.Conn_out × t.Conn_inp

  -- Give the list of all output connections on a router
  def Topology.conns_out (t : Topology netsz) (rid : t.RouterID) : List t.Conn_out' :=
    (t.neigh_out rid).mapFinIdx (λ d rid' h => ⟨rid, t.mkDir_out rid d h, rid'⟩)

  -- Give the list of all input connections on a router
  def Topology.conns_inp (t : Topology netsz) (rid : t.RouterID) : List t.Conn_inp' :=
    (t.neigh_inp rid).mapFinIdx (λ d rid' h => ⟨rid, t.mkDir_inp rid d h, rid'⟩)

  -- Give the list of all internal connections on a router
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
        | .none => (conns_inp, conns) -- Unreachable
      )
      (conns_inp, [])
      conns_out).2

  -- Routing Policy ------------------------------------------------------------
  -- Limitations:
  --  · Can only be deterministic
  --  · Cannot drop packets
  --  · Cannot broadcast them

  @[simp]
  abbrev Route' (t : Topology netsz) (Flit : Type) : Type :=
    (cur : t.RouterID) → (flit : Flit) → (t.Dir_out cur × Flit)

  @[simp]
  abbrev Flit' (Data : Type) (FlitHeader : Type) : Type :=
    Data × FlitHeader

  @[simp]
  abbrev MkHead' (t : Topology netsz) (Data : Type) (FlitHeader : Type) : Type :=
    (cur dst : t.RouterID) → (data : Data) → FlitHeader

  structure RoutingPolicy (t : Topology netsz) (Data : Type) where
    FlitHeader  : Type
    route       : Route' t (Flit' Data FlitHeader)
    mkhead      : MkHead' t Data FlitHeader

  variable {t : Topology netsz} {Data : Type}

  @[simp]
  abbrev RoutingPolicy.Flit (rp : RoutingPolicy t Data) :=
    Flit' Data rp.FlitHeader

  @[simp]
  abbrev RoutingPolicy.Route (rp : RoutingPolicy t Data) :=
    Route' t rp.Flit

  @[simp]
  abbrev RoutingPolicy.MkHead (rp : RoutingPolicy t Data) :=
    MkHead' t Data rp.FlitHeader

  -- Buffer --------------------------------------------------------------------

  -- TODO: BufferRel' should have a `Dir_inp rid` / `Dir_out rid` as a parameter so we know
  -- where we got the message from
  -- This require parametrizing Buffer by the topology instead of just the netsz
  -- but it should not be a real problem
  @[simp]
  abbrev BufferRel' (netsz : Netsz) (Flit BufferState : Type) :=
    (rid : RouterID' netsz) → (old_s : BufferState) → (val : Flit) → (new_s : BufferState) → Prop

  structure Buffer (netsz : Netsz) (Flit : Type) where
    State       : Type
    init_state  : State
    input_rel   : BufferRel' netsz Flit State
    output_rel  : BufferRel' netsz Flit State

  @[simp]
  abbrev Buffer.Rel {netsz : Netsz} {Flit : Type} (r : Buffer netsz Flit) :=
    BufferRel' netsz Flit r.State

  -- Noc -----------------------------------------------------------------------

  structure Noc (Data : Type) [BEq Data] [LawfulBEq Data] (netsz : Netsz) where
    topology        : Topology netsz
    routing_policy  : RoutingPolicy topology Data
    buffer          : Buffer netsz routing_policy.Flit
    DataS           : String

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  @[simp]
  abbrev Noc.State (n : Noc Data netsz) :=
    Vector n.buffer.State netsz

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
    n.routing_policy.Flit

  @[simp]
  abbrev Noc.Rel_out (n : Noc Data netsz) (T : Type) :=
    (rid : n.RouterID) → (dir : n.Dir_out rid) → (old_s : n.State) → (val : T) → (old_s : n.State) → Prop

  @[simp]
  abbrev Noc.Rel_inp (n : Noc Data netsz) (T : Type) :=
    (rid : n.RouterID) → (dir : n.Dir_inp rid) → (old_s : n.State) → (val : T) → (old_s : n.State) → Prop

end Graphiti.Projects.Noc
