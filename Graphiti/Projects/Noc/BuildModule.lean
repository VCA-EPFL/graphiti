/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Module
import Graphiti.Component
import Graphiti.Examples.Noc.Utils
import Graphiti.Examples.Noc.Lang

set_option autoImplicit false
set_option linter.all false

namespace Graphiti.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  @[drcomponents]
  abbrev Noc.router_output_rel (n : Noc Data netsz) :=
    λ (rid : n.RouterID) (dir : n.Dir_out rid) (old_s : n.routers.State) (val : n.Flit) (new_s : n.routers.State) =>
      let val' := n.arbiter.route rid val
      dir = val'.1 ∧
      n.routers.output_rel rid old_s val new_s

  @[drcomponents]
  abbrev Noc.input_rel (n : Noc Data netsz) : n.Rel_inp n.Flit :=
    λ rid dir old_s val new_s =>
      n.routers.input_rel rid old_s[rid] val new_s[rid]
      ∧ ∀ (rid' : n.RouterID), rid ≠ rid' → new_s[rid'] = old_s[rid']

  @[drcomponents]
  abbrev Noc.input_rel' (n : Noc Data netsz) : n.Rel_inp (Data × n.RouterID) :=
    λ rid dir old_s val new_s =>
      n.input_rel rid dir old_s (val.1, (n.arbiter.mkhead rid val.2 val.1)) new_s

  @[drcomponents]
  abbrev Noc.output_rel (n : Noc Data netsz) : n.Rel_out n.Flit :=
    λ (rid : n.RouterID) (dir : n.Dir_out rid) old_s val new_s =>
      n.router_output_rel rid dir old_s[rid] val new_s[rid]
      ∧ ∀ (rid' : n.RouterID), rid ≠ rid' → new_s[rid'] = old_s[rid']

  @[drcomponents]
  def Noc.mk_router_input (n : Noc Data netsz) (rid : n.RouterID) (dir : n.Dir_inp rid) : RelIO n.State :=
    ⟨
      Data × n.topology.RouterID, n.input_rel' rid dir
    ⟩

  @[drcomponents]
  def Noc.mk_router_output (n : Noc Data netsz) (rid : n.RouterID) (dir : n.Dir_out rid) : RelIO n.State :=
    ⟨
      Data,
      λ old_s out new_s => ∃ head, n.output_rel rid dir old_s (out, head) new_s
    ⟩

  @[drcomponents]
  def Noc.mk_router_conn (n : Noc Data netsz) (conn : n.topology.Conn) : RelInt n.State :=
    λ old_s new_s => ∃ (val : n.Flit) (mid_s : n.State),
      n.output_rel conn.1.1 conn.1.2 old_s val mid_s ∧
      n.input_rel conn.2.1 conn.2.2 mid_s val new_s

  @[drcomponents]
  def Noc.build_module (n : Noc Data netsz) : Module Nat n.State :=
    {
      inputs := RelIO.liftFinf netsz (λ rid => n.mk_router_input rid n.topology.DirLocal_inp)
      outputs := RelIO.liftFinf netsz (λ rid => n.mk_router_output rid n.topology.DirLocal_out)
      internals := (n.topology.conns).map (n.mk_router_conn),
      init_state := λ s => s = Vector.replicate netsz n.routers.init_state,
    }

end Graphiti.Noc
