/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Graphiti.Core.Module
import Graphiti.Core.Component
import Graphiti.Projects.Noc.Utils
import Graphiti.Projects.Noc.Lang

namespace Graphiti.Projects.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  @[drcomponents]
  abbrev Noc.router_output_rel (n : Noc Data netsz) :=
    λ (rid : n.RouterID) (dir : n.Dir_out rid) (old_s : n.buffer.State) (val : n.Flit) (new_s : n.buffer.State) =>
      let val' := n.routing_policy.route rid val
      dir = val'.1 ∧
      n.buffer.output_rel rid old_s val new_s

  @[drcomponents]
  abbrev Noc.input_rel (n : Noc Data netsz) : n.Rel_inp n.Flit :=
    λ rid dir old_s val new_s =>
      n.buffer.input_rel rid old_s[rid] val new_s[rid]
      ∧ ∀ (rid' : n.RouterID), rid ≠ rid' → new_s[rid'] = old_s[rid']

  @[drcomponents]
  abbrev Noc.input_rel' (n : Noc Data netsz) : n.Rel_inp (Data × n.RouterID) :=
    λ rid dir old_s val new_s =>
      n.input_rel rid dir old_s (val.1, (n.routing_policy.mkhead rid val.2 val.1)) new_s

  @[drcomponents]
  abbrev Noc.output_rel (n : Noc Data netsz) : n.Rel_out n.Flit :=
    λ rid dir old_s val new_s =>
      ∃ out_flit,
        n.routing_policy.route rid out_flit = (dir, val)
        ∧ n.router_output_rel rid dir old_s[rid] out_flit new_s[rid]
        ∧ ∀ rid', rid ≠ rid' → new_s[rid'] = old_s[rid']

  @[drcomponents]
  def Noc.mk_router_input (n : Noc Data netsz) (rid : n.RouterID) : RelIO n.State :=
    ⟨
      Data × n.topology.RouterID, n.input_rel' rid n.topology.DirLocal_inp
    ⟩

  @[drcomponents]
  def Noc.mk_router_output (n : Noc Data netsz) (rid : n.RouterID) : RelIO n.State :=
    ⟨
      Data,
      λ old_s val new_s =>
        ∃ head, n.output_rel rid n.topology.DirLocal_out old_s (val, head) new_s
    ⟩

  @[drcomponents]
  def Noc.mk_router_conn (n : Noc Data netsz) (conn : n.topology.Conn) : RelInt n.State :=
    λ old_s new_s => ∃ (val : n.Flit) (mid_s : n.State),
      n.output_rel conn.1.1 conn.1.2 old_s val mid_s ∧
      n.input_rel conn.2.1 conn.2.2 mid_s val new_s

  @[drcomponents]
  def Noc.build_module (n : Noc Data netsz) : Module Nat n.State :=
    {
      inputs := RelIO.liftFinf netsz n.mk_router_input,
      outputs := RelIO.liftFinf netsz n.mk_router_output,
      internals := (n.topology.conns).map (n.mk_router_conn),
      init_state := λ s => s = Vector.replicate netsz n.buffer.init_state,
    }

end Graphiti.Projects.Noc
