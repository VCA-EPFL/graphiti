/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.BuildModule
import Graphiti.Projects.Noc.BuildExpr

set_option autoImplicit false
set_option linter.all false

namespace Graphiti.Projects.Noc

variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

-- Router ----------------------------------------------------------------------

@[drcomponents]
def Noc.mk_spec_router_input_rule_z (n : Noc Data netsz) (rid : n.RouterID) : RelIO n.buffer.State :=
  ⟨
    Data × n.topology.RouterID,
    λ old_s val new_s =>
      n.buffer.input_rel rid old_s (val.1, (n.routing_policy.mkhead rid val.2 val.1)) new_s
  ⟩

@[drcomponents]
def Noc.mk_spec_router_input_rule_s (n : Noc Data netsz) (rid : n.RouterID) : RelIO n.buffer.State :=
  ⟨n.routing_policy.Flit, n.buffer.input_rel rid⟩

@[drcomponents]
def Noc.mk_spec_router_input_rule (n : Noc Data netsz) (rid : n.RouterID) (dir : n.Dir_inp rid) : RelIO n.buffer.State :=
  if dir = n.topology.DirLocal_inp
  then n.mk_spec_router_input_rule_z rid
  else n.mk_spec_router_input_rule_s rid

@[drcomponents]
def Noc.mk_spec_router_output_rule_z (n : Noc Data netsz) (rid : n.RouterID) : RelIO n.buffer.State :=
  ⟨
    Data,
    λ old_s val new_s => ∃ head,
      n.router_output_rel rid n.topology.DirLocal_out old_s (val, head) new_s
  ⟩

@[drcomponents]
def Noc.mk_spec_router_output_rule_s (n : Noc Data netsz) (rid : n.RouterID) (dir : n.Dir_out rid) : RelIO n.buffer.State :=
  ⟨n.Flit, λ old_s val new_s => n.router_output_rel rid dir old_s val new_s⟩

@[drcomponents]
def Noc.mk_spec_router_output_rule (n : Noc Data netsz) (rid : n.RouterID) (dir : n.Dir_out rid) : RelIO n.buffer.State :=
  if dir = n.topology.DirLocal_out then n.mk_spec_router_output_rule_z rid else
    n.mk_spec_router_output_rule_s rid dir

@[drcomponents]
def Noc.spec_router' (n : Noc Data netsz) (rid : n.topology.RouterID) : NatModule n.buffer.State :=
  {
    inputs := RelIO.liftFinf ((n.topology.neigh_inp rid).length + 1) (n.mk_spec_router_input_rule rid)
    outputs := RelIO.liftFinf ((n.topology.neigh_out rid).length + 1) (n.mk_spec_router_output_rule rid)
    init_state := λ s => s = n.buffer.init_state
  }

@[drcomponents]
def Noc.spec_router (n : Noc Data netsz) (rid : n.topology.RouterID) : StringModule (n.buffer.State) :=
  n.spec_router' rid |> NatModule.stringify

-- Bag -------------------------------------------------------------------------
-- Weakest possible specification, where order is not preserved by the Noc

abbrev Noc.spec_bagT (n : Noc Data netsz) : Type :=
  List (Data × n.topology.RouterID)

@[drcomponents]
def Noc.mk_spec_bag_input_rule (n : Noc Data netsz) (rid : n.topology.RouterID) : RelIO n.spec_bagT :=
  ⟨Data × n.topology.RouterID, λ old_s v new_s => new_s = old_s ++ [v]⟩

@[drcomponents]
def Noc.mk_spec_bag_output_rule (n : Noc Data netsz) (rid : n.topology.RouterID) : RelIO n.spec_bagT :=
  ⟨
    Data,
    λ oldS v newS =>
      ∃ i : Fin oldS.length, newS = oldS.remove i ∧ (v, rid) = oldS.get i
  ⟩

@[drcomponents]
def Noc.spec_bag (n : Noc Data netsz) (name := "spec_bag") : NatModule (NatModule.Named name n.spec_bagT) :=
  {
    inputs := RelIO.liftFinf netsz n.mk_spec_bag_input_rule,
    outputs := RelIO.liftFinf netsz n.mk_spec_bag_output_rule,
    init_state := λ s => s = [],
  }

instance (n : Noc Data netsz) : MatchInterface n.build_module n.spec_bag := by
  apply MatchInterface_simpler
  <;> intros _
  <;> simpa only [drcomponents, RelIO.mapVal]

instance (n : Noc Data netsz) : MatchInterface n.spec_bag n.build_module := by
  apply MatchInterface_symmetric
  exact inferInstance

-- Multi-Queue -----------------------------------------------------------------
-- Flit are sent ordered per channel (one per each input/output pair)

abbrev Noc.spec_mqueueT (n : Noc Data netsz) : Type :=
  Vector n.spec_bagT (netsz * netsz)

abbrev Noc.spec_mqueue_idx (n : Noc Data netsz) (src dst : n.topology.RouterID) : Fin (netsz * netsz) :=
  ⟨src * netsz + dst, by apply add_mul src.2 dst.2⟩

@[drcomponents]
def Noc.mk_spec_mqueue_input_rule (n : Noc Data netsz) (rid : n.topology.RouterID) : RelIO n.spec_mqueueT :=
  ⟨
    Data × n.topology.RouterID, λ old_s v new_s =>
      let idx := n.spec_mqueue_idx rid v.2
      new_s = old_s.set idx (old_s[idx] ++ [v])
  ⟩

@[drcomponents]
def Noc.mk_spec_mqueue_output_rule (n : Noc Data netsz) (rid : n.topology.RouterID) : RelIO n.spec_mqueueT :=
  ⟨
    Data, λ old_s v new_s =>
      ∃ src : n.topology.RouterID,
        let idx := n.spec_mqueue_idx src rid
        old_s = new_s.set idx ((v, rid) :: new_s[idx])
  ⟩

@[drcomponents]
def Noc.spec_mqueue (n : Noc Data netsz) (name := "spec_mqueue") : NatModule (NatModule.Named name n.spec_mqueueT) :=
  {
    inputs := RelIO.liftFinf netsz n.mk_spec_mqueue_input_rule,
    outputs := RelIO.liftFinf netsz n.mk_spec_mqueue_output_rule,
    init_state := λ s => s = Vector.replicate (netsz * netsz) [],
  }

instance (n : Noc Data netsz) : MatchInterface n.build_module n.spec_mqueue := by
  apply MatchInterface_simpler
  <;> intros _
  <;> simpa only [drcomponents, RelIO.mapVal]

instance (n : Noc Data netsz) : MatchInterface n.spec_mqueue n.build_module := by
  apply MatchInterface_symmetric
  exact inferInstance

instance (n : Noc Data netsz) : MatchInterface n.spec_mqueue n.spec_bag := by
  apply MatchInterface_transitive n.build_module
  repeat exact inferInstance

instance (n : Noc Data netsz) : MatchInterface n.spec_bag n.spec_mqueue := by
  apply MatchInterface_symmetric
  repeat exact inferInstance

end Graphiti.Projects.Noc
