/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.BuildModule
import Graphiti.Projects.Noc.Spec
import Graphiti.Projects.Noc.Buffer
import Graphiti.Projects.Noc.Lemmas

open Batteries (AssocList)

namespace Graphiti.Projects.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  inductive get_output (noc : Noc Data netsz) :
    (src dst : noc.RouterID) → (src_flit : noc.Flit) → (dst_data : Data) → Prop
  where
  | step src dst src_flit mid_flit dst_data dir (hdir : noc.topology.isConnDir_out dir) :
      noc.routing_policy.route src src_flit = (dir, mid_flit)
      → get_output noc (noc.topology.getConnDir_out hdir) dst mid_flit dst_data
      → get_output noc src dst src_flit dst_data
  | done src src_flit dst_flit :
      noc.routing_policy.route src src_flit = (noc.topology.DirLocal_out, dst_flit)
      → get_output noc src src src_flit dst_flit.1

  -- This correctness is partial. It requires that the data is exactly the same
  -- in the end.
  -- This is true because we want to show that the noc behave as a bag, but it
  -- would also be nice that it behaves like a bag + a pure function applied to
  -- it.
  def Noc.routing_policy_correct (noc : Noc Data netsz) : Prop :=
    ∀ (src dst : (noc.RouterID)) data,
      get_output noc src dst (data, noc.routing_policy.mkhead src dst data) data

  -- A weaker, more general version where we don't require that output will
  -- actually leave, but if they do, it has to be at the correct output router
  def Noc.routing_policy_correct_weak (noc : Noc Data netsz) : Prop :=
    ∀ (src dst dst' : (noc.RouterID)) data data',
      get_output noc src dst' (data, noc.routing_policy.mkhead src dst data) data'
      → dst = dst' ∧ data = data'

  class NocCorrect (noc : Noc Data netsz) where
    routing_policy : noc.routing_policy_correct

end Graphiti.Projects.Noc
