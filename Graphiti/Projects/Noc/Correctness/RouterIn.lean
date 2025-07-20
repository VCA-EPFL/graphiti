/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.BuildModule
import Graphiti.Projects.Noc.Topology.Torus
import Graphiti.Projects.Noc.Spec
import Graphiti.Projects.Noc.Router

open Batteries (AssocList)

set_option Elab.async false

namespace Graphiti.Noc.RouterIn

  variable (Data : Type) [BEq Data] [LawfulBEq Data]

  class RouterParam where
    noc : Noc Data
    router' : Router noc.netsz noc.Flit

  variable [RP : @RouterParam Data (by infer_instance) (by infer_instance)]

  abbrev noc' : Noc Data :=
    {
      topology    := RP.noc.topology
      routing_pol := RP.noc.routing_pol
      routers     := RP.router'
    }

  abbrev nocM := RP.noc.build_module
  abbrev nocM' := (noc' Data).build_module

  abbrev routerS := RP.noc.spec_router
  abbrev routerS' := (noc' Data).spec_router

  class Router'_Ok (rid : RP.noc.RouterID) where
    mm : MatchInterface (routerS' Data rid) (routerS Data rid)
    φ : RP.router'.State → RP.noc.routers.State → Prop
    refines_φ : (routerS' Data rid) ⊑_{φ} (routerS Data rid)
    indistinguishable : ∀ x y, φ x y → Module.indistinguishable (routerS' Data rid) (routerS Data rid) x y
    initial : Module.refines_initial (routerS' Data rid) (routerS Data rid) φ

  variable [ROK : ∀ rid : RP.noc.RouterID, Router'_Ok Data rid]

  def φ (I : (noc' Data).State) (S : RP.noc.State) : Prop :=
    ∀ rid : RP.noc.RouterID, (ROK rid).φ I[rid] S[rid]

  instance : MatchInterface (nocM' Data) (nocM Data) := by
    apply MatchInterface_simpler
    <;> intros ident
    <;> simpa only [drcomponents, RelIO.mapVal]

  theorem refines_initial :
    Module.refines_initial (nocM' Data) (nocM Data) (φ Data) := by
      intros i H
      -- apply Exists.intro (Vector.mapFinIdx (λ rid ir Hrid => (ROK rid).initial ir) i)
      sorry

  theorem refines_φ : (nocM' Data) ⊑_{φ Data} (nocM Data) := by
    sorry

  theorem ϕ_indistinguishable :
    ∀ i s, (φ Data) i s → Module.indistinguishable (nocM' Data) (nocM Data) i s := by
      sorry

  theorem correct : (nocM' Data) ⊑ (nocM Data) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable Data)
        (refines_initial Data)
        (refines_φ Data)
    )

end Graphiti.Noc.RouterIn
