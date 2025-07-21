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

namespace Graphiti.Projects.Noc

  variable (Data : Type) [BEq Data] [LawfulBEq Data] (netsz : Netsz)

  class RouterParam where
    noc : Noc Data netsz
    router' : Router netsz noc.Flit

  variable [RP : @RouterParam Data (by infer_instance) (by infer_instance) netsz]

  abbrev noc' : Noc Data netsz :=
    {
      topology  := RP.noc.topology
      arbiter   := RP.noc.arbiter
      routers   := RP.router'
      DataS     := RP.noc.DataS
    }

  abbrev nocM := RP.noc.build_module
  abbrev nocM' := (noc' Data netsz).build_module

  abbrev routerS := RP.noc.spec_router
  abbrev routerS' := (noc' Data netsz).spec_router

  variable (ROK : ∀ rid : RP.noc.RouterID, (routerS' Data netsz rid) ⊑ (routerS Data netsz rid))

  def φ (I : (noc' Data netsz).State) (S : RP.noc.State) : Prop :=
    ∀ (rid : (noc' Data netsz).RouterID), (ROK rid).2.choose I[rid] S[rid]

  instance : MatchInterface (nocM' Data netsz) (nocM Data netsz) := by
    apply MatchInterface_simpler
    <;> intros ident
    <;> simpa only [drcomponents, RelIO.mapVal]

  theorem refines_initial :
    Module.refines_initial (nocM' Data netsz) (nocM Data netsz) (φ Data netsz ROK) := by
      intros i H
      dsimp [drcomponents]
      apply Exists.intro _
      and_intros
      · rfl
      · intro rid
        obtain ⟨Hspec1, Hspec2⟩ := Exists.choose_spec ((ROK rid).2)
        dsimp [Module.refines_initial] at Hspec1 Hspec2
        specialize Hspec2 i[rid]
        dsimp [drcomponents] at H
        subst i
        simp only [Fin.getElem_fin, Vector.getElem_replicate] at Hspec2 ⊢
        dsimp [routerS', noc'] at Hspec2
        specialize Hspec2 (by rfl)
        obtain ⟨s, Hs1, Hs2, Hs3⟩ := Hspec2
        dsimp [drcomponents] at Hs1
        subst s
        assumption

  theorem refines_φ : (nocM' Data netsz) ⊑_{φ Data netsz ROK} (nocM Data netsz) := by
    intro i s Hφ
    constructor
    · intro ident mid_i v Hrule
      case_transition Hcontains : (Module.inputs (nocM' Data netsz)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      obtain ROK' := Module.refines_refines' (ROK idx)
      obtain ⟨Hok, -, -⟩ := Exists.choose_spec (ROK'.2)
      dsimp at Hok
      specialize Hok i[idx] s[idx] (by sorry) -- sorry should be (Hφ idx)?
      obtain ⟨Hok_inp, -, -⟩ := Hok
      specialize Hok_inp (InternalPort.map NatModule.stringify_input ident)
      clear Hcontains
      subst ident
      dsimp [drcomponents] at v Hrule ⊢
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp at Hrule
      have_hole Hv :
        typeOf v = ((routerS' Data netsz idx).inputs.getIO (InternalPort.map NatModule.stringify_input { inst := InstIdent.top, name := ↑idx })).1 := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp [routerS', noc', Noc.spec_router, Noc.spec_router',
        NatModule.stringify, Module.mapIdent, PortMap.getIO]
        rw [AssocList.mapKey_find?]
        dsimp [drcomponents]
        rw [←PortMap.getIO]
        -- rw [RelIO.liftFinf_get]
        sorry
        sorry
      have_hole HHrule :
        typeOf Hrule = ((routerS' Data netsz idx).inputs.getIO
          (InternalPort.map NatModule.stringify_input { inst := InstIdent.top, name := ↑idx })).snd
          i[idx] (Hv.mp v) mid_i[idx] := by
            sorry
      specialize Hok_inp mid_i[idx] (Hv.mp v) (HHrule.mp Hrule)
      obtain ⟨almost_mid_s, mid_s, Hinp1, Hinp2, Hinp3⟩ := Hok_inp
      simp only [drcomponents] at Hinp2
      cases Hinp2
      exists Vector.set s idx almost_mid_s
      exists Vector.set s idx almost_mid_s
      and_intros
      · -- How can this not be type correct
        -- rw [RelIO.liftFinf_get]
        sorry
      · constructor
      · intro rid
        by_cases heq: rid = idx
        · subst rid
          simp only [Fin.getElem_fin, Vector.getElem_set_self]
          simp at Hinp3
          -- assumption
          sorry
        · have h : ↑idx ≠ ↑rid := by sorry
          conv =>
            arg 3
            simp
            rw [Vector.getElem_set_ne (h := by
              intros h; apply heq; cases rid; cases idx; congr; simp at h; rw [h])]
          specialize Hφ rid
          dsimp [drcomponents] at Hrule
          obtain ⟨-, Hrule2⟩ := Hrule
          specialize Hrule2 rid (by simpa [heq])
          simp only [Fin.getElem_fin] at ⊢ Hφ
          simpa [Hrule2]
      · contradiction
    · intro ident mid_i v Hrule
      case_transition Hcontains : (Module.outputs (nocM' Data netsz)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      clear Hcontains
      obtain ROK' := Module.refines_refines' (ROK idx)
      obtain ⟨Hok, -, -⟩ := Exists.choose_spec (ROK'.2)
      dsimp at Hok
      specialize Hφ idx
      specialize Hok i[idx] s[idx] (by sorry) -- sorry should be Hφ?
      obtain ⟨-, Hok_out, -⟩ := Hok
      specialize Hok_out (InternalPort.map NatModule.stringify_output ident)
      subst ident
      dsimp [drcomponents] at v Hrule ⊢
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp at Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      dsimp [drcomponents] at Hok_out
      specialize Hok_out mid_i[idx]
      -- We need to simplify types of Hok_out arguments but then we are done?
      -- specialize Hok_out (Hv.mp v) Hrule
      sorry
    · intro rule mid_i HruleIn Hrule
      dsimp [drcomponents] at HruleIn
      simp only [List.mem_map, Prod.exists] at HruleIn
      obtain ⟨conn_out, conn_inp, Hconn1, Hconn2⟩ := HruleIn
      obtain ROK_out := Module.refines_refines' (ROK conn_out.1)
      obtain ROK_inp := Module.refines_refines' (ROK conn_inp.1)
      obtain ⟨Hok_inp1, Hok_out1, Hok_int1⟩ := Exists.choose_spec ROK_inp
      obtain ⟨Hok_inp2, Hok_out2, Hok_int2⟩ := Exists.choose_spec ROK_out
      -- specialize Hφ idx
      -- specialize Hok i[idx] s[idx] (by sorry) -- sorry should be Hφ?
      -- obtain ⟨-, Hok_out, -⟩ := Hok
      -- specialize Hok_out (InternalPort.map NatModule.stringify_output ident)
      subst rule
      dsimp [drcomponents] at Hrule
      obtain ⟨val, mid_s, ⟨Hmid_s1, Hmid_s2⟩, ⟨Hmid_s3, Hmid_s4⟩⟩ := Hrule
      sorry

  -- Proven useless
  theorem ϕ_indistinguishable :
    ∀ i s, (φ Data netsz ROK) i s → Module.indistinguishable (nocM' Data netsz) (nocM Data netsz) i s := by
      sorry

  theorem correct : (nocM' Data netsz) ⊑ (nocM Data netsz) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable Data netsz)
        (refines_initial Data netsz ROK)
        (refines_φ Data netsz ROK)
    )

end Graphiti.Projects.Noc
