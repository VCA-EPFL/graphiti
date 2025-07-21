/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.BuildModule
import Graphiti.Projects.Noc.Spec
import Graphiti.Projects.Noc.Router

open Batteries (AssocList)

set_option Elab.async false

namespace Graphiti.Projects.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data]
  variable {netsz : Netsz}
  variable (noc : Noc Data netsz)

  @[drunfold_defs]
  abbrev mod := noc.build_module

  @[drunfold_defs]
  abbrev spec := noc.spec_bag

  -- TODO: We should first require that Routers are correct.
  -- This require that they ⊑ spec_routerBag
  -- We can then use RouterIn to prove full correctness and only use the
  -- spec_routerbag router

  -- We can then use the router inductive correctness definition

  -- inductive output : noc.RouterID → noc.RouterID → noc.Flit → Prop where
  -- | init :
  --   ∀ cur flit dst,
  --     output (noc.arbiter.mkhead cur flit dst)
  -- | done :
  --     ∀ cur flit flit', noc.arbiter.route cur flit = (noc.topology.DirLocal_out, flit')
  --     → True

  def reachable (n : Noc Data netsz) (src dst : n.RouterID) (flit : n.Flit) : Prop :=
    True

  def φ (I : noc.State) (S : noc.spec_bagT) : Prop :=
    -- ∀ src dst flit, reachable noc src dst flit → reachable (spec noc) src dst
    True
    -- TODO: Use an inductive which repeat the steping function
    -- inductive good where

  theorem refines_initial :
    Module.refines_initial (mod noc) (spec noc) (φ noc) := by
      sorry

  theorem refines_φ : (mod noc) ⊑_{φ noc} (spec noc) := by
    intro i s H
    constructor
    · intro ident mid_i v Hrule
      case_transition Hcontains : (Module.inputs (mod noc)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      clear Hcontains
      subst ident
      dsimp [drcomponents] at v Hrule ⊢
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents, drunfold_defs] at Hrule
      obtain ⟨Hrule1, Hrule2⟩ := Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      apply Exists.intro _
      apply Exists.intro _
      · and_intros
        · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
          dsimp [drcomponents]
        · constructor
        · -- dsimp [drcomponents, drunfold_defs] at s
          sorry
    · intros ident mid_i v Hrule
      case_transition Hcontains : (Module.outputs (mod noc)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      clear Hcontains
      subst ident
      dsimp [drcomponents] at v Hrule ⊢
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp at Hrule
      obtain ⟨head, ⟨Hhead1, Hhead2⟩, Hhead3⟩ := Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      apply Exists.intro _
      apply Exists.intro _
      · and_intros
        · constructor
        · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
          dsimp [drcomponents]
          sorry
          sorry
        · sorry
    · intro rule mid_i HruleIn Hrule
      dsimp [drcomponents] at HruleIn
      rw [List.mem_map] at HruleIn
      obtain ⟨conn, Hconn1, Hconn2⟩ := HruleIn
      obtain ⟨conn_out, conn_inp⟩ := conn
      obtain ⟨idx_out, dir_out⟩ := conn_out
      obtain ⟨idx_inp, dir_inp⟩ := conn_inp
      subst rule
      dsimp [drcomponents] at Hrule
      obtain ⟨val, mid_s, ⟨⟨H1, H2⟩, H3⟩, H4, H5⟩ := Hrule
      apply Exists.intro _
      · and_intros
        · constructor
        · sorry

  -- Proven Useless
  theorem ϕ_indistinguishable :
    ∀ i s, (φ noc) i s → Module.indistinguishable (mod noc) (spec noc) i s := by
        sorry

  theorem correct : (mod noc) ⊑ (spec noc) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable noc)
        (refines_initial noc)
        (refines_φ noc)
    )

