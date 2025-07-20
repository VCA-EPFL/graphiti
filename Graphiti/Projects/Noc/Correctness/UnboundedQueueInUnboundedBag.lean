/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Examples.Noc.Lang
import Graphiti.Examples.Noc.BuildModule
import Graphiti.Examples.Noc.Topology.Torus
import Graphiti.Examples.Noc.Spec
import Graphiti.Examples.Noc.Router

open Batteries (AssocList)

set_option Elab.async false

namespace Graphiti.Noc.DirectedTorusAbsoluteUnboundedCorrect

  variable {netsz : Netsz}
  variable (Data : Type) [BEq Data] [LawfulBEq Data]
  variable (topology : Topology netsz)
  variable (arbiter : Arbiter topology Data)

  @[drunfold_defs]
  def noc_queue : Noc Data netsz :=
    {
      topology := topology
      arbiter := arbiter
      routers := Router.Unbounded.queue netsz arbiter.Flit
    }

  @[drunfold_defs]
  abbrev mod_queue := (noc_queue Data topology arbiter).build_module

  @[drunfold_defs]
  def noc_bag : Noc Data netsz :=
    {
      topology := topology
      arbiter := arbiter
      routers := Router.Unbounded.bag netsz arbiter.Flit
    }

  @[drunfold_defs]
  abbrev mod_bag := (noc_bag Data topology arbiter).build_module

  def φ (I : (noc_queue Data topology arbiter).State) (S : (noc_bag Data topology arbiter).State) : Prop :=
    I = S

  instance : MatchInterface (mod_queue Data topology arbiter) (mod_bag Data topology arbiter) := by
    apply MatchInterface_simpler
    -- FIXME
    <;> simp only [drcomponents, RelIO_mapVal]
    <;> intros _
    <;> rfl

  theorem refines_initial :
    Module.refines_initial (mod_queue Data topology arbiter) (mod_bag Data topology arbiter) (φ Data topology arbiter) := by
      intros s i; exists s

  theorem refines_φ : (mod_queue Data topology arbiter) ⊑_{φ Data topology arbiter} (mod_bag Data topology arbiter) := by
    intros i s H
    <;> dsimp [drcomponents, drunfold_defs] at i s
    constructor
    · intros ident mid_i v Hrule
      case_transition Hcontains : (Module.inputs (mod_queue Data topology arbiter)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      dsimp [drcomponents, drunfold_defs] at v Hrule Hcontains ⊢
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents] at Hrule
      obtain ⟨Hrule1, Hrule2⟩ := Hrule
      exists s.set idx (s[idx].concat ((Hv.mp v).1, arbiter.mkhead idx (Hv.mp v).2 (Hv.mp v).1))
      exists s.set idx (s[idx].concat ((Hv.mp v).1, arbiter.mkhead idx (Hv.mp v).2 (Hv.mp v).1))
      and_intros
      · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        dsimp [drcomponents]
        and_intros
        · simpa only [List.concat_eq_append, Vector.getElem_set_self]
        · intros rid' H
          specialize Hrule2 rid' H
          apply Vector.getElem_set_ne
          sorry -- Should be simp H, but not working :(
      · constructor
      · unfold φ at H
        subst s
        -- We can say `have mid_i = i.set idx ...`, and this could be turned
        -- into an exterior lemma afterward cause it will be useful
        -- Not working because of cast issues...
        -- obtain Htmp := vec_set_reconstruct
        --   (by
        --     intros idx' Hidx'
        --     rewrite [eq_comm] at Hidx'
        --     specialize Hrule2 idx' Hidx'
        --     simpa [Hrule2])
        --   Hrule1
        sorry
    · intros ident mid_i v Hrule
      case_transition Hcontains : (Module.outputs (mod_queue Data topology arbiter)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      dsimp [drcomponents] at v Hrule Hcontains ⊢
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents, drunfold_defs] at Hrule idx
      obtain ⟨Hrule1, ⟨Hrule2, Hrule3⟩, Hrule4⟩ := Hrule
      obtain Htmp := vec_set_reconstruct
        (by
          intros idx' Hidx'
          specialize Hrule4 idx' Hidx'
          simpa [Hrule4])
        Hrule3
      exists s, mid_i
      subst i
      subst s
      and_intros
      · constructor
      · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        dsimp [drcomponents, drunfold_defs]
        exists Hrule1
        and_intros
        · simpa only [Hrule2, cast_cast]
        · exists (Fin.mk 0 (by simpa [Vector.getElem_set_self]))
          simpa only [Vector.getElem_set_self, List.eraseIdx_zero, List.tail_cons]
        · intros rid' Hrid'; rw [Vector.getElem_set_ne]
          -- FIXME: Cast issue
          sorry
      · rfl
    · intros rule mid_i HruleIn Hrule
      exists mid_i
      unfold φ at H
      subst s
      dsimp [drcomponents, drunfold_defs] at HruleIn
      -- FIXME
      obtain ⟨idx, j, Hj⟩ := RelInt.liftFinf_in HruleIn
      have Hrule' : ∃ rule', rule' ∈ (mod_bag Data topology arbiter).internals ∧ rule' i mid_i:= by
        apply Exists.intro _
        and_intros
        · sorry
        · sorry
        -- TODO
        sorry
      obtain ⟨rule', HruleIn2, Hrule2⟩ := Hrule'
      and_intros
      · apply existSR.step i mid_i mid_i _ HruleIn2 Hrule2 (by constructor)
      · rfl

  theorem ϕ_indistinguishable :
    ∀ i s, (φ Data topology arbiter) i s → Module.indistinguishable (mod_queue Data topology arbiter) (mod_bag Data topology arbiter) i s := by
      sorry

  theorem correct : (mod_queue Data topology arbiter) ⊑ (mod_bag Data topology arbiter) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable Data topology arbiter)
        (refines_initial Data topology arbiter)
        (refines_φ Data topology arbiter)
    )
