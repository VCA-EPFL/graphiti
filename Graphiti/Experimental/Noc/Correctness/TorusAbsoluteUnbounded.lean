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

  variable (Data : Type) [BEq Data] [LawfulBEq Data] (DataS : String)
  variable (dt : DirectedTorus)

  @[drunfold_defs]
  def noc : Noc Data dt.netsz :=
    let topology := dt.to_topology
    let arbiter := dt.AbsoluteArbiter Data
    let routers := Router.Unbounded.queue dt.netsz arbiter.Flit
    { topology, arbiter, routers, DataS}

  @[drunfold_defs]
  abbrev mod := (noc Data DataS dt).build_module

  @[drunfold_defs]
  abbrev spec := (noc Data DataS dt).spec_bag

  @[drunfold_defs]
  abbrev specT := (noc Data DataS dt).spec_bagT

  -- TODO
  -- theorem route_xy_correct : Noc.Route_correct (noc Data dt) := by
  --   intros src dst
  --   dsimp [noc, DirectedTorus.xy_to_noc, DirectedTorus.route_xy]
  --   intros H
  --   cases Hx: (dt.get_x src != dt.get_x dst)
  --   <;> cases Hy: (dt.get_y src != dt.get_y dst)
  --   <;> simp only [Hx, Hy] at H
  --   <;> simp only [bne_eq_false_iff_eq, bne_iff_ne, ne_eq] at Hx Hy
  --   · sorry -- TODO: annoying arithmetic
  --   · simp [DirLocal', DirectedTorus.DirY] at H
  --   · simp [DirLocal'] at H
  --   · simp [DirLocal'] at H

  def φ (I : (noc Data DataS dt).State) (S : specT Data DataS dt) : Prop :=
    I.toList.flatten ⊆ S

  theorem refines_initial :
    Module.refines_initial (mod Data DataS dt) (spec Data DataS dt) (φ Data DataS dt) := by
      dsimp [drcomponents, Module.refines_initial]
      intros i s
      subst i
      exists []
      and_intros
      · rfl
      · unfold φ; simpa [drunfold_defs]

  theorem refines_φ : (mod Data DataS dt) ⊑_{φ Data DataS dt} (spec Data DataS dt) := by
    intro i s H
    constructor
    · intro ident mid_i v Hrule
      case_transition Hcontains : (Module.inputs (mod Data DataS dt)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      dsimp [drcomponents] at v Hrule Hcontains ⊢
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents, drunfold_defs] at Hrule
      obtain ⟨Hrule1, Hrule2⟩ := Hrule
      exists s.concat (Hv.mp v)
      exists s.concat (Hv.mp v)
      and_intros
      · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        simpa [drcomponents]
      · constructor
      · rw [List.concat_eq_append]
        have hEq := vec_set_reconstruct (f := λ i => i ++ [Hv.mp v]) Hrule2 Hrule1
        subst mid_i
        intros flit hflit
        simp at hflit
        obtain ⟨l, hflit1, hflit2⟩ := hflit
        obtain ⟨idx', hidx'⟩ := vec_in_if_idx hflit1
        subst l
        by_cases heq: idx = idx'
        · subst idx'
          simp at hflit2
          cases hflit2
          · unfold φ at H
            have hin : flit ∈ (Vector.toList i).flatten := by
              simp
              exists i[idx]
              apply And.intro
              · apply idx_in_vec; exists idx
              · simpa
            specialize H hin
            simp
            left
            assumption
          · subst flit
            simp only [
              typeOf, eq_mp_eq_cast, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false, or_true
            ]
        · simp at hflit2
          rw [Vector.getElem_set_ne] at hflit2
          · have hin : flit ∈ (Vector.toList i).flatten := by
              simp
              exists i[idx']
              apply And.intro
              · apply idx_in_vec; exists idx'
              · simpa
            specialize H hin
            simp
            left
            assumption
          · cases idx; cases idx'; simp at heq <;> simpa
    · intros ident mid_i v Hrule
      case_transition Hcontains : (Module.outputs (mod Data DataS dt)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      dsimp [drcomponents] at v Hrule Hcontains ⊢
      obtain ⟨idx, Heq⟩ := RelIO.liftFinf_in Hcontains
      clear Hcontains
      subst ident
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp only [RelIO] at Hrule
      obtain ⟨head, ⟨Hrule1, Hrule2⟩, Hrule3⟩ := Hrule
      dsimp only [drcomponents, drunfold_defs] at Hrule1 Hrule2
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      have hv : (Hv.mp v, head) ∈ s := by
        apply H
        simp
        apply Exists.intro i[↑idx]
        and_intros
        · apply idx_in_vec; exists idx
        · simp at Hrule2 ⊢
          -- TODO: Should be true but can't rewrite
          -- rw [Hrule2]
          sorry
      -- We need to show that idx = head, this is done with a correctness for
      -- route_xy
      obtain ⟨idx', Hidx'⟩ := in_list_idx hv
      apply Exists.intro s
      apply Exists.intro (s.remove idx')
      and_intros
      · constructor
      · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        · dsimp only [drcomponents]
          exists idx'
          and_intros
          · rfl
          · simp at Hidx'; simp;
            -- rw [Hidx'];
            sorry
      · unfold φ
        sorry
    · intro rule mid_i HruleIn Hrule
      exists s
      and_intros
      · constructor
      · unfold φ at *
        dsimp [drcomponents] at HruleIn
        rw [List.mem_map] at HruleIn
        obtain ⟨conn, Hconn1, Hconn2⟩ := HruleIn
        subst rule
        obtain ⟨conn_out, conn_inp⟩ := conn
        obtain ⟨idx_out, dir_out⟩ := conn_out
        obtain ⟨idx_inp, dir_inp⟩ := conn_inp
        dsimp [drcomponents] at Hrule
        obtain ⟨val, i', ⟨⟨Hval1, Hval2⟩, Hval3⟩, Hval4, Hval5⟩ := Hrule
        dsimp [drcomponents, drunfold_defs] at Hval1 Hval2 Hval3 Hval4
        apply List.Subset.trans (h₂ := H)
        intro x Hx
        simp only [List.mem_flatten, Vector.mem_toList_iff] at Hx ⊢
        obtain ⟨y, hy1, hy2⟩ := Hx
        obtain ⟨idxy1, hidxy1⟩ := vec_in_if_idx hy1
        subst y
        dsimp [drcomponents, drunfold_defs] at dir_out dir_inp
        have htmp : dir_out - 1 < (dt.neigh_out idx_out).length :=
          by sorry
        by_cases heq: (dt.neigh_out idx_out)[↑dir_out - 1] = idx_inp
        · subst idx_inp
          -- simp only [heq] at Hval4
          -- TODO: Is this true?
          sorry
        · specialize Hval5 idxy1 heq
          by_cases heq2: idx1 = idxy1
          · subst idxy1
            simp at hy2
            exists i[↑idx1]
            and_intros
            · apply idx_in_vec; exists idx1
            · -- dsimp
              -- TODO: Should be true but can't rewrite
              -- rw [Hval2]
              sorry
          · specialize Hval3 idxy1 heq2
            simp at hy2
            exists i[↑idxy1]
            apply And.intro
            · apply idx_in_vec; exists idxy1
            · simp at ⊢ Hval3
              -- TODO: Should be true but can't rewrite
              -- rw [←Hval3]
              sorry

  theorem ϕ_indistinguishable :
    ∀ i s, (φ Data DataS dt) i s → Module.indistinguishable (mod Data DataS dt) (spec Data DataS dt) i s := by
      intros i s Hφ
      constructor
      <;> intros ident new_i v Hrule
      · case_transition Hcontains : (Module.inputs (mod Data DataS dt)), ident,
         (PortMap.getIO_not_contained_false' Hrule)
        obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
        subst ident
        dsimp [drcomponents] at Hrule v ⊢
        rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
        dsimp [drcomponents] at Hrule
        have_hole Hv : typeOf v = _ := by
          unfold typeOf
          rewrite [RelIO.liftFinf_get]
          dsimp
        exists s.concat (Hv.mp v)
        rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        simpa [drcomponents]
      · case_transition Hcontains : (Module.outputs (mod Data DataS dt)), ident,
         (PortMap.getIO_not_contained_false' Hrule)
        obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
        subst ident
        dsimp [drcomponents] at Hrule v ⊢
        rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
        dsimp [drcomponents] at Hrule
        have_hole Hv : typeOf v = _ := by
          unfold typeOf
          rewrite [RelIO.liftFinf_get]
          dsimp
        obtain ⟨head, Hrule1, Hrule2⟩ := Hrule
        -- subst i
        -- obtain ⟨idx', Hidx'⟩ := vec_set_subset_in Hφ
        -- exists s.remove idx'
        -- rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        -- dsimp [drcomponents]
        -- exists idx'; dsimp at Hidx'; and_intros
        -- · rfl
        -- · simp [Hidx']
        -- -- From Hrule1 we have idx = head
        -- -- Then we can conclude from Hidx'
        --   sorry
        sorry

  theorem correct : (mod Data DataS dt) ⊑ (spec Data DataS dt) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable Data DataS dt)
        (refines_initial Data DataS dt)
        (refines_φ Data DataS dt)
    )
