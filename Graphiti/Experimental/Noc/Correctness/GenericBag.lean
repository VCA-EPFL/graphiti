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

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  inductive get_output (noc : Noc Data netsz) : (src dst : noc.RouterID) → noc.Flit → Prop where
  | step cur dst flit flit' dir (hdir : noc.topology.isConnDir_out dir) :
      noc.routing_policy.route cur flit = (dir, flit')
      → get_output noc (noc.topology.getConnDir_out hdir) dst flit'
      → get_output noc cur dst flit
  | done cur flit flit':
      noc.routing_policy.route cur flit = (noc.topology.DirLocal_out, flit')
      → get_output noc cur cur flit'

  def routing_policy_correct (noc : Noc Data netsz) : Prop :=
    ∀ (src dst : (noc.RouterID)) data,
      get_output noc src dst (data, noc.routing_policy.mkhead src dst data)

  -- A weaker, more general version where we don't require that output will
  -- actually leave, but if they do, it has to be at the correct output router
  def routing_policy_correct' (noc : Noc Data netsz) : Prop :=
    ∀ (src dst dst' : (noc.RouterID)) data,
      get_output noc src dst' (data, noc.routing_policy.mkhead src dst data)
      → dst = dst'

  @[drcomponents]
  def noc' (noc : Noc Data netsz) :=
    { noc with router := Router.Unbounded.bag netsz noc.routing_policy.Flit }

  class NocCorrect (noc : Noc Data netsz) where
    routing_policy  : routing_policy_correct (noc' noc)

  variable (noc : Noc Data netsz)
  variable [NC : NocCorrect (noc' noc)]
  variable [BEq noc.routing_policy.FlitHeader] [LawfulBEq noc.routing_policy.FlitHeader]
  -- The following sould not be necessary, but it does not work otherwise for
  -- some reason.
  -- They could be defined by infer_instance instead of taken as a variable
  variable [BEq (noc' noc).routing_policy.FlitHeader] [LawfulBEq (noc' noc).routing_policy.FlitHeader]

  @[drunfold_defs]
  abbrev mod := (noc' noc).build_module

  @[drunfold_defs]
  abbrev modT := (noc' noc).State

  @[drunfold_defs]
  abbrev spec := (noc' noc).spec_bag

  @[drunfold_defs]
  abbrev specT := (noc' noc).spec_bagT

  def routing_function : Type :=
    (src : noc.RouterID) → (flit : noc.Flit) → noc.RouterID

  @[simp]
  def routing_function_correct (rf : routing_function noc) (I : modT noc) : Prop :=
    ∀ (src : noc.RouterID) (flit : noc.Flit),
      List.Mem flit I[src] →
      get_output noc src (rf src flit) flit

  @[simp]
  def routing_function_reconstruct (rf : routing_function noc) (I : modT noc) :=
    I.mapFinIdx (λ i flitList h => flitList.map (λ flit => (flit.1, rf ⟨i, h⟩ flit)))

  def φ (I : (modT (noc' noc))) (S : (specT (noc' noc))) : Prop :=
    ∃ rf : routing_function noc,
      routing_function_correct noc rf I
    ∧ (routing_function_reconstruct noc rf I).toList.flatten ⊆ S

  -- Initial correctness relies on the fact that routers of the noc are correct
  -- (Since they are effectively bag routers)
  omit NC [BEq noc.routing_policy.FlitHeader] [LawfulBEq noc.routing_policy.FlitHeader] in
  theorem refines_initial :
    Module.refines_initial (mod (noc' noc)) (spec (noc' noc)) (φ (noc' noc)) := by
      intro i h
      dsimp [drcomponents, drunfold_defs] at h
      subst i
      apply Exists.intro []
      apply And.intro
      · rfl
      · apply Exists.intro (λ src _ => src)
        apply And.intro
        · intro src flit h
          simp only [Fin.getElem_fin, Vector.getElem_replicate] at h
          contradiction
        · simpa only [
            routing_function_reconstruct, Noc.Flit, List.subset_nil,
            List.flatten_eq_nil_iff,
            Vector.mem_toList_iff, Vector.mem_mapFinIdx,
            Vector.getElem_replicate, List.map_nil, List.nil_eq, exists_prop,
            exists_and_right, and_imp, imp_self, implies_true
          ]

  theorem refines_φ : (mod (noc' noc)) ⊑_{φ (noc' noc)} (spec (noc' noc)) := by
    intro i s ⟨rf, Hrf1, Hrf2⟩
    constructor
    -- Input case
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
        ·
          -- We need to update the routing function to consider the new flit we
          -- just added in the router, and we know that it should be outputted
          -- at the required destination.
          apply Exists.intro (λ src flit =>
            if src == idx
            && flit == ((Hv.mp v).1, noc.routing_policy.mkhead idx (Hv.mp v).2 (Hv.mp v).1)
            then (Hv.mp v).2
            else rf src flit
          )
          apply And.intro
          · intro src flit Hflit
            cases h: (
              src == idx &&
              flit == ((cast Hv v).fst, noc.routing_policy.mkhead idx (cast Hv v).snd (cast Hv v).fst)
            )
            <;> dsimp at ⊢ Hrf1 Hrf2 flit src
            · rw [h]
              apply Hrf1
              by_cases hsrceqidx: src = idx
              · subst src
                simp at Hflit h
                -- rw [Hrule1] at Hflit
                -- Then, with h, we know that the flit is not in the tail
                sorry
              · specialize Hrule2 src (by intro _; subst idx; apply hsrceqidx; rfl)
                -- rw [←Hrule2]
                -- assumption
                sorry
            · simp only [Noc.RouterID, Noc.Flit, typeOf, Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [BEq.rfl, Bool.and_self, ↓reduceIte]
              apply NC.routing_policy
          · intro v' hv'
            simp at hv'
            obtain ⟨l, hl1, hl2⟩ := hv'
            obtain ⟨i, hi1, hi2⟩ := hl1
            subst l
            simp at hl2
            obtain ⟨data, dst, HflitIn, HflitEq⟩ := hl2
            cases h: (⟨i, hi1⟩ == idx && (data, dst) == ((cast Hv v).1,
              noc.routing_policy.mkhead idx (cast Hv v).2 (cast Hv v).1))
            <;> rw [h] at HflitEq
            <;> subst v'
            <;> dsimp
            ·
              unfold routing_function_correct at Hrf1
              unfold routing_function_reconstruct at Hrf2
              -- Seems obviously true, it is in the head
              -- apply List.mem_concat_hd
              -- apply Hrf2
              sorry
            · simp only [typeOf, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              -- Obviously true, it is in the tail
              sorry
    -- Output case
    · intros ident mid_i v Hrule
      case_transition Hcontains : (Module.outputs (mod noc)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      clear Hcontains
      subst ident
      dsimp [drcomponents] at v Hrule ⊢
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drunfold_defs] at Hrule
      obtain ⟨head, ⟨Hhead1, ⟨id, Hid1, Hid2⟩⟩, Hhead3⟩ := Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      have Hvin : (Hv.mp v, idx) ∈ s :=
        by
          apply Hrf2
          simp
          apply Exists.intro _
          apply And.intro
          -- idx should be equal to rf idx flit
          -- we should be able to have get_output flit (rf idx flit) = idx
          -- and then by Hhead1, we can do an inversion and obtain this result
          -- So this is very probably true
          sorry
          · sorry
          · sorry
      obtain ⟨sidx, Hsidx⟩ := in_list_idx Hvin
      apply Exists.intro s
      apply Exists.intro (List.remove s sidx)
      · and_intros
        · constructor
        · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
          dsimp [drcomponents]
          apply Exists.intro sidx
          apply And.intro
          · rfl
          · simp at Hsidx
            simpa [Hsidx]
        · -- We do not need to take extra care for the routing function:
          -- we have less element in the router, so everything in it was also
          -- exactly at the same place in the other router, which in turn means
          -- that the old routing function is still correct
          apply Exists.intro rf
          apply And.intro
          · intro src flit Hflit
            dsimp at src flit
            -- Are we looking at the modified router?
            by_cases Heq: idx = src
            · subst src
              -- We could case on if flit = (Hv.mp v, head), which is the only
              -- hard part
              -- In this case, then we should be able to apply the done or a
              -- step?
              -- Are we looking at the modified flit?
              by_cases Heq2: flit = (Hv.mp v, head)
              · subst flit
                apply get_output.step
                · dsimp
                · dsimp
                  sorry
                · sorry
              · apply Hrf1
                -- TODO:
                -- rw [Hid1] at Hflit
                -- flit ∈ i[idx].erase id ∧ flit != i[idx][id] can conclude
                sorry
            · apply Hrf1
              specialize Hhead3 src Heq
              simp
              -- TODO: Why does this not work? Should be enough
              -- rw [←Hhead3]
              -- exact Hflit
              sorry
          · sorry
    -- Internal rule case
    · intro rule mid_i HruleIn Hrule
      dsimp [drcomponents] at HruleIn
      rw [List.mem_map] at HruleIn
      obtain ⟨conn, Hconn1, Hconn2⟩ := HruleIn
      obtain ⟨conn_out, conn_inp⟩ := conn
      obtain ⟨idx_out, dir_out⟩ := conn_out
      obtain ⟨idx_inp, dir_inp⟩ := conn_inp
      subst rule
      dsimp [drcomponents] at Hrule
      obtain ⟨val, mid_s, ⟨⟨H1, ⟨H2, ⟨H3, H4⟩⟩⟩, H5⟩, H6, H7⟩ := Hrule
      dsimp [drunfold_defs] at mid_s H1 H2 H3 H4 H5 H6 H7
      apply Exists.intro _
      · and_intros
        · constructor
        · apply Exists.intro (λ rid flit =>
            if ((noc' noc).routing_policy.2 idx_inp val).2 == flit && rid == idx_out
            then rf idx_inp flit
            else rf rid flit
          )
          apply And.intro
          · intro src flit Hflit
            cases h: (((noc' noc).routing_policy.2 idx_inp val).2 == flit && src == idx_out)
            <;> dsimp
            <;> rw [h]
            <;> dsimp
            · apply Hrf1
              sorry
            · simp at h
              obtain ⟨rfl, rfl⟩ := h
              have tmp := Hrf1
                (src := idx_inp)
                (flit := ((noc' noc).routing_policy.route idx_inp val).snd)
                -- TODO: This sorry is annoying to prove.
                -- It might not even be true?
                (by sorry)
              -- TODO: Why does this not work?
              -- cases tmp
              sorry

              -- -- We basically need to do an inversion on the get_output we can
              -- -- get from Hrf1?
              -- apply get_output.step
              --   (dst := rf idx_inp val)
              --   (hdir := conns_isConn_out Hconn1)
              --   (flit' := ((noc' noc).routing_policy.route idx_inp val).snd)
              -- · subst dir_out;
              --   simp
              --   rfl
              --   congr
              --   -- rfl
              -- · -- we need to apply Hrf1 now?
              --   have tmp := Hrf1
              --   unfold routing_function_correct at tmp
              --   -- specialize tmp (src := idx_inp)
              --   dsimp
              --   -- We need to prove that
              --   -- ((noc' noc).topology.neigh_out src)[↑dir_out - 1] = idx_inp
              --   -- Which relies on the correctness of .conns
              --   have Hconns_correct :
              --     ((noc' noc).topology.getConnDir_out (conns_isConn_out Hconn1)) = idx_inp
              --     := by sorry
              --   rw [Hconns_correct]
              --   specialize tmp (src := idx_inp)
              --   sorry
              -- · dsimp
              -- · dsimp at Hrf1
              --   specialize Hrf1 (dst := dir_out)
              --   -- apply Hrf1
              --   sorry
              -- · sorry
          · sorry

  theorem correct : (mod (noc' noc)) ⊑ (spec (noc' noc)) := by
    exists inferInstance, φ (noc' noc); solve_by_elim [refines_φ, refines_initial]

end Graphiti.Projects.Noc
