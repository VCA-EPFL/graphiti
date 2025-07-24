/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.BuildModule
import Graphiti.Projects.Noc.Spec
import Graphiti.Projects.Noc.Router
import Graphiti.Projects.Noc.Tactic

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

  @[simp, drcomponents]
  def noc' (noc : Noc Data netsz) :=
    { noc with router := Router.Unbounded.bag netsz noc.routing_policy.Flit }

  theorem get_output' {noc : Noc Data netsz} {src dst flit} :
    get_output noc src dst flit ↔ get_output (noc' noc) src dst flit := by
    apply Iff.intro <;> intro h
    · induction h
      · sorry
      · sorry
    · sorry

  class NocCorrect (noc : Noc Data netsz) where
    routing_policy  : routing_policy_correct (noc' noc)

  variable (noc : Noc Data netsz)
  variable [NC : NocCorrect (noc' noc)]
  -- Maybe we should require BEq and LawfulBEq for all FlitHeader, but unsure
  variable [BEq noc.routing_policy.FlitHeader] [LawfulBEq noc.routing_policy.FlitHeader]
  -- The following sould not be necessary, but it does not work otherwise for
  -- some reason.
  -- They could be defined by infer_instance instead of taken as a variable, but
  -- eh
  variable [BEq (noc' noc).routing_policy.FlitHeader] [LawfulBEq (noc' noc).routing_policy.FlitHeader]

  @[simp, drunfold_defs]
  abbrev mod := (noc' noc).build_module

  @[simp, drunfold_defs]
  abbrev modT := (noc' noc).State

  @[simp, drunfold_defs]
  abbrev spec := (noc' noc).spec_bag

  @[simp, drunfold_defs]
  abbrev specT := (noc' noc).spec_bagT

  def routing_function : Type :=
    (src : noc.RouterID) → (flit : noc.Flit) → noc.RouterID

  @[simp]
  def routing_function_correct (rf : routing_function noc) (I : modT noc) : Prop :=
    ∀ (src : noc.RouterID) (flit : noc.Flit),
      List.Mem flit I[src]
      → get_output noc src (rf src flit) flit

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
      exists []
      and_intros
      · rfl
      · exists (λ src _ => src)
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
    -- Input rule
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
        · -- We need to update the routing function to consider the new flit we
          -- just added in the router, and we know that it should be outputted
          -- at the required destination.
          exists (λ src flit =>
            if src == idx
            && flit == ((Hv.mp v).1, noc.routing_policy.mkhead idx (Hv.mp v).2 (Hv.mp v).1)
            then (Hv.mp v).2
            else rf src flit
          )
          apply And.intro
          -- routing_function_correct
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
                simp [drunfold_defs, drcomponents] at Hflit h
                rw [Hrule1] at Hflit
                -- Then, with h, we know that the flit is not in the tail
                sorry
              · specialize Hrule2 src (by intro _; subst idx; apply hsrceqidx; rfl)
                -- set_option pp.explicit true in trace_state
                simp [drunfold_defs, drcomponents] at Hflit ⊢
                rwa [←Hrule2]
            · simp only [Noc.RouterID, Noc.Flit, typeOf, Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [BEq.rfl, Bool.and_self, ↓reduceIte]
              apply NC.routing_policy
          -- routing_function_reconstruct
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
            · simp [drunfold_defs, drcomponents] at ⊢
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
    -- Output rule
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
          and_intros
          exists idx.1, idx.2
          simp
          exists (Hv.mp v), head
          have HflitIn : List.Mem (Hv.mp v, head) i[idx] := List.mem_of_getElem Hid2
          and_intros
          · assumption
          · rfl
          · specialize Hrf1 idx (Hv.mp v, head) HflitIn
            generalize (rf idx (Hv.mp v, head)) = dst at Hrf1
            cases Hrf1
            · rename_i f1 f2 f3 f4
              simp [drunfold_defs, drcomponents] at f4 Hhead1
              simp [f4] at Hhead1
              subst f1
              contradiction
            · rfl
      obtain ⟨sidx, Hsidx⟩ := in_list_idx Hvin
      exists s, (List.remove s sidx)
      · and_intros
        · constructor
        · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
          dsimp [drcomponents]
          exists sidx
          and_intros
          · rfl
          · simp at Hsidx
            simpa [Hsidx]
        · -- We do not need to take extra care for the routing function:
          -- we have less element in the router, so everything in it was also
          -- exactly at the same place in the other router, which in turn means
          -- that the old routing function is still correct
          exists rf
          and_intros
          -- routing_function_correct
          · intro src flit Hflit
            dsimp at src flit
            apply Hrf1
            -- Are we looking at the modified router?
            by_cases Heq: idx = src
            · subst src
              simp [drunfold_defs, drcomponents] at Hflit ⊢
              rw [Hid1] at Hflit
              -- TODO: flit ∈ s.eraseIdx id → flit ∈ s
              sorry
            · specialize Hhead3 src Heq
              simp [drunfold_defs, drcomponents] at Hhead3 ⊢
              rwa [←Hhead3]
          -- routing_function_reconstruct
          · dsimp
            intro flit Hflit
            -- We need a case analysis: flit ∈ a map to list flatten, is it in
            -- simp at Hflit
            -- obtain ⟨l, ⟨i, h, Hil⟩, Hl⟩ := Hflit
            sorry
    -- Internal rule
    · intro rule mid_i HruleIn Hrule
      dsimp [drcomponents] at HruleIn
      rw [List.mem_map] at HruleIn
      obtain ⟨conn, Hconn1, Hconn2⟩ := HruleIn
      obtain ⟨conn_out, conn_inp⟩ := conn
      obtain ⟨idx_out, dir_out⟩ := conn_out
      obtain ⟨idx_inp, dir_inp⟩ := conn_inp
      subst rule
      dsimp [drcomponents] at Hrule
      obtain ⟨val, midest_i, ⟨⟨H1, ⟨H2, ⟨H3, H4⟩⟩⟩, H5⟩, H6, H7⟩ := Hrule
      dsimp [drunfold_defs] at midest_i H1 H2 H3 H4 H5 H6 H7
      apply Exists.intro s
      · and_intros
        · constructor
        · -- The new routing function is updated with our new move:
          -- idx_inp sent the modified flit given by the routing policy to
          -- idx_out
          -- So if we are this modified flit, we can recover the original target
          -- by going back
          exists (λ rid flit =>
            if ((noc' noc).routing_policy.2 idx_inp val).2 == flit && rid == idx_out
            then rf idx_inp flit
            else rf rid flit
          )
          apply And.intro
          -- routing_function_correct
          · intro src flit Hflit
            -- Are we looking at a modified flit?
            cases Heq1 : src == idx_out
            <;> cases Heq2 : ((noc' noc).routing_policy.route idx_inp val).2 == flit
            <;> dsimp at ⊢ Heq1 Heq2
            <;> rw [Heq1, Heq2]
            <;> simp [Heq1, Heq2]
            <;> simp [drcomponents, drunfold_defs] at Heq1 Heq2
            · -- We are not looking at the modified router nor the modified flit,
              -- we don't need an extra step
              apply Hrf1
              specialize (H5 src (by sorry))
              simp [drunfold_defs, drcomponents] at ⊢ H5 Hflit
              rw [←H5]
              by_cases Heq3: idx_inp = src
              · subst src
                rw [H6] at Hflit
                -- TODO: We can conclude by Hflit and Heq2
                sorry
              · specialize H7 _ Heq3
                rwa [←H7]
            · -- We are not looking at the modified router,
              -- we don't need an extra step
              -- FIXME: Why is Heq2 not simplified?
              -- I would guess that the LawfulBEq instance is incorrect
              stop
              subst flit
              apply Hrf1
              sorry
            · -- We are looking at a modified router but not a modified flit,
              -- we don't need an extra step
              subst src
              apply Hrf1
              by_cases Heq3: idx_inp = idx_out
              · subst idx_out
                simp [drcomponents, drunfold_defs] at Hflit H6
                rw [H6, H3] at Hflit
                -- We know by Heq2 that flit is not in the tail of Hflit,
                -- So it must be in i.eraseIdx ...
                -- Which is itself included in i[idx_inp]
                skip
                sorry
              · specialize H7 _ Heq3
                simp [drcomponents, drunfold_defs] at Hflit
                rw [H7, H3] at Hflit
                -- We can conclude with HFlit
                sorry
            · -- We are looking at the modifed router and modified flit!
              -- We need to take an extra step in the get_output
              -- We first need to get back the old get_output that we would have
              -- had, and then we apply a step to obtain the final one.
              -- FIXME: Why is Heq2 not simplified?
              subst src -- flit
              have Hstep := Hrf1
                (src := idx_out)
                (flit := val)
                (by
                  apply List.mem_of_getElem
                  simp [drunfold_defs, drcomponents]
                  exact H4
                  exact H2.2)
              have Hdir : (noc' noc).topology.isConnDir_out dir_out := by
                -- by Hconn1
                sorry
              -- simp at Hstep
              have h : ∃ tmp, tmp = rf idx_out val := by exists rf idx_out val
              obtain ⟨tmp, htmp⟩ := h
              rw [←htmp] at Hstep
              -- generalize (rf idx_out val) = rf_out at Hstep
              -- generalize (noc' noc) = noc'' at Hstep
              -- simp at Hstep
              rw [←get_output'] at Hstep
              -- We had a correctness before moving the flit around.
              cases Hstep
              -- The correctness was telling us to move to another router
              · subst tmp
                rename_i dir' hdir' H1' H2'
                -- we have flitcross = flit by Heq2
                apply get_output.step
                  (hdir := hdir')
                  (flit' := ((noc' noc).routing_policy.route idx_out val).snd)
                · -- This is true actually!
                  sorry -- simp [H1]; rfl
                · dsimp
                  -- we have to show that rf idx_out val = rf idx_inp flit
                  sorry
              -- The correctness was saying we should leave
              · rename_i dir' hdir' h1' h2'
                -- We cannot have a contradiction with H1 because actually
                -- h1 is not val, and we don't have a way to know it is?
                unfold routing_function_correct at Hrf1
                rw [htmp] at h2' ⊢
                skip
                sorry
          -- routing_function_reconstruct
          · dsimp
            intro flit Hflit
            -- we need to case to see if we have the modified flit or not
            sorry

  theorem correct : (mod (noc' noc)) ⊑ (spec (noc' noc)) := by
    exists inferInstance, φ (noc' noc); solve_by_elim [refines_φ, refines_initial]

end Graphiti.Projects.Noc
