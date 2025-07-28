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
    · have : ∃ n, noc' noc = n := by exists noc' noc
      obtain ⟨n, Hn⟩ := this
      -- rw [Hn] at h
      -- revert flit
      -- rw [Hn]
      -- We cannot do induction on h :(
      sorry

  class NocCorrect (noc : Noc Data netsz) where
    routing_policy  : routing_policy_correct (noc' noc)

  variable (noc : Noc Data netsz)
  variable [NC : NocCorrect (noc' noc)]
  -- Maybe we should require BEq and LawfulBEq for all FlitHeader (in the lang), but unsure
  variable [BEq noc.routing_policy.FlitHeader] [LawfulBEq noc.routing_policy.FlitHeader]

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
                simp only [Router.Unbounded.bag.eq_1, RouterID', List.remove.eq_1, Fin.getElem_fin,
                  Noc.Flit, RoutingPolicy.Flit, Flit', modT, Noc.State, noc', Noc.RouterID,
                  Topology.RouterID, BEq.rfl, typeOf, Bool.true_and, beq_eq_false_iff_ne,
                  ne_eq] at Hflit h
                rw [Hrule1] at Hflit
                cases list_mem_concat_either Hflit
                · assumption
                · rename_i h'; cases h' <;> contradiction
              · specialize Hrule2 src (by intro _; subst idx; apply hsrceqidx; rfl)
                -- set_option pp.explicit true in trace_state
                simp only [Router.Unbounded.bag.eq_1, RouterID', List.remove.eq_1, Fin.getElem_fin,
                  Noc.Flit, RoutingPolicy.Flit, Flit', modT, Noc.State, noc', Noc.RouterID,
                  Topology.RouterID] at Hflit ⊢
                rwa [←Hrule2]
            · simp only [Noc.RouterID, Noc.Flit, typeOf, Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [BEq.rfl, Bool.and_self, ↓reduceIte]
              apply NC.routing_policy
          -- routing_function_reconstruct
          · intro v' hv'
            simp only [Noc.RouterID, Topology.RouterID, RouterID', routing_function_reconstruct, noc', RoutingPolicy.Flit,
              Flit', Noc.Flit, typeOf, eq_mp_eq_cast, Bool.and_eq_true, beq_iff_eq, List.mem_flatten, Vector.mem_toList_iff,
              Vector.mem_mapFinIdx] at hv'
            obtain ⟨l, hl1, hl2⟩ := hv'
            obtain ⟨idx_inp, hi1, hi2⟩ := hl1
            subst l
            simp only [Bool.and_eq_true, beq_iff_eq, List.mem_map, Prod.exists, Prod.mk.injEq] at hl2
            obtain ⟨data, dst, HflitIn, HflitEq⟩ := hl2
            cases h: (⟨idx_inp, hi1⟩ == idx && (data, dst) == ((cast Hv v).1,
              noc.routing_policy.mkhead idx (cast Hv v).2 (cast Hv v).1))
            <;> rw [h] at HflitEq
            <;> subst v'
            <;> dsimp
            · simp only [Router.Unbounded.bag.eq_1, RouterID', List.remove.eq_1, Fin.getElem_fin,
                cast_cast, List.mem_append, List.mem_cons, List.not_mem_nil,
                or_false
              ] at ⊢ HflitIn Hrule1
              left
              apply Hrf2
              simp only [noc', RoutingPolicy.Flit, Flit', Noc.RouterID, Topology.RouterID, RouterID',
                routing_function_reconstruct, Noc.Flit, List.mem_flatten, Vector.mem_toList_iff, Vector.mem_mapFinIdx]
              by_cases Heq3: idx = idx_inp
              · subst idx_inp
                rw [Hrule1] at HflitIn
                simp only [
                  List.mem_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
                  or_false
                ] at HflitIn
                cases HflitIn
                · rename_i HflitIn
                  skip
                  apply Exists.intro _
                  and_intros
                  · exists idx.1, idx.2
                  · simp only [Fin.eta, List.mem_map, Prod.mk.injEq, Prod.exists]
                    exists data, dst
                · rename_i HflitIn
                  obtain ⟨rfl, rfl⟩ := HflitIn
                  simp only [Fin.eta, BEq.rfl, typeOf, Bool.and_self, Bool.true_eq_false] at h
              · specialize Hrule2 ⟨idx_inp, hi1⟩ (by sorry)
                sorry
              -- Seems obviously true, it is in the head
              -- apply List.mem_concat_hd
              -- apply Hrf2
            · simp only [typeOf, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              rw [List.mem_append]
              right
              simpa only [cast_cast, List.mem_cons, List.not_mem_nil, or_false]
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
          simp only [noc', RoutingPolicy.Flit, Flit', Noc.RouterID, Topology.RouterID, RouterID',
            routing_function_reconstruct, Noc.Flit, typeOf, eq_mp_eq_cast, List.mem_flatten, Vector.mem_toList_iff,
            Vector.mem_mapFinIdx
          ]
          apply Exists.intro _
          and_intros
          exists idx.1, idx.2
          simp only [Fin.eta, List.mem_map, Prod.mk.injEq, Prod.exists]
          exists (Hv.mp v), head
          have HflitIn : List.Mem (Hv.mp v, head) i[idx] := List.mem_of_getElem Hid2
          and_intros
          · assumption
          · rfl
          · specialize Hrf1 idx (Hv.mp v, head) HflitIn
            generalize (rf idx (Hv.mp v, head)) = dst at Hrf1
            cases Hrf1
            · rename_i f1 f2 f3 f4
              simp only [noc', RoutingPolicy.Flit, Flit', Router.Unbounded.bag.eq_1, RouterID',
                List.remove.eq_1, Fin.getElem_fin, Topology.Dir_out, Topology.out_len, typeOf,
                eq_mp_eq_cast] at f4 Hhead1
              simp only [f4] at Hhead1
              subst f1
              contradiction
            · rfl
      obtain ⟨sidx, Hsidx⟩ := in_list_idx Hvin
      exists s, (List.remove s sidx)
      and_intros
      · constructor
      · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        dsimp [drcomponents]
        exists sidx
        and_intros
        · rfl
        · simp only [Fin.getElem_fin, typeOf, eq_mp_eq_cast] at Hsidx
          simpa only [cast_cast, Hsidx]
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
            simp only [Router.Unbounded.bag.eq_1, RouterID', List.remove.eq_1, Fin.getElem_fin,
              Noc.Flit, RoutingPolicy.Flit, Flit', modT, Noc.State, noc', Noc.RouterID,
              Topology.RouterID] at Hflit ⊢
            rw [Hid1] at Hflit
            apply list_mem_eraseIdx Hflit
          · specialize Hhead3 src Heq
            simp only [noc', RoutingPolicy.Flit, Flit', Router.Unbounded.bag.eq_1, RouterID',
              List.remove.eq_1, Fin.getElem_fin, Noc.Flit, modT, Noc.State, Noc.RouterID,
              Topology.RouterID] at Hhead3 ⊢
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
            if (noc.routing_policy.2 idx_inp val).2 == flit && rid == idx_out
            then rf idx_inp flit
            else rf rid flit
          )
          apply And.intro
          -- routing_function_correct
          · intro src flit Hflit
            -- Are we looking at a modified flit?
            cases Heq1 : src == idx_out
            <;> dsimp at ⊢ Heq1
            <;> rw [Heq1]
            <;> simp [drcomponents, drunfold_defs] at Heq1 flit
            <;> simp [Heq1]
            · -- We are not looking at the modified router, we don't need an extra step
              apply Hrf1
              specialize (H5 src (by intro h; apply Heq1; rw [h]))
              simp only [noc', RoutingPolicy.Flit, Flit', Router.Unbounded.bag.eq_1, RouterID',
                              List.remove.eq_1, Fin.getElem_fin, Noc.Flit, modT, Noc.State, Noc.RouterID,
                Topology.RouterID] at ⊢ H5 Hflit
              rw [←H5]
              by_cases Heq3: idx_inp = src
              · subst src
                rw [H6] at Hflit
                -- TODO: We can conclude by Hflit and Heq2
                sorry
              · specialize H7 _ Heq3
                rwa [←H7]
            · -- We are looking at a modified router.
              -- Are we looking at the modified flit?
              cases Heq2 : (noc.routing_policy.route idx_inp val).2 == flit
              <;> simp [drcomponents, drunfold_defs] at Heq2 flit ⊢
              · -- We are not looking at the modified flit
                -- We don't need an extra step
                apply Hrf1
                subst src
                simp only [noc', RoutingPolicy.Flit, Flit', Router.Unbounded.bag.eq_1, RouterID',
                  List.remove.eq_1, Fin.getElem_fin, Noc.Flit, modT, Noc.State, Noc.RouterID,
                  Topology.RouterID] at Hflit
                by_cases Heq3 : idx_inp = idx_out
                · subst idx_out
                  rw [H6] at Hflit
                  -- TODO: We can conclude with Hflit combined with Heq2
                  sorry
                · specialize H7 _ Heq3
                  rw [H7, H3] at Hflit
                  -- TODO: We can conclude with Hflit
                  sorry
              · -- We are looking at the modified flit
                -- We need to take an extra step in the get_output
                -- We first need to get back the old get_output that we would have
                -- had, and then we apply a step to obtain the final one.
                subst src flit
                have Hstep := Hrf1
                  (src := idx_out)
                  (flit := val)
                  (by
                    apply List.mem_of_getElem
                    simp only [noc', RoutingPolicy.Flit, Flit', Router.Unbounded.bag.eq_1,
                      RouterID', List.remove.eq_1, Fin.getElem_fin, Noc.Flit, modT, Noc.State,
                      Noc.RouterID, Topology.RouterID]
                    exact H4
                    exact H2.2)
                have Hdir : (noc' noc).topology.isConnDir_out dir_out := by
                  exact conns_isConn_out Hconn1
                have h : ∃ tmp, tmp = rf idx_out val := by exists rf idx_out val
                obtain ⟨tmp, htmp⟩ := h
                rw [←htmp] at Hstep
                -- We had a correctness before moving the flit around,
                -- what was it?
                cases Hstep
                -- The correctness was telling us to move to another router
                · subst tmp
                  rename_i dir' hdir' H1' H2'
                  apply get_output.step
                    (hdir := hdir')
                    (flit' := ((noc' noc).routing_policy.route idx_out val).snd)
                  · -- This is true actually!
                    rename_i flit'
                    have : ((noc' noc).routing_policy.route idx_out val).2 = flit' := by
                      rw [H1']
                    rw [this]
                    dsimp
                    sorry -- simp [H1]; rfl
                  · rw [←get_output']
                    dsimp at ⊢ H1'
                    rw [H1']
                    -- have : rf idx_inp (rf idx_inp (noc.routing_policy.route idx_inp val).snd) = rf idx_out val := by
                    --   dsimp at Hrf1
                    --   sorry
                    --   sorry
                    -- rwa [this]
                    sorry
                -- The correctness was saying we should leave,
                -- we should have a contradiction?
                · rename_i dir' Hdir' flit' Hflit'
                  -- This is a bit unclear…
                  -- We should have a contradiction here, right?
                  -- We have that dir_out should be equal to
                  -- ((noc' noc).routing_policy.route idx_out h1').fst
                  -- and Hconn1 gives us that dir_out is not a local dir.

                  -- htmp is very interesting: idx_out = rf idx_out val
                  -- this should give us that
                  -- (noc' noc).routing_policy.route idx_out val = dirlocal,
                  -- which gives us the contradiction
                  -- But this is false, idx_out = rf idx_out val could mean that
                  -- we first have to go out to another router, this modifies
                  -- the flit and send it back to us and then we leave.
                  sorry
          -- routing_function_reconstruct
          · dsimp
            intro flit Hflit
            -- we need to case to see if we have the modified flit or not
            sorry

  theorem correct : (mod (noc' noc)) ⊑ (spec (noc' noc)) := by
    exists inferInstance, φ (noc' noc); solve_by_elim [refines_φ, refines_initial]

end Graphiti.Projects.Noc
