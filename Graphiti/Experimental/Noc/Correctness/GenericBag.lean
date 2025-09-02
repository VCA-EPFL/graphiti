/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.BuildModule
import Graphiti.Projects.Noc.Spec
import Graphiti.Projects.Noc.Buffer
import Graphiti.Projects.Noc.Lemmas

open Batteries (AssocList)

set_option Elab.async false

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

  -- get_output is deterministic, and thus the destination must be unique
  theorem get_output_unique {noc : Noc Data netsz}
    {src dst dst' : noc.RouterID} {src_flit : noc.Flit} {dst_data dst_data' : Data} :
    get_output noc src dst src_flit dst_data →
    get_output noc src dst' src_flit dst_data' →
    dst = dst' ∧ dst_data = dst_data' := by
      intro h1
      induction h1 with
      | step src dst src_flit mid_flit dst_data dir hdir h1_1 h1_2 HR => sorry
      | done src src_flit dst_flit => sorry

  -- This correctness is partial. It requires that the data is exactly the same
  -- in the end.
  -- This is true because we want to show that the noc behave as a bag, but it
  -- would also be nice that it behaves like a bag + a pure function applied to
  -- it.
  def routing_policy_correct (noc : Noc Data netsz) : Prop :=
    ∀ (src dst : (noc.RouterID)) data,
      get_output noc src dst (data, noc.routing_policy.mkhead src dst data) data

  -- A weaker, more general version where we don't require that output will
  -- actually leave, but if they do, it has to be at the correct output router
  def routing_policy_correct' (noc : Noc Data netsz) : Prop :=
    ∀ (src dst dst' : (noc.RouterID)) data data',
      get_output noc src dst' (data, noc.routing_policy.mkhead src dst data) data'
      → dst = dst' ∧ data = data'

  @[simp, drcomponents]
  def noc' (noc : Noc Data netsz) :=
    { noc with buffer := Buffer.Unbounded.bag netsz noc.routing_policy.Flit }

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
    (src : noc.RouterID) → (flit : noc.Flit) → (Data × noc.RouterID)

  @[simp]
  def routing_function_correct (rf : routing_function noc) (I : modT noc) : Prop :=
    ∀ (src : noc.RouterID) (flit : noc.Flit),
      List.Mem flit I[src] →
      get_output noc src (rf src flit).2 flit (rf src flit).1

  @[simp]
  def routing_function_reconstruct (rf : routing_function noc) (I : modT noc) :=
    I.mapFinIdx (λ i flits h => flits.map (rf ⟨i, h⟩))
    |>.toList |>.flatten

  def φ (I : (modT (noc' noc))) (S : (specT (noc' noc))) : Prop :=
    ∃ rf : routing_function noc,
      routing_function_correct noc rf I
    -- We could use Setoids with ≈ but does not seem to work well
    -- We would like to use Quotient but I don't know how to…
    -- Quotient.mk (
    ∧ (routing_function_reconstruct _ rf I).Perm S

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
      · exists (λ src flit => (flit.1, src))
        apply And.intro
        · intro src flit h
          simp only [Fin.getElem_fin, Vector.getElem_replicate] at h
          contradiction
        · simpa only [
            routing_function_reconstruct, List.perm_nil,
            List.flatten_eq_nil_iff, Vector.mem_toList_iff, Vector.mem_mapFinIdx,
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
        dsimp [drcomponents, drunfold_defs]
      apply Exists.intro _
      apply Exists.intro _
      · and_intros
        · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
          dsimp [drcomponents]
        · constructor
        · -- We need to update the routing function to consider the new flit we
          -- just added in the router (v), and we know that it should be
          -- outputted at the required destination.
          exists (λ src flit =>
            if src == idx
            && flit == ((Hv.mp v).1, noc.routing_policy.mkhead idx (Hv.mp v).2 (Hv.mp v).1)
            then Hv.mp v
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
                simp only [Buffer.Unbounded.bag.eq_1, RouterID', List.remove.eq_1, Fin.getElem_fin,
                  Noc.Flit, RoutingPolicy.Flit, Flit', modT, Noc.State, noc', Noc.RouterID,
                  Topology.RouterID, BEq.rfl, typeOf, Bool.true_and, beq_eq_false_iff_ne,
                  ne_eq] at Hflit h
                rw [Hrule1] at Hflit
                cases list_mem_concat_either Hflit with
                | inl Hflit' => assumption
                | inr Hflit' => cases Hflit' <;> contradiction
              · specialize Hrule2 src (by intro _; subst idx; apply hsrceqidx; rfl)
                simp only [Buffer.Unbounded.bag.eq_1, RouterID', List.remove.eq_1, Fin.getElem_fin,
                  Noc.Flit, RoutingPolicy.Flit, Flit', modT, Noc.State, noc', Noc.RouterID,
                  Topology.RouterID] at Hflit ⊢
                rwa [←Hrule2]
            · simp only [Noc.RouterID, Noc.Flit, typeOf, Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [BEq.rfl, Bool.and_self, ↓reduceIte]
              apply NC.routing_policy
          -- routing_function_reconstruct
          · simp
            rw [vec_set_reconstruct
              (f := λ i => i ++ [((Hv.mp v).1, noc.routing_policy.mkhead idx
              (Hv.mp v).2 (Hv.mp v).1)]) Hrule2 Hrule1
            ]
            rw [vec_set_map]
            simp only [
              Bool.and_eq_true, beq_iff_eq, Fin.eta, BEq.rfl, Bool.true_and,
              Fin.getElem_fin, typeOf, eq_mp_eq_cast, List.map_append,
              List.map_cons, Bool.and_self, ↓reduceIte, List.map_nil
            ]
            rw [vec_set_toList]
            rw [list_set_flatten (hidx := by simpa)]
            rw [←List.insertIdx_length_self]
            apply list_Perm_insertIdx (hidx2 := by simpa)
            · apply List.Perm.trans _ Hrf2
              rw [←vec_set_toList, ←vec_set_map]
              have :
                rf idx ((Hv.mp v).1, noc.routing_policy.mkhead idx (Hv.mp v).2 (Hv.mp v).1)
                = Hv.mp v := by
                  dsimp at Hrf1
                  have tmp := Hrf1 idx
                  have tmp2 := NC.routing_policy
                  unfold routing_policy_correct at tmp2
                  specialize tmp2 idx (Hv.mp v).2 (Hv.mp v).1
                  specialize tmp
                    ((Hv.mp v).1, noc.routing_policy.mkhead idx (Hv.mp v).2 (Hv.mp v).1)
                    (by sorry)
                  have ⟨tmp3, tmp4⟩ := get_output_unique tmp tmp2
                  cases heq: (rf idx ((Hv.mp v).1, noc.routing_policy.mkhead idx (Hv.mp v).2 (Hv.mp v).1))
                  rw [heq] at tmp3 tmp4
                  dsimp at tmp3 tmp4
                  rw [tmp3, tmp4]
                  rfl
               -- We need to rewrite `this` inside the if, which is annoying to
               -- do
              -- TODO:
              -- rw [Vector.set_getElem_self] is not working for some reason
              unfold routing_function_reconstruct
              sorry
            · simp
              -- TODO, annoying
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
      obtain ⟨out_head, out_flit, ⟨Hrule1, ⟨Hrule2, ⟨Hrule3_1, Hrule3_2, Hrule3_3⟩⟩, Hrule4⟩⟩ := Hrule
      simp [
        drunfold_defs, drcomponents
      ] at out_head out_flit Hrule1 Hrule2 Hrule3_1 Hrule3_2 Hrule3_3 Hrule4
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp [drunfold_defs, drcomponents]
      have Hvin : (Hv.mp v, idx) ∈ s :=
        by
          apply list_perm_in Hrf2
          simp only [
            routing_function_reconstruct, typeOf, eq_mp_eq_cast, List.mem_flatten,
            Vector.mem_toList_iff, Vector.mem_mapFinIdx
          ]
          have HflitIn : List.Mem out_flit i[idx] :=
            List.mem_of_getElem Hrule3_3
          apply Exists.intro _
          and_intros
          · exists idx.1, idx.2
          · specialize Hrf1 idx out_flit HflitIn
            have ⟨rf_out, Hrf_out⟩ : ∃ x, x = rf idx out_flit := by
              exists rf idx (out_flit.1, out_flit.2)
            have ⟨rf_out1, Hrf_out1⟩ : ∃ x, x = rf_out.1 := by
              exists rf_out.1
            have ⟨rf_out2, Hrf_out2⟩ : ∃ x, x = rf_out.2 := by
              exists rf_out.2
            rw [←Hrf_out, ←Hrf_out1, ←Hrf_out2] at Hrf1
            cases Hrf1
            · rename_i f1 f2 f3 f4
              simp only [
                noc', RoutingPolicy.Flit, Flit', Buffer.Unbounded.bag.eq_1,
                RouterID', List.remove.eq_1, Fin.getElem_fin, Topology.Dir_out,
                Topology.out_len, typeOf, eq_mp_eq_cast
              ] at f3 Hrule1
              simp only [f3] at Hrule1
              injections
              subst f1
              contradiction
            · rename_i f1 f2
              simp only [
                noc', RoutingPolicy.Flit, Flit', Noc.RouterID, Topology.RouterID,
                RouterID', Noc.Flit, Fin.eta, List.mem_map
              ]
              exists out_flit
              and_intros
              · assumption
              · rw [←Hrf_out]
                cases rf_out
                rename_i rf_out1 rf_out2
                dsimp at Hrf_out1 Hrf_out2
                rw [←Hrf_out1, ←Hrf_out2]
                congr
                simp at f2
                rw [Hrule1] at f2
                injection f2 with _ f2
                rw [←f2]
      obtain ⟨sidx, Hsidx⟩ := in_list_idx Hvin
      exists s, (List.remove s sidx)
      and_intros
      · constructor
      · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        dsimp [drcomponents]
        exists sidx
        and_intros
        · rfl
        · simp [drunfold_defs, drcomponents] at Hsidx
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
          · -- Yes, we are
            subst src
            simp only [Buffer.Unbounded.bag.eq_1, RouterID', List.remove.eq_1,
              Fin.getElem_fin, Noc.Flit, RoutingPolicy.Flit, Flit', modT,
              Noc.State, noc', Noc.RouterID, Topology.RouterID
            ] at Hflit ⊢
            rw [Hrule3_2] at Hflit
            apply list_mem_eraseIdx Hflit
          · -- No, we are not
            specialize Hrule4 src Heq
            simp [drcomponents, drunfold_defs] at Hrule4 ⊢
            rwa [←Hrule4]
        -- routing_function_reconstruct
        · rw [vec_set_reconstruct (f := λ i => i.eraseIdx Hrule3_1) Hrule4 Hrule3_2]
          dsimp
          rw [vec_set_map]
          rw [list_map_eraseIdx]
          rw [vec_set_toList]
          have ⟨idx', Hidx'1, Hidx'2⟩ := list_set_eraseIdx
            (l := (Vector.mapFinIdx i (λ i flits h => List.map (rf ⟨i, h⟩) flits)).toList)
            (idx := idx)
            (l1 := (List.map (rf idx) i[↑idx]))
            (idx1 := Hrule3_1)
            (hidx1 := by sorry)
            (hidx := by sorry)
          simp [drcomponents, drunfold_defs] at ⊢ Hidx'1
          rw [Hidx'1]
          apply list_Perm_eraseIdx
          · simp [drunfold_defs, drcomponents] at Hsidx Hidx'2 ⊢
            rw [Hrule3_3] at Hidx'2
            rw [Hsidx]
            obtain Hrule1' := Hrf1 idx out_flit (by sorry)
            have ⟨x, Hx⟩ : ∃ x, (rf idx out_flit) = x := by exists rf idx out_flit
            rw [Hx] at Hrule1'
            obtain ⟨x1, x2⟩ := x; dsimp only at Hrule1'
            cases Hrule1' with
            | step src dst src_flit mid_flit dst_data dir hdir h1 h2 =>
              dsimp at h1
              rw [Hrule1] at h1
              injections h1
              subst dir
              contradiction
            | done src src_flit dst_flit h1 =>
              dsimp at h1
              rw [Hrule1] at h1
              injections h1
              rename_i h1_1 h1_2
              subst dst_flit
              dsimp at Hx
              rw [Hx] at Hidx'2
              simp only [Hidx'2]
              rfl
          · apply List.Perm.trans _ Hrf2
            rw [←vec_set_toList, ←vec_set_map, Vector.set_getElem_self]
            exact List.Perm.rfl
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
      obtain ⟨val, midest_i, ⟨out_val, H1, ⟨H2, ⟨H3, H4, H5⟩⟩, H6⟩, H7, H8⟩ := Hrule
      dsimp [drunfold_defs] at val midest_i out_val H1 H2 H3 H4 H5 H6 H7 H8
      apply Exists.intro s
      · and_intros
        · constructor
        · -- The new routing function is updated with our new move:
          -- idx_inp sent the modified flit given by the routing policy to
          -- idx_out
          -- So if we are this modified flit, we can recover the original target
          -- by going back
          exists (λ rid flit =>
            if val == flit && rid == idx_inp
            then rf idx_out out_val
            else rf rid flit
          )
          apply And.intro
          -- routing_function_correct
          · intro src flit Hflit
            -- Are we looking at the modified router ?
            cases Heq1 : src == idx_inp
            <;> dsimp at ⊢ Heq1
            <;> rw [Heq1]
            <;> simp [drcomponents, drunfold_defs] at Heq1 flit
            <;> simp [Heq1]
            · -- We are not looking at the modified router, we don't need an extra step
              apply Hrf1
              specialize (H8 src (by intro h; apply Heq1; rw [h]))
              simp only [noc', RoutingPolicy.Flit, Flit', Buffer.Unbounded.bag.eq_1, RouterID',
                              List.remove.eq_1, Fin.getElem_fin, Noc.Flit, modT, Noc.State, Noc.RouterID,
                Topology.RouterID] at ⊢ H5 Hflit
              rw [H8] at Hflit
              by_cases Heq3: idx_out = src
              · subst src
                rw [H4] at Hflit
                exact list_mem_eraseIdx Hflit
              · specialize H6 _ Heq3
                rwa [←H6]
            · -- We are looking at a modified router.
              -- Are we looking at the modified flit?
              cases Heq2 : val == flit
              <;> simp [drcomponents, drunfold_defs] at Heq2 flit ⊢
              · -- We are not looking at the modified flit
                -- We don't need an extra step
                apply Hrf1
                subst src
                simp only [noc', RoutingPolicy.Flit, Flit', Buffer.Unbounded.bag.eq_1, RouterID',
                  List.remove.eq_1, Fin.getElem_fin, Noc.Flit, modT, Noc.State, Noc.RouterID,
                  Topology.RouterID] at Hflit
                by_cases Heq3 : idx_inp = idx_out
                · subst idx_out
                  rw [H7, H4] at Hflit
                  cases list_mem_concat_either Hflit with
                  | inl Hflit' => apply list_mem_eraseIdx Hflit'
                  | inr Hflit' => cases Hflit' <;> contradiction
                · specialize H8 _ Heq3
                  specialize H6 idx_inp (by intro H; apply Heq3; rw [H])
                  rw [H7, H6] at Hflit
                  have Hflit' := list_mem_concat_either Hflit
                  cases list_mem_concat_either Hflit with
                  | inl Hflit' => exact Hflit'
                  | inr Hflit' => cases Hflit' <;> contradiction
              · -- We are looking at the modified flit
                -- We need to take an extra step in the get_output
                -- We first need to get back the old get_output that we would have
                -- had, and then we apply a step to obtain the final one.
                subst src flit
                have Hstep := Hrf1
                  (src := idx_out)
                  (flit := out_val)
                  (by
                    apply List.mem_of_getElem
                    simp only [noc', RoutingPolicy.Flit, Flit', Buffer.Unbounded.bag.eq_1,
                      RouterID', List.remove.eq_1, Fin.getElem_fin, Noc.Flit, modT, Noc.State,
                      Noc.RouterID, Topology.RouterID]
                    exact H5
                    exact H3.2)
                have Hdir : (noc' noc).topology.isConnDir_out dir_out := by
                  exact conns_isConn_out Hconn1
                have ⟨tmp1, htmp1⟩ : ∃ tmp1, tmp1 = (rf idx_out out_val).1 := by
                  exists (rf idx_out out_val).1
                have ⟨tmp2, htmp2⟩ : ∃ tmp2, tmp2 = (rf idx_out out_val).2 := by
                  exists (rf idx_out out_val).2
                rw [←htmp1, ←htmp2] at Hstep
                -- We had a correctness before moving the flit around,
                -- what was it?
                cases Hstep
                -- The correctness was telling us to move to another router
                · subst tmp1 tmp2
                  rename_i mid_flit dir' hdir' H1' H2'
                  dsimp at H1' H2'
                  rw [H1] at H1'
                  obtain ⟨rfl, rfl⟩ := H1'
                  have := conns_getConnDir_out Hconn1
                  rwa [this] at H2'
                · rename_i dir' Hdir' flit' Hflit'
                  subst dir_out
                  simp [drcomponents, drunfold_defs] at Hdir Hflit'
                  rw [Hflit'] at Hdir
                  contradiction
          -- routing_function_reconstruct
          · apply List.Perm.trans _ Hrf2
            dsimp
            rw [vec_set_reconstruct (f := λ i => i ++ [val]) H8 H7]
            rw [vec_set_reconstruct (f := λ i => i.eraseIdx H3) H6 H4]
            rw [vec_set_map]
            by_cases Heq: idx_out = idx_inp
            <;> simp [Heq]
            · subst idx_out
              rw [vec_set_map]
              rw [Vector.set_set]
              rw [vec_set_toList]
              -- We will have to show that out_val and val have the same rf
              -- (almost)
              sorry
            · rw [Vector.getElem_set_ne idx_out.2 idx_inp.2 (by
                simp; intro h;
                apply Heq; cases idx_out; cases idx_inp; simp only at h; simp only [h])
              ]
              rw [vec_set_toList]
              sorry

  theorem correct : (mod (noc' noc)) ⊑ (spec (noc' noc)) := by
    exists inferInstance, φ (noc' noc); solve_by_elim [refines_φ, refines_initial]

end Graphiti.Projects.Noc
