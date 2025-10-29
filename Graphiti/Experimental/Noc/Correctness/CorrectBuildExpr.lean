/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Graphiti.Core.ModuleReduction
import Graphiti.Core.ExprLow
import Graphiti.Core.ExprLowLemmas
import Graphiti.Core.Component
import Graphiti.Projects.Noc.Utils
import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.Spec
import Graphiti.Projects.Noc.Tactic
import Graphiti.Projects.Noc.BuildExpr
import Graphiti.Experimental.Noc.Correctness.ExprHighSem

open Batteries (AssocList)

set_option Elab.async false

namespace Graphiti.Projects.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  def Noc.env_rmod_ok (n : Noc Data netsz) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, (rmod rid).2 ⊑ (n.spec_router rid)

  def Noc.env_rmod_ok' (n : Noc Data netsz) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, (n.spec_router rid) ⊑ (rmod rid).2

  @[drenv]
  def Noc.env_rmod_in (n : Noc Data netsz) (ε : Env String String) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, ε (router_type_name n rid) = .some (rmod rid)

  @[drenv]
  def Noc.env_empty (n : Noc Data netsz) (ε : Env String String) : Prop :=
    ε "empty" = .some ⟨Unit, StringModule.empty⟩

  class EnvCorrect (n : Noc Data netsz) (ε : Env String String) where
    rmod        : n.RouterID → TModule String
    rmod_ok     : n.env_rmod_ok rmod
    rmod_ok'    : n.env_rmod_ok' rmod
    rmod_in_ε   : n.env_rmod_in ε rmod
    empty_in_ε  : n.env_empty ε

  variable (n : Noc Data netsz) (ε : Env String String) [EC : EnvCorrect n ε]

  abbrev mod := NatModule.stringify n.build_module

  -- Utils lemmas (TODO: Move elsewhere) ---------------------------------------

  theorem valsList_foldr {α β γ} (f : γ → α) (g : γ → β) (acc : AssocList α β) (l : List γ) :
    AssocList.valsList (List.foldr (λ i acc => AssocList.cons (f i) (g i) acc) acc l) =
    List.foldr (λ i acc => .cons (g i) acc) (AssocList.valsList acc) l := by sorry

  theorem mapM_map {m} [Monad m] {α β γ} (f : α → m β) (g : β → m γ) l :
    l.mapM (λ i => bind (f i) g) = (List.map f l).mapM (λ i => bind i g) := sorry

  theorem mapM_option_id {α} (l : List (Option α)) :
    -- TODO. Require that all element of l is some
    l.mapM (λ (i : Option α) => i) = .some (l.map (λ i => Option.get i (by sorry))) := by
      induction l with
      | nil => rfl
      | cons hd tl HR => sorry

  ------------------------------------------------------------------------------

  set_option pp.proofs true in
  @[drunfold_defs]
  def_module expT : Type 1 := n.build_expr.build_module_high_type ε reduction_by
    dsimp [drunfold_defs, drcomponents]
    rw [valsList_foldr]
    simp only [List.foldr_cons_eq_append, List.map_append, List.map_map, List.append_nil]
    simp only [AssocList.valsList, AssocList.toList, List.map_nil, List.append_nil]
    conv =>
      pattern List.map _ _
      arg 1
      intro x
      dsimp
      rw [←router_type_name]
      rw [EC.rmod_in_ε x]
      dsimp
    simp only [Option.bind_fun_some]
    conv =>
      pattern List.mapM _ _
      rw [mapM_option_id]
    simp only [List.map_map, List.getElem_map, Function.comp_apply, Option.get_some, Option.getD_some]
    conv =>
      pattern List.map _ _
      arg 1
      intro i
      simp only [Function.comp_apply, Option.get_some]
    skip

  @[drunfold_defs]
  def_module expM : Module String (expT n ε) := n.build_expr.build_module_high_expr ε reduction_by
    dsimp [drunfold_defs, drcomponents]
    -- rw [valsList_foldr]
    -- simp only [AssocList.valsList, AssocList.toList, List.map_nil, List.append_nil]
    skip

  instance : MatchInterface (expM n ε) (mod n) := by
    apply MatchInterface_simpler
    <;> intro _
    <;> dsimp [drunfold_defs, drcomponents]
    <;> sorry

  -- TODO: Proper name
  def tmp2 {rid : Fin (fin_range netsz).length} :
    (EC.rmod ((fin_range netsz).get rid)).1 = (EC.rmod (fin_conv rid)).1 := by
      rw [fin_range_get]

  def I_cast_get (I : expT n ε) (rid : n.RouterID) : (EC.rmod rid).1 :=
    ((tmp2 n ε).mp (I.get (fin_conv' rid)))

  set_option pp.proofs true in
  #check I_cast_get

  def φ (I : expT n ε) (S : n.State) : Prop :=
    ∀ (rid : n.RouterID), (Module.refines_refines' (EC.rmod_ok rid)).2.choose
      (I_cast_get n ε I rid)
      (S.get rid)

  set_option pp.proofs true in
  def i_init_rid (i : expT n ε) (Hinit : (expM n ε).init_state i) :
    ∀ (rid : n.RouterID), (EC.rmod rid).2.init_state (I_cast_get n ε i rid) := by
      dsimp [drunfold_defs] at Hinit i
      conv at Hinit =>
        arg 2
        -- This rewrite does not work, not sure why… Probably universe
        -- constraints?
        -- rw [←Module.dep_foldr]
        -- But this does not work either…
        -- rw [←dep_foldr']
      revert n
      induction netsz with
      | zero => intro _ _ _ _ ⟨_, _⟩; contradiction
      | succ netsz' HR =>
        dsimp [drcomponents, drunfold_defs] at *
        intro n EC i Hinit ⟨ridv, Hrid⟩
        induction ridv with
        | zero =>
          dsimp [fin_range] at ⊢ Hinit i
          obtain ⟨i, hi⟩ := i
          dsimp [I_cast_get, DPList.get'] at *
          unfold expM._proof_5 at Hinit
          unfold Module.dep_foldr_β at Hinit
          -- TODO: This is true and should but provable with hinit
          -- but there is annoying casts to handle everywhere
          sorry
        | succ ridv' HR' =>
          rw [add_lt_add_iff_right] at Hrid
          dsimp [fin_range] at ⊢ Hinit i
          obtain ⟨i, hi⟩ := i
          -- FIXME: Process described below is not possible, init_state might
          -- depend on the total number of router in the system, this is very
          -- annoying
          -- But thinking about it we should be able to create a new Noc which
          -- depends just as much as the original with casts in the correct
          -- places
          -- TODO: Trick here is probably to define a new noc but with one less
          -- router so that we can use HR with this new noc.
          -- This new noc will probably be also useful down the line for proving
          -- other rules by induction, so this seems kind of like a custom
          -- induction hypothesis
          sorry

  set_option pp.proofs true in
  theorem refines_initial : Module.refines_initial (expM n ε) (mod n) (φ n ε) := by
    intro i H
    apply Exists.intro _
    apply And.intro
    · -- NOTE: This work only because Noc's router initial state is just one
      -- state and not a property on state, which is quite weak.
      dsimp [drcomponents]
    · intro rid
      obtain Hspec := Exists.choose_spec ((Module.refines_refines' (EC.rmod_ok rid)).2)
      obtain ⟨Hspec1, ⟨Hspec2, Hspec3⟩⟩ := Hspec
      dsimp [Module.refines_initial] at Hspec3
      specialize Hspec3 (I_cast_get n ε i rid)
      apply i_init_rid at H
      specialize H rid
      unfold I_cast_get at Hspec3
      specialize Hspec3 H
      obtain ⟨s, ⟨Hs1, Hs2⟩⟩ := Hspec3
      dsimp [drcomponents] at Hs1
      subst s
      dsimp [drunfold_defs, drcomponents] at Hs2
      rw [Vector.get_replicate]
      exact Hs2

  theorem refines_φ : (expM n ε) ⊑_{φ n ε} (mod n) := by
    intro i s hφ
    constructor
    · intro ident mid_i v hv
      unfold φ at hφ
      dsimp [drcomponents, drunfold_defs] at v hv
      sorry
    · intro ident mid_i v hv
      dsimp [drcomponents, drunfold_defs] at v hv
      sorry
    · sorry

  theorem correct : (expM n ε) ⊑ (mod n) := by sorry

end Graphiti.Projects.Noc
