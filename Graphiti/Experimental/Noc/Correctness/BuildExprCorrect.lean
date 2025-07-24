/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
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

open Batteries (AssocList)

set_option Elab.async false

namespace Graphiti.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  def Noc.env_rmod_ok (n : Noc Data netsz) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, (rmod rid).2 ⊑ (n.spec_router rid)

  def Noc.env_rmod_ok' (n : Noc Data netsz) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, (n.spec_router rid) ⊑ (rmod rid).2

  @[drenv]
  def Noc.env_rmod_in (n : Noc Data netsz) (ε : Env String) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, ε (router_type_name n rid) = .some (rmod rid)

  @[drenv]
  def Noc.env_empty (n : Noc Data netsz) (ε : Env String) : Prop :=
    ε "empty" = .some ⟨Unit, StringModule.empty⟩

  class EnvCorrect (n : Noc Data netsz) (ε : Env String) where
    rmod        : n.RouterID → TModule String
    rmod_ok     : n.env_rmod_ok rmod
    rmod_ok'    : n.env_rmod_ok' rmod
    rmod_in_ε   : n.env_rmod_in ε rmod
    empty_in_ε  : n.env_empty ε

  variable (n : Noc Data netsz) (ε : Env String) [EC : EnvCorrect n ε]

  abbrev mod := NatModule.stringify n.build_module

  @[drunfold_defs]
  def_module expT : Type := [T| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type]
    dsimp [ExprLow.build_module]
    rw [ExprLow.build_module_connect_foldr]
    dsimp [ExprLow.build_module]
    rw [ExprLow.build_module_product_foldr]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]
    conv =>
      pattern List.foldr _ _
      arg 2
      arg 1
      intro i acc
      rw [←router_name, ←router_type_name]
      rw [EC.rmod_in_ε i]
      dsimp
    rw [Module.dep_foldr_1 (f := λ i acc => acc)]
    rw [Module.dep_foldr_1 (f := λ i acc => (EC.rmod i).1 × acc)]
    simp only [drenv, drcompute, List.foldr_fixed]
    rw [←DPList', ←DPList]

  theorem nil_renaming {α β} [DecidableEq α] (l : AssocList α β) :
  (AssocList.mapKey (@AssocList.nil α α).bijectivePortRenaming l) = l := by
    induction l with
    | nil => rfl
    | cons x v tl HR => simpa [HR, AssocList.bijectivePortRenaming, drcompute]

  -- theorem magic {T₁ T₁' T₂} {h : T₁ = T₁'} {t : T₁} {f : T₁' → T₂}
  --   : f (h.mp t) = (f t) := by sorry

  -- f : (α → β) → α → β
  -- theorem magic {α α' β} {h : α = α'} {f : (α → β) → α → α}
  -- (h : α = α') : f p (h.mp v) = h.mpr (f (λ i => h.mp i) v)

  theorem tmp_magic {α β T₁} [DecidableEq α] (l : AssocList α β) (l : T₁)
    (p : α → β → Bool) (h : T₁ = AssocList α β) :
    AssocList.eraseAllP p (h.mp l) = sorry := by sorry

  theorem eraseAll_depfoldr {α β δ} [DecidableEq α] (l : List δ) (p : α → Bool) (f : δ → Type → Type) (g : δ → AssocList α β) h acc :
      AssocList.eraseAllP (λ k _ => p k)
        (
          List.foldr
          (λ i acc => (⟨f i acc.1, (g i) ++ (acc.2.mapVal h)⟩: Σ T, AssocList α β))
          acc
          l
        ).snd
      =
        (List.foldr
          (λ i acc => ⟨f i acc.1, AssocList.eraseAllP (λ k _ => p k) (g i) ++ (acc.2.mapVal h)⟩)
          (⟨acc.1, AssocList.eraseAllP (λ k _ => p k) acc.2⟩: Σ T, AssocList α β)
          l).snd
      := by
    induction l generalizing acc with
    | nil => rfl
    | cons hd tl HR =>
      dsimp; rw [←HR, AssocList.eraseAllP_concat, AssocList.eraseAllP_map_comm]

  set_option pp.proofs true in
  @[drunfold_defs]
  def_module expM : Module String (expT n ε) := [e| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp [ExprLow.build_module_expr, ExprLow.build_module_type]
    dsimp [ExprLow.build_module]
    rw [ExprLow.build_module_connect_foldr]
    dsimp [ExprLow.build_module]
    rw [ExprLow.build_module_product_foldr]
    dsimp [ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]; dsimp
    dsimp [drcomponents]
    rw [rw_opaque (by
      conv =>
        pattern List.foldr _ _
        arg 2
        arg 1
        intro i acc
        rw [←router_name, ←router_type_name]
        rw [EC.rmod_in_ε i]
        dsimp [Module.product]
        dsimp [
          Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts,
          Module.mapInputPorts, reduceAssocListfind?
        ]
        -- rw [nil_renaming]
        -- rw [nil_renaming]
    )]
    dsimp [
      Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts,
      Module.mapInputPorts, reduceAssocListfind?
    ]
    have := Module.foldr_acc_plist_2
      (acc :=
        ⟨Unit, { inputs := .nil, outputs := .nil, init_state := λ x => True }⟩
      )
      (l := fin_range netsz)
      (f := λ i acc1 => (EC.rmod i).1 × acc1)
      (g_inputs := λ i acc =>
        AssocList.mapVal (λ x => Module.liftL) ((EC.rmod i).2.inputs)
          ++ AssocList.mapVal (λ x => Module.liftR) acc.2
      )
      (g_outputs := λ i acc =>
        (AssocList.mapVal (λ x => Module.liftL) ((EC.rmod i).2.outputs))
          ++ (AssocList.mapVal (λ x => Module.liftR) acc.2)
      )
      (g_internals := λ i acc =>
            List.map Module.liftL' (EC.rmod i).2.internals
         ++ List.map Module.liftR' acc.2
      )
      (g_init_state := λ i acc =>
        λ x => (EC.rmod i).snd.init_state x.1 ∧ acc.2 x.2
      )
    rw [←Module.dep_foldr, this]
    clear this
    rw [Module.foldr_connect']
    dsimp
    simp only [drcompute]
    -- Casts in i/o forbid us from anything, we must make them at top-level
    -- rw [eraseAll_depfoldr]

    -- For the init_state:
    -- We want to remove the dependent type part.
    -- This is specific to the combination of a dep_foldl to produce a PListL,
    -- but should work

    -- For inputs, outputs:
    -- We want to lower the eraseAll.
    -- It is a bit annoying to do, since erasing after a fold is rarely the same
    -- thing as erasing inside of it.
    -- Even here, there is a subtelty that we cannot make it disapear easily
    -- because otherwise we might not get the correct amount of lift…
    --
    -- What would be really nice would be to be able to transform the
    -- Module.foldl_io into a map-flatten or something...

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

end Graphiti.Noc
