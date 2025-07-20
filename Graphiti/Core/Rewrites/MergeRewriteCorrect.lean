/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import Graphiti.Core.Simp
import Graphiti.Core.Module
import Graphiti.Core.ExprLow
import Graphiti.Core.Component
import Graphiti.Core.KernelRefl
import Graphiti.Core.Reduce
import Graphiti.Core.List
import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Tactic
import Graphiti.Core.Rewrites.MergeRewrite
import Mathlib.Tactic

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace Graphiti.MergeRewrite

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Batteries.AssocList.find? Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq Module.bijectivePortRenaming ExprLow.filterId List.Nodup List.inter AssocList.keysList List.filter List.elem AssocList.eraseAllP

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map List.empty_eq decide_true ne_eq List.pairwise_cons List.mem_singleton forall_eq
  InternalPort.mk.injEq String.reduceEq and_false not_false_eq_true List.not_mem_nil IsEmpty.forall_iff
  implies_true List.Pairwise.nil and_self Bool.and_self reduceCtorEq reduceIte decide_false and_true
  List.remove List.get_eq_getElem eq_mp_eq_cast cast_eq Prod.exists forall_const not_true_eq_false imp_self
  List.append_nil

abbrev Ident := Nat

def ε (T : Type _) : IdentMap String (TModule String) :=
  [ ("Merge", ⟨ _, StringModule.merge T 2 ⟩)
  , ("Merge3", ⟨ _, StringModule.merge T 3 ⟩)
  ].toAssocList

@[drunfold] def threemerge (T : Type _) : StringModule (List T) := by
  precomputeTac [e| rewrite.output_expr, ε T ] by
    dsimp only [drunfold,seval,drcompute]
    simp only [seval,drdecide]
    -- conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    -- conv in _ :: Module.connect'' _ _ :: _ => arg 2; rw [Module.connect''_dep_rw]; rfl
    -- unfold Module.connect''
    -- dsimp

theorem threemerge_eq_merge3 T : threemerge T = StringModule.merge T 3 := by rfl

def merge_sem_type (T : Type _) : Type := by
  precomputeTac [T| rewrite.input_expr, ε T ] by
    dsimp only [drunfold,seval,drcompute]

def merge_sem (T : Type _) : StringModule ([T| rewrite.input_expr, ε T ]) := by
  precomputeTac [e| rewrite.input_expr, ε T ] by
    dsimp only [drunfold,seval,drcompute]
    simp only [seval,drdecide, ↓reduceIte]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect''
    dsimp

attribute [dmod] Batteries.AssocList.find? BEq.beq

instance {T} : MatchInterface (merge_sem T) (threemerge T) where
  input_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (merge_sem T).inputs)
    · have h' := AssocList.keysInMap h
      fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      rfl
  output_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (merge_sem T).outputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      rfl
  inputs_present := by sorry
  outputs_present := by sorry

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x (h ▸ v) y := by
  constructor <;> (intros; subst h; assumption)

def φ {T} (x : List T × List T) (y : List T) := (x.1 ++ x.2).Perm y

theorem φ_indistinguishable {T} :
  ∀ x y, φ x y → Module.indistinguishable (merge_sem T) (threemerge T) x y := by stop
  unfold φ; intro x y H
  constructor <;> intro ident new_i v Hsem
  · have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys <;> (constructor; rfl)
  · have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys
    let ⟨ ⟨ i, Ha, Hc ⟩, Hb ⟩ := Hsem; clear Hsem
    let (x1, x2) := x; clear x
    let (new_i1, new_i2) := new_i; clear new_i
    subst_vars; simp [seval,drunfold]
    generalize h : x2[i] = y'
    have Ht : ∃ (i : Fin x2.length), x2.get i = y' := by exists i
    rw [← List.mem_iff_get] at Ht
    have He := List.Perm.symm H
    have Hiff := List.Perm.mem_iff (a := y') He
    have Ht' : y' ∈ y := by rw [Hiff]; simp; cases Ht <;> tauto
    rw [List.mem_iff_get] at Ht'
    let ⟨ i', Hi' ⟩ := Ht'; clear Ht'
    constructor; exists i'; and_intros; rfl
    simp [←Hi']

-- theorem correct_threeway_merge'' {T: Type _} [DecidableEq T]:
--     threemerge T ⊑_{φ} (merge_sem T) := by
--   intro ⟨ x1, x2 ⟩ y HPerm
--   apply Module.comp_refines.mk
--   . intro ident ⟨x'1, x'2⟩ v Hcontains Himod
--     have := keysInMap Hcontains
--     fin_cases this
--     · dsimp at *
--       rw [sigma_rw] at Himod
--       dsimp at Himod
--       let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
--       have Hφ : φ (v :: x1, x'2) (v :: y) := by
--         simp [*, φ] at HPerm ⊢; assumption
--       constructor; constructor; and_intros
--       all_goals first | rfl | apply existSR.done | assumption
--     · dsimp at *
--       rw [sigma_rw] at Himod
--       dsimp at Himod
--       let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
--       have Hφ : φ (v :: x1, x'2) (v :: y) := by
--         simp [*, φ] at HPerm ⊢; assumption
--       constructor; constructor; and_intros
--       all_goals first | rfl | apply existSR.done | assumption
--     · dsimp at *
--       rw [sigma_rw] at Himod
--       dsimp at Himod
--       let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
--       have Hφ : φ (x'1, v :: x2) (v :: y) :=
--         List.Perm.symm (List.perm_cons_append_cons v (List.Perm.symm HPerm))
--       constructor; constructor; and_intros
--       all_goals first | rfl | apply existSR.done | assumption
--   · intro ident mid_i v Hcontains Hi
--     have := keysInMap Hcontains
--     fin_cases this
--     rcases Hi with ⟨ ⟨ i, Hil ⟩, Hir ⟩
--     rcases Hil with ⟨ Hill, Hilr ⟩
--     dsimp at *
--     subst v; subst x1
--     generalize Hx2get : x2.get i = v'
--     have Hx2in : v' ∈ x2 := by rw [List.mem_iff_get]; tauto
--     have He := HPerm
--     have Hiff := List.Perm.mem_iff (a := v') HPerm
--     have Hyin : v' ∈ y := by rw [← Hiff]; simp; tauto
--     rw [List.mem_iff_get] at Hyin
--     rcases Hyin with ⟨ i', Hyget ⟩
--     have HerasePerm : φ mid_i (y.eraseIdx i'.1) := by
--       simp [φ, Hill]
--       trans; apply List.perm_append_comm
--       rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
--       trans ((x2 ++ mid_i.1).erase x2[i])
--       have H2 : x2[i] = (x2 ++ mid_i.1)[i] := by
--         symm; apply List.getElem_append_left
--       rw [H2]; symm; apply List.erase_get
--       symm; trans; symm; apply List.erase_get
--       rw [Hyget]; simp at Hx2get; simp; rw [Hx2get]
--       apply List.perm_erase; symm
--       symm; trans; symm; assumption
--       apply List.perm_append_comm
--     constructor; constructor; and_intros
--     · exists i'; and_intros; rfl; simp_all
--     · apply existSR.done
--     · assumption
--   · intro ident mid_i Hcontains Hv
--     fin_cases Hcontains; have Hv' := Hv rfl; clear Hv
--     reduce at *
--     rcases Hv' with ⟨ ⟨ la1, la2 ⟩, lb, Hv' ⟩; reduce at *;
--     rcases Hv' with  ⟨ ⟨ ⟨ i, H2, H3 ⟩, Hx3 ⟩, Hx2, H4 ⟩
--     subst lb; subst la1; subst la2
--     have HerasePerm : φ mid_i y := by
--       simp [φ, Hx2,← H4]
--       rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
--       trans ((x1 ++ x1[i] :: x2).erase x1[i])
--       rw [List.perm_comm]
--       have : x1[↑i] = x1.get i := by simp
--       simp [*] at *
--       have H : x1[↑i] = (x1 ++ x1[↑i] :: x2)[↑i] := by
--         symm; apply List.getElem_append_left
--       dsimp at *; conv => arg 1; arg 2; rw [H]
--       apply List.erase_get
--       trans ((x1[i] :: (x1 ++ x2)).erase x1[i])
--       apply List.perm_erase; simp
--       rw [List.erase_cons_head]; assumption
--     constructor; and_intros
--     all_goals first | rfl | apply existSR.done | assumption

-- theorem correct_threeway_merge' {T: Type _} [DecidableEq T] :
--     (merge_sem' T).snd ⊑ threemerge' T :=
--   Module.refines_φ_refines φ_indistinguishable correct_threeway_merge''

-- instance {T} : MatchInterface (merge_sem T).snd (threemerge T) :=
--   inferInstanceAs (MatchInterface (merge_sem' T).snd (threemerge' T))

-- theorem correct_threeway_merge {T: Type _} [DecidableEq T] :
--     (merge_sem T).snd ⊑ threemerge T := by
--   apply correct_threeway_merge'

-- /--
-- info: 'Graphiti.correct_threeway_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms correct_threeway_merge

end Graphiti.MergeRewrite
