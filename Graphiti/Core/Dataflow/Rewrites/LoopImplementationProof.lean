/-
Copyright (c) 2025, 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martina Camaioni, Yann Herklotz
-/

module

public import Graphiti.Core.Graph.ExprLowLemmas
public import Graphiti.Core.Dataflow.Rewrites.LoopRewriteCorrect
public import Mathlib

@[expose] public section

namespace Graphiti.LoopRewrite

open Batteries (AssocList)

--open matchGoal

open Lean hiding AssocList
open Meta Elab

open StringModule

section Proof

variable [e : Environment Env.well_formed lhsLower]

seal T
seal f

section Iterate

variable {Data : Type}
variable (f : Data → Data × Bool)

attribute [drunfold] AssocList.eraseAll

def apply (n : Nat) (i : Data) : Data × Bool :=
match n with
| 0 => (i, true)
| n' + 1 => f (apply n' i).fst

@[aesop safe unfold]
def iterate (i: Data) (n : Nat) (i': Data) : Prop :=
  (∀ m, m < n -> (apply f m i).snd = true) ∧ apply f n i = (i', false) ∧ n > 0

inductive iterate_full (i: Data) : Option Nat → Option Data → Prop where
| terminate {n i'} : iterate f i n i' → iterate_full i (some n) (some i')
| diverge : (∀ m, (apply f m i).snd = true) → iterate_full i none none

omit e in
theorem exists_minimal_m {i} {m} :
  (apply f m i).2 = false →
  ∃ m', (apply f m' i).2 = false ∧ (∀ n, n < m' → (apply f n i).snd = true) := by
  induction m using Nat.strong_induction_on; grind

omit e in
theorem iterate_deterministic {i n i' n2 i'2} :
  iterate f i n i' →
  iterate f i n2 i'2 →
  n = n2 ∧ i' = i'2 := by grind [iterate]

omit e in
theorem iterate_full_deterministic {i n i' n2 i'2} :
  iterate_full f i n i' →
  iterate_full f i n2 i'2 →
  n = n2 ∧ i' = i'2 := by
  intro ha hb; cases ha <;> cases hb <;> grind [iterate_deterministic, iterate]

omit e in
theorem iterate_full_complete {i} :
  ∃ n d, iterate_full f i n d := by
  cases Classical.em (∀ m, (apply f m i).snd = true)
  · exists none, none; constructor; assumption
  · simp at *; rename_i h; obtain ⟨x, h⟩ := h
    have := exists_minimal_m f h
    obtain ⟨m', ha⟩ := this
    exists m', (apply f m' i).1
    constructor; constructor <;> grind [apply]

inductive lt_current : Nat → Option Nat → Prop :=
| some {n final} : n < final → lt_current n (some final)
| none {n} : lt_current n none

omit e in
theorem apply_plus_one (i: Data) (n : Nat) : (f (apply f n i).1).1 = (apply f (1 + n) i).1 := by
  rw [show 1 + n = n + 1 by omega]; rfl

omit e in
theorem apply_plus_one_condiction (i: Data) (n : Nat) : (f (apply f n i).1).2 = (apply f (n + 1) i).2 := rfl

omit e in
theorem apply_true (i : Data) (i' : Option Data) (n : Option Nat) (k : Nat) :
  lt_current k n ->
  (apply f (k + 1) i).2 = true ->
  iterate_full f i n i' ->
  lt_current (k + 1) n := by
  intro hl1 happly hiter
  cases hiter
  · unfold iterate at *; cases hl1; constructor; grind
  · constructor

omit e in
theorem apply_false (i : Data) (i' : Option Data) (n : Option Nat) (k : Nat) :
  lt_current k n →
  (apply f (k + 1) i).2 = false →
  iterate_full f i n i' →
  some (k + 1) = n := by
  intro hl1 happly hiter
  cases hiter
  · unfold iterate at *; cases hl1; grind
  · grind

end Iterate

inductive state_relation : rhsGhostType -> Prop where
| intros : ∀ (s :  rhsGhostType) x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB x_split_branchT x_split_branchF x_moduleT x_moduleF,
  ⟨ x_module, ⟨x_branchD, x_branchB⟩, x_merge, ⟨x_tagT, x_tagM, x_tagD ⟩, ⟨x_splitD, x_splitB⟩⟩ = s ->
  ( ∀ elem, elem ∈ x_tagD ->  elem.1 = elem.2.2 ∧ elem.2.1 = 0) ->
  (∀ elem n i', elem ∈ x_merge -> iterate_full f elem.2.2 n i' -> elem.2.1 ≥ 0 ∧ lt_current elem.2.1 n ∧ elem.1.2 = (apply f elem.2.1 elem.2.2).1) ->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (List.zip (x_branchD ++ x_splitD ) ( x_branchB ++ x_splitB))) = x_split_branchT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (List.zip (x_branchD ++ x_splitD ) (x_branchB ++ x_splitB ))) = x_split_branchF ->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (x_module)) = x_moduleT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (x_module)) = x_moduleF ->
  (∀ elem , elem ∈ x_split_branchT ++ x_moduleT -> ∃ n i', iterate_full f elem.2.2 n i' ∧
    elem.2.1 > 0 ∧ lt_current elem.2.1 n ∧ elem.1.2 = (apply f elem.2.1 elem.2.2).1) ->
  (∀ elem, elem ∈ x_split_branchF ++ x_moduleF ->  iterate_full f elem.2.2 elem.2.1 elem.1.2) ->
  ((((x_merge ++ (x_module.map Prod.fst) ++ x_splitD ++ x_branchD ++ x_tagM.toList.map (λ x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))).map Prod.fst).map Prod.fst).Nodup) ->
  (∀ elem, elem ∈ ((x_merge ++ (x_module.map Prod.fst) ++ x_splitD ++ x_branchD ++ x_tagM.toList.map (λ x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))).map (fun ((x, _), _, y) => (x, y)))-> elem ∈ x_tagT) ->
  ((x_tagT.map Prod.fst).Nodup) ->
  (x_branchD ++ x_splitD).length = (x_branchB ++ x_splitB).length ->
  ( ∀ tag d n i, x_tagM.find? tag = some (d, n, i) -> (tag, i ) ∈ x_tagT ∧ iterate_full f i n d) ->
  ( ∀ d, d ∈ x_tagD -> d.2 = (0, d.1)) ->
  ( ∀ tag i, (tag, i) ∈ x_tagT -> ∃ d n, iterate_full f i n d) ->
  ( ∀ e, e ∈ x_tagD -> ∃ d n, iterate_full f e.1 n d) ->
  -- ( ∀ tag i, (i) ∈ x_tagD -> ∃ d n, iterate f i n d) ->
  state_relation s

def default_lhs : lhsType := by unfold lhsType; apply default
def default_rhs : rhsGhostType := by unfold rhsGhostType; apply default

theorem default_rhs_eq {p} : rhsGhostEvaled.init_state p → p = default_rhs := by
  intro hghost
  dsimp [rhsGhostEvaled, tagger_untagger_val_ghost, NatModule.tagger_untagger_val_ghost, NatModule.stringify, Module.mapIdent] at hghost
  dsimp [default_rhs, default, Batteries.instInhabitedAssocList.default];
  obtain ⟨x_module, ⟨x_branchD, x_branchB⟩, x_merge, ⟨x_tagT, x_tagM, x_tagD ⟩, ⟨x_splitD, x_splitB⟩⟩ := p
  grind

theorem default_lhs_eq : lhsEvaled.init_state default_lhs := by
  dsimp [lhsEvaled, tagger_untagger_val_ghost, NatModule.tagger_untagger_val_ghost, NatModule.stringify, Module.mapIdent]
  dsimp [default_lhs, default, Batteries.instInhabitedAssocList.default]
  grind

theorem state_relation_empty :
  state_relation default_rhs := by
  constructor <;> try trivial
  · intro elem hin; cases hin
  · intro elem n i' hin; cases hin
  · intro _ hin; cases hin
  · intro _ hin; cases hin
  · constructor
  · intro _ hin; cases hin
  · constructor
  · intro _ _ _ _ hfind
    rw [show default = Batteries.AssocList.nil by rfl] at hfind
    simp [-AssocList.find?_eq] at hfind
  · intro _ hin; cases hin
  · intro _ _ hin; cases hin
  · intro _ hin; cases hin

/-
# Proof state_relation_prserve in rhsGhost
-/

omit e in
theorem alpa {α : Type} {a : α} {l : List α} : a :: l = [a] ++ l := by simp only [List.singleton_append]

omit e in
theorem perm_comm {α : Type} {l1 l2 l3 : List α} : (l1).Perm (l2 ++ l3) -> (l1).Perm (l3 ++ l2) := by
  intros
  apply List.Perm.trans; assumption
  apply List.perm_append_comm

attribute [aesop unsafe 50% forward] List.Nodup.cons List.perm_append_singleton
attribute [aesop norm] List.perm_comm

omit e in
theorem erase_map {α β γ : Type} {l : List ((α × β) × γ)} {k : Nat} :
  List.map (Prod.fst ∘ Prod.fst) (List.eraseIdx l k) = (List.map (Prod.fst ∘ Prod.fst) l).eraseIdx k := by
  simp [List.eraseIdx_map]

omit e in
theorem erase_perm {α β γ : Type} {l : List ((α × β) × γ)} (k : Fin (List.length l)):
  ((List.map (Prod.fst ∘ Prod.fst) l).eraseIdx k ++ [(l[k].1.1)]).Perm (List.map (Prod.fst ∘ Prod.fst) l) := by
  rw [←erase_map]
  rw [show [l[k].1.1] = List.map (Prod.fst ∘ Prod.fst) [l[k]] by rfl]
  rw [show List.map (Prod.fst ∘ Prod.fst) (l.eraseIdx ↑k) ++ List.map (Prod.fst ∘ Prod.fst) [l[k]] = List.map (Prod.fst ∘ Prod.fst) (l.eraseIdx ↑k ++ [l[k]]) by simp]
  apply List.Perm.map
  apply List.Perm.trans
  apply List.perm_append_singleton
  apply List.getElem_cons_eraseIdx_perm

omit e in
theorem map_fst {α β γ η  : Type} {i : α} {l : List ((α × β) × γ × η)}:  i ∈ (l.map Prod.fst).map Prod.fst -> ∃ i', (i, i') ∈ l.map (fun x => (x.1.1, x.2.2)) := by aesop

omit e in
theorem getIO_cons_neq {α} {a b x} {xs}:
  a ≠ b ->
  PortMap.getIO (.cons a x xs) b = @PortMap.getIO String α _ xs b := by
  unfold PortMap.getIO; intro heq
  rw [Batteries.AssocList.find?_cons_neq']; assumption

omit e in
theorem getIO_nil {α} {b}:
  @PortMap.getIO String α _ .nil b = ⟨ Unit, λ _ _ _ => False ⟩ := by aesop

omit e in
theorem getIO_cons_eq {α} {a x} {xs}:
  @PortMap.getIO String α _ (.cons a x xs) a = x := by
  unfold PortMap.getIO; rw [Batteries.AssocList.find?_cons_eq]; rfl

omit e in
theorem find?_cons_eq {α β} [DecidableEq α] {a x} {xs : Batteries.AssocList α β}:
  Batteries.AssocList.find? a (xs.cons a x) = x := by simp

omit e in
theorem find?_cons_neq {α β} [DecidableEq α] {a x} y {xs : Batteries.AssocList α β}:
  ¬(a = y) -> Batteries.AssocList.find? a (xs.cons y x) = Batteries.AssocList.find? a xs := by simp; grind

theorem state_relation_preserve_input:
  ∀ (s s' : rhsGhostType) rule,
    rule ∈ ( rhsGhostEvaled).internals ->
    rule s s' ->
    state_relation s ->
    (List.map Prod.snd s.2.2.2.1.1 ++ List.map Prod.fst s.2.2.2.1.2.2) = (List.map Prod.snd s'.2.2.2.1.1 ++ List.map Prod.fst s'.2.2.2.1.2.2) := by
  intro s s' rule hrulein hrule hstate
  dsimp [rhsGhostEvaled, Module.liftL, Module.liftR] at hrulein
  fin_cases hrulein <;> try grind

omit e in
theorem in_eraseAll_noDup {α β γ δ} {l : List ((α × β) × γ × δ)} (Ta : α) [DecidableEq α](a : AssocList α (β × γ × δ)):
  (List.map Prod.fst ( List.map Prod.fst (l ++ (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) a.toList)))).Nodup ->
  (List.map Prod.fst ( List.map Prod.fst (l ++ List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) (AssocList.eraseAll Ta a).toList))).Nodup := by
  unfold AssocList.eraseAll
  rw [Batteries.AssocList.eraseAllP_TR_eraseAll]
  apply Batteries.AssocList.in_eraseAll_noDup

omit e in
theorem notinfirst {A B} {x : List (A × B)} {a} :
  a ∉ List.map Prod.fst x → ∀ y, (a, y) ∉ x := by
  grind

omit e in
theorem elem_in_third {α} {e : α} {a b c d : List _} :
  e ∈ a ++ (b ++ (c ++ d)) → e ∉ c → e ∈ a ++ (b ++ d) := by grind

omit e in
theorem elem_in_erase_first {α} {e : α} {a b : List _} {n} :
  e ∈ (List.eraseIdx a n) ++ b → e ∈ a ++ b := by grind [List.mem_of_mem_eraseIdx]

set_option maxHeartbeats 0 in
theorem state_relation_preserve:
  ∀ (s s' : rhsGhostType) rule,
    rule ∈ (rhsGhostEvaled).internals ->
    rule s s' ->
    state_relation s ->
    state_relation s' := by
  intro s s' rule h1 h2 h3
  let ⟨ x_module, ⟨x_branchD, x_branchB⟩, x_merge, ⟨x_tagT, x_tagM, x_tagD ⟩, ⟨x_splitD, x_splitB⟩⟩ := s
  let ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := s'
  fin_cases h1
  . dsimp only [Module.liftR, Module.liftL, cast_eq] at h2
    replace h2 := h2.1 rfl
    simp only [List.concat_eq_append, Module.liftR, Module.liftL] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnewnew
    repeat rw [Prod.mk.injEq] at h
    repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . grind [←List.singleton_append]
    . clear h9 h10 h12 H13 H14 H15
      intro elem n i' h1 h2
      specializeAll elem
      simp only [List.mem_cons, forall_eq_or_imp, zero_le] at *
      cases h1
      . and_intros
        · grind
        · cases h2
          · constructor
            unfold iterate at *
            grind
          · constructor
        · subst_vars; simp only [true_and, h3, h2]; rfl
      . grind
    . clear h10 h9 h4 h3 H13 H14
      rename_i h _
      replace h := notinfirst h
      have h' := h
      specialize h newC.2.2
      --specialize h12 (newC.1.1, newC.2.2)
      rw[← List.singleton_append ]
      (repeat rw[List.map_append])
      have H : List.map Prod.fst (List.map Prod.fst [newC]) = [newC.1.1] := by simp
      rw[H]
      (repeat rw[← List.append_assoc])
      --rw[List.singleton_append ]
      rw[List.append_assoc]; rw[List.append_assoc]; rw[List.append_assoc]
      rw[List.append_assoc]
      rw[List.singleton_append]
      rw[← List.append_assoc]
      rw[@List.nodup_cons _ newC.1.1 ]
      constructor
      . rename_i x_merge x_module x_branch _ _ x_tagM x_split _ _
        by_cases newC.1.1 ∉ List.map Prod.fst (List.map Prod.fst x_merge) ++
            (List.map Prod.fst (List.map Prod.fst (List.map Prod.fst x_module)) ++
            (List.map Prod.fst (List.map Prod.fst x_split) ++ List.map Prod.fst (List.map Prod.fst x_branch)) ++
                  List.map Prod.fst (List.map Prod.fst (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) x_tagM.toList)))
        . ac_nf at *
        . rename_i h; simp only [exists_and_right, exists_eq_right, Bool.exists_bool, not_or, not_exists, not_and, not_forall, not_not] at h
          simp only [ List.mem_append] at h12
          (repeat rw[← List.map_append] at h)
          have h := map_fst h
          cases h; rename_i i' h
          ac_nf at *
          specialize h12 (newC.1.1, i') h
          specialize h' i'
          solve_by_elim
      . repeat rw[List.map_append] at h11
        ac_nf at *
    . rename_i h14 h15
      clear h10 h9 h4 h11 h14 h15
      intro elem h1
      specialize h12 elem
      by_cases elem = (newC.1.1, newC.2.2)
      . specialize H15 _ (by constructor)
        grind [List.mem_append_right]
      . obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
        repeat (rw [List.map_append] at h1)
        rw [List.map_cons] at h1; dsimp at h1
        cases h1
        · grind
        · apply List.mem_append_left
          apply h12; repeat (rw [List.map_append])
          assumption
    . clear h10 h9 h4  H13 H14 H15
      rename_i hn _
      rename_i x_tag _ _ _ _
      rw[List.map_append]
      rw[List.nodup_append]
      constructor
      . assumption
      . constructor
        . grind
        . grind
    . clear h10 h9 h4  H13 H15
      intro tag d n i h1
      specialize H14 tag d n i h1
      cases H14; rename_i H14 H14'
      constructor
      . grind
      . assumption
    . clear h10 h9 h4 H13 H14 h3 h11 h12
      grind
    . intro tag i h1
      rename_i x_tagT _ _ _ _ _
      rw[List.mem_append] at h1
      cases h1 <;> rename_i h1
      . specialize Hnew tag i h1; assumption
      . simp at h1; subst_vars
        obtain ⟨⟨newC11, newC12⟩, newC21, newC22⟩ := newC
        cases h1
        specialize Hnewnew (i, newC21, newC22)
        specialize Hnewnew (by simp)
        assumption
    · intros; apply Hnewnew; simp [*]
  . dsimp only [Module.liftR, Module.liftL, cast_eq] at h2
    replace h2 := h2.1 rfl
    simp only [List.concat_eq_append, Module.liftR, Module.liftL] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew'
    repeat rw [Prod.mk.injEq] at h
    repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . clear h11 h12 h13 h9 h10
      rename_i h
      cases h; rename_i l h4
      cases h4
      subst_vars
      intro elem n i' h1
      specialize h4 elem n i'
      grind [List.mem_of_mem_eraseIdx]
    . clear h10  --h13 h11 H13
      intro elem h1
      specialize h9 elem
      --rw[List.map_append] at h1
      rw[List.filter_append ] at h1
      rw[List.map_append] at h1
      rw[← List.append_assoc ] at h1
      rename_i x_module x_branchD x_bramchB x_tagT x_tagM x_tagD x_splitD x_splitB _
      have h1' := @List.mem_append _ elem (List.map Prod.fst (List.filter (fun x => x.2 == true) ((x_branchD ++ x_splitD).zip (x_bramchB ++ x_splitB))) ++ List.map Prod.fst (List.filter (fun x => x.2 == true) x_module)) (List.map Prod.fst (List.filter (fun x => x.2 == true) [liftF2 (liftF f) newC]))
      cases h1'; rename_i h1' h1''; clear h1''
      specialize h1' h1; clear h1
      cases h1' <;> rename_i h1
      . specialize h9 h1; assumption
      . unfold liftF2 at h1; unfold liftF at h1; simp at h1
        cases h1
        rename_i H _ _; cases H; rename_i H; cases H; rename_i H
        rename_i x_merge _ _ w _
        have H1 := @List.mem_of_getElem? _ (x_merge) w newC
        simp only [Fin.is_lt, getElem?_pos, Option.some.injEq] at H1; have H := Eq.symm H
        specialize H1 H
        obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
        specialize h12  (newCT, newCDI)
        have H1' := @List.mem_map_of_mem _ _ x_merge ((newCT, newCD), newCN, newCDI) (fun x => match x with | ((x, _), _, y) => (x, y)) H1
        (repeat rw[List.map_append] at h12)
        have H1' := List.mem_append_left (List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) (List.map Prod.fst x_module) ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) x_splitD ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) x_branchD ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) x_tagM.toList)) H1'
        ac_nf at *
        specialize h12 H1'
        specialize Hnew newCT newCDI h12
        cases Hnew; rename_i i Hnew; cases Hnew; rename_i n Hnew
        specialize h4 ((newCT, newCD), newCN, newCDI) n i H1 Hnew
        simp [ge_iff_le, zero_le, true_and] at h4
        constructor; constructor; rotate_left
        . exact i
        . exact n
        subst_vars
        simp only [gt_iff_lt, add_pos_iff, zero_lt_one, true_or, true_and]
        cases h4
        have HT := apply_true f newCDI i n newCN
        rename_i hh _
        specialize HT hh
        --simp at HT
        and_intros
        · rename_i H; rename _ = true => H'''; rw [H] at H'''
          rw [add_comm]
          solve_by_elim
        . have hf := apply_plus_one f newCDI newCN; rename_i H
          rw[← H] at hf; assumption
        . rename_i Hf _ _ H
          rw[H] at Hf
          rw[apply_plus_one_condiction] at Hf
          specialize HT Hf Hnew; omega
    . clear h9
      intro elem
      specialize h10 elem
      unfold liftF2
      unfold liftF
      simp
      intro h1
      cases h1 <;> rename_i h
      . rename_i x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB _
        have H1 := @List.mem_filter_of_mem (((TagT × T) × ℕ × T) × Bool) (fun x => x.2 == false) _ _ h
        simp only [beq_self_eq_true] at H1
        simp only [forall_const] at H1
        have H := @List.mem_map_of_mem (((TagT × T) × ℕ × T) × Bool) ((TagT × T) × ℕ × T) (List.filter (fun x => x.2 == false) ((x_branchD ++ x_splitD).zip (x_branchB ++ x_splitB))) ((elem, false)) Prod.fst H1
        simp only [] at H
        have H := List.mem_append_left (List.map Prod.fst (List.filter (fun x => x.2 == false) x_module)) H
        specialize h10 H; assumption
      . cases h <;> rename_i h
        . simp only [List.mem_append, List.mem_map, Prod.exists,
                     exists_and_right, exists_eq_right, List.length_append,
                     beq_false, List.mem_filter, Bool.not_eq_eq_eq_not,
                     Bool.not_true] at h10
          simp only [or_true, h, h10]
        . cases h;
          rename_i x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB _ _ _
          rename_i H _ _; cases H; rename_i H; cases H; rename_i H
          rename_i w _
          have H1 := @List.mem_of_getElem? _ (x_merge) w newC
          simp only [Fin.is_lt, getElem?_pos, Option.some.injEq] at H1; have H := Eq.symm H
          specialize H1 H
          obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
          specialize h12  (newCT, newCDI)
          have H1' := @List.mem_map_of_mem _ _ x_merge ((newCT, newCD), newCN, newCDI) (fun x => match x with | ((x, _), _, y) => (x, y)) H1
          (repeat rw[List.map_append] at h12)
          have H1' := List.mem_append_left (List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) (List.map Prod.fst x_module) ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) x_splitD ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) x_branchD ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) x_tagM.toList)) H1'
          ac_nf at *
          specialize h12 H1'
          specialize Hnew newCT newCDI h12
          cases Hnew; rename_i i Hnew; cases Hnew; rename_i n Hnew
          specialize h4 ((newCT, newCD), newCN, newCDI) n i H1 Hnew
          simp only [ge_iff_le, zero_le, true_and] at h4
          subst_vars; simp
          cases h4
          have HH := apply_false f newCDI i n newCN
          rename_i H
          rename_i Hf _ _ _ h
          rw[H.1] at Hf
          rw[apply_plus_one_condiction] at Hf
          specialize HH h Hf Hnew
          rw[← HH] at Hnew
          dsimp at h10
          have HH''' := HH
          cases HH'''; cases Hnew
          constructor; unfold iterate; and_intros
          . intro k hh
            subst_vars
            rename_i H
            apply H.1
            omega
          . rw [H.1,apply_plus_one]
            have ho : 1 + newCN = newCN + 1 := by omega
            rw[ho]
            generalize apply f (newCN + 1) newCDI = y at *
            cases y; congr
            -- grind [apply_plus_one]
          . omega
    . clear h9 h12 h13 h10 h4
      unfold liftF2
      unfold liftF
      rename_i H
      cases H; rename_i l H
      cases H; rename_i H1 H2
      subst x_merge'
      ac_nf at *
      rename_i x_merge x_module x_branchD _ _ x_tagM _ x_splitD _
      have H : (List.map (Prod.fst ∘ Prod.fst) (List.eraseIdx x_merge ↑l) ++
    (List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module ++
      x_merge[↑l].1.1 :: (List.map (Prod.fst ∘ Prod.fst) x_splitD ++ List.map (Prod.fst ∘ Prod.fst) x_branchD)) ++
      List.map (Prod.fst ∘ Prod.fst ∘ fun x => ((x.1, x.2.1), x.2.2)) x_tagM.toList).Perm (List.map (Prod.fst ∘ Prod.fst) x_merge ++
    (List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module ++
      (List.map (Prod.fst ∘ Prod.fst) x_splitD ++ List.map (Prod.fst ∘ Prod.fst) x_branchD)) ++
      List.map (Prod.fst ∘ Prod.fst ∘ fun x => ((x.1, x.2.1), x.2.2)) x_tagM.toList) := by
        (repeat rw[ ← List.append_assoc])
        rw[List.append_cons]
        rw[List.append_assoc _ (List.map (Prod.fst ∘ Prod.fst) x_splitD) (List.map (Prod.fst ∘ Prod.fst) x_branchD)]
        rw [List.perm_append_right_iff]
        rw [erase_map]
        . have hh := List.perm_append_comm_assoc ((List.map (Prod.fst ∘ Prod.fst) x_merge).eraseIdx ↑l) (List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module) ([x_merge[↑l].1.1] ++ (List.map (Prod.fst ∘ Prod.fst) x_splitD ++ List.map (Prod.fst ∘ Prod.fst) x_branchD))
          have h1 := @List.Perm.trans _ _ _ (List.map (Prod.fst ∘ Prod.fst) x_merge ++ List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module ++ (List.map (Prod.fst ∘ Prod.fst) x_splitD ++ List.map (Prod.fst ∘ Prod.fst) x_branchD)) hh
          rw[← List.singleton_append]
          ac_nf at *
          apply h1
          clear hh h1
          apply perm_comm
          ac_nf
          rw [List.perm_append_left_iff]
          apply List.Perm.trans
          apply List.perm_append_comm
          ac_nf
          apply List.Perm.trans
          apply List.perm_append_comm
          ac_nf
          rw [List.perm_append_left_iff]
          rw [List.perm_append_left_iff]
          apply erase_perm l
      have H := List.Perm.symm H
      ac_nf at *
      simp only [List.map_append, List.map_map] at h11
      have HH := List.Nodup.perm h11 H
      rw[← List.singleton_append] at *
      (repeat rw[ ← List.append_assoc])
      rw[ ← List.append_assoc] at HH
      rw[ ← List.append_assoc] at HH
      rw[ ← List.append_assoc] at HH
      rw[ ← List.append_assoc] at HH
      simp only [List.append_nil, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
  List.nil_append, Prod.mk.eta, List.map_map, H2]
      simp only [List.append_assoc] at *; assumption
    . clear h9 h10 h4 h11
      rename_i x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB _
      intro elem h1
      specialize h12 elem
      unfold liftF2 at h1
      unfold liftF at h1
      dsimp at *
      apply h12
      clear h12
      rename_i H ; cases H; rename_i w H; cases H; rename_i H H1
      obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
      subst x_merge'
      simp only [List.map_append,←List.eraseIdx_map,List.map_map] at h1 ⊢
      ac_nf at h1 ⊢
      by_cases helem : elem = (newCT, newCDI)
      · apply List.mem_append_left; grind
      · apply elem_in_erase_first; apply elem_in_third; assumption
        intro helem2
        apply helem; cases helem2; rfl
        contradiction
  . dsimp only [Module.liftR, Module.liftL, cast_eq] at h2
    replace h2 := h2.1 rfl
    simp only [List.concat_eq_append, Module.liftR, Module.liftL] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    repeat rw [Prod.mk.injEq] at *
    repeat with_reducible cases ‹_ ∧ _›
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    repeat rw [Prod.mk.injEq] at h
    repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . clear h10 h12 h13 h11
      intro elem h1
      specialize h9 elem
      have h1' := @List.zip_append _ _ _ [newC.1] _ [newC.2] H13
      ac_nf at *
      have H : [newC] = [newC.1].zip [newC.2] := by simp
      rw[h1'] at h1
      rw[List.filter_append] at h1
      rw[List.map_append] at h1
      rw[← List.singleton_append ] at h9
      rw[List.filter_append] at h9
      rw[List.map_append] at h9
      rw[H] at h9
      ac_nf at *
      specialize h9 h1
      assumption
    . clear h9 h12 h13 h11
      intro elem h1
      specialize h10 elem
      have h1' := @List.zip_append _ _ _ [newC.1] _ [newC.2] H13
      ac_nf at *
      have H : [newC] = [newC.1].zip [newC.2] := by simp
      rw[h1'] at h1
      rw[List.filter_append] at h1
      rw[List.map_append] at h1
      rw[← List.singleton_append ] at h10
      rw[List.filter_append] at h10
      rw[List.map_append] at h10
      rw[H] at h10
      ac_nf at *
      specialize h10 h1
      assumption
    . clear h9 h12 h13 h10 h4
      rw [← List.append_assoc ]
      rw[← List.singleton_append ] at h11
      (repeat rw[List.map_append])
      (repeat rw[List.map_append] at h11)
      have H : List.map Prod.fst [newC] = [newC.1] := by simp
      rw[H] at h11
      simp only [List.map_cons, List.cons_append, List.nil_append, List.append_assoc] at *
      (repeat rw[← List.append_assoc])
      rw[List.nodup_middle] at h11
      rename_i x_branch _ _ _ _ _ x_split _
      rw[List.nodup_middle]
      ac_nf at *
    . clear h9 h10 h4 h11 h13 h3 H13 Hnew H15
      intro elem h1
      specialize h12 elem
      grind
    . clear h3 h4 h13 h11 h12 h9 h10
      (repeat rw [← List.append_assoc ])
      (repeat rw [List.length_append])
      (repeat rw [List.length_append] at H13)
      rw[H13]; rfl
  . dsimp only [Module.liftR, Module.liftL, cast_eq] at h2
    replace h2 := h2.1 rfl
    simp only [List.concat_eq_append, Module.liftR, Module.liftL] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    repeat rw [Prod.mk.injEq] at h
    repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . clear h10 h12 h13 h11 h4 h3
      intro elem h1
      specialize h9 elem
      rw[← List.singleton_append ] at h9
      ac_nf at *
      specialize h9 h1
      assumption
    . clear h9 h12 h13 h11
      intro elem h1
      specialize h10 elem
      rw[← List.singleton_append ] at h10
      ac_nf at *
      specialize h10 h1
      assumption
    . clear h9 h12 h13 h10 h4
      rw [List.append_assoc ] at h11
      rw[← List.singleton_append ] at h11
      (repeat rw[List.map_append])
      (repeat rw[List.map_append] at h11)
      simp only [List.map_map, List.map_cons, List.cons_append, List.append_assoc] at *
      (repeat rw[← List.append_assoc])
      (repeat rw[← List.append_assoc] at h11)
      rename_i x_merge x_module _ _ _ _ _ _
      rw[@List.nodup_middle _  _ (List.map (Prod.fst ∘ Prod.fst) x_merge ++ List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module)] at h11
      rw[List.nodup_middle]
      ac_nf at *
    . clear h9 h10 h4 h11 h13 h3 H13
      intro elem h1
      specialize h12 elem
      grind
    . clear h3 h4 h13 h11 h12 h9 h10
      (repeat rw [← List.append_assoc ])
      (repeat rw [List.length_append])
      rw[← List.singleton_append ] at H13
      (repeat rw [List.length_append] at H13)
      rw[← H13]; ac_nf
  . dsimp only [Module.liftR, Module.liftL, cast_eq] at h2
    replace h2 := h2.1 rfl
    simp only [List.concat_eq_append, Module.liftR, Module.liftL] at *
    obtain ⟨cons, newC, h⟩ := h2
    . obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
      dsimp at h
      simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
      subst_vars
      cases h3
      rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
      repeat rw [Prod.mk.injEq] at h
      repeat with_reducible cases ‹_ ∧ _›
      subst_vars
      constructor <;> (try rfl) <;> (try assumption)
      . clear h10 h12 h13 h11 h4 h3
        intro elem h1
        specialize h9 elem
        rw[← List.singleton_append ] at h9
        ac_nf at *
        specialize h9 h1
        assumption
      . clear h9 h12 h13 h11
        intro elem h1
        specialize h10 elem
        rw[← List.singleton_append ] at h10
        ac_nf at *
        specialize h10 h1
        assumption
      . clear h3 h4 h13 h11 h12 h9 h10
        (repeat rw [← List.append_assoc ])
        (repeat rw [List.length_append])
        rw[← List.singleton_append ] at H13
        (repeat rw [List.length_append] at H13)
        rw[H13]
        ac_nf at *
  . dsimp only [Module.liftR, Module.liftL, cast_eq] at h2
    replace h2 := h2.1 rfl
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    repeat rw [Prod.mk.injEq] at h
    repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . clear h10 h12 H13 h13
      intro elem n i' h1 h2
      specialize h4 elem n i'
      specialize h9 elem
      cases h1
      . simp only [List.cons_append, List.map_cons, zero_le,
                   true_and, beq_true, List.zip_cons_cons, List.filter_cons_of_pos, List.mem_cons,
                   exists_and_right, true_or,
                   forall_const] at *
        cases h9; rename_i n' h9
        cases h9; rename_i h9
        repeat cases ‹_ ∧ _›
        constructor
        . grind [iterate_full_deterministic]
        . assumption
      . rename_i h
        specialize h4 h h2
        assumption
    . clear h10 h12 h13 h11 h4 h3
      intro elem h1
      specialize h9 elem
      rw[← List.singleton_append ] at h9
      rw[← @List.singleton_append _ true ] at h9
      ac_nf at h9
      rw[List.zip_append] at h9
      (repeat rw[List.filter_append] at h9)
      (repeat rw[List.filter_append] at h1)
      (repeat rw[List.map_append] at h9)
      (repeat rw[List.map_append] at h1)
      have h1 := List.mem_append_right (List.map Prod.fst (List.filter (fun x => x.2 == true) ([newC].zip [true]))) h1
      ac_nf at *
      specialize h9 h1
      . assumption
      . simp
    . clear h9 h12 h13 h10 h4 H13
      rename_i x_merge x_module _ x_tagM _ x_splitD _
      have H := @List.Nodup.perm _ _ (List.map Prod.fst (List.map Prod.fst (newC :: x_merge ++ List.map Prod.fst x_module ++ x_splitD ++ x_branchD' ++ List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) x_tagM.toList))) h11
      apply H
      simp only [List.append_assoc, Prod.mk.eta, List.cons_append, List.map_append, List.map_map, List.map_cons]
      (repeat rw [← List.append_assoc])
      have h := @List.perm_middle _ newC.1.1 (List.map (Prod.fst ∘ Prod.fst) x_merge ++ List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module ++ List.map (Prod.fst ∘ Prod.fst) x_splitD ) (List.map (Prod.fst ∘ Prod.fst) x_branchD' ++ List.map (Prod.fst ∘ Prod.fst ∘ fun x => ((x.1, x.2.1), x.2.2)) x_tagM.toList)
      ac_nf at *
    . clear h9 h10 h4 h11 h13 h3 H13 Hnew
      intro elem h1
      specialize h12 elem
      grind
    . clear h3 h4 h13 h11 h12 h9 h10
      (repeat rw [← List.append_assoc ])
      (repeat rw [List.length_append])
      rw[← List.singleton_append ] at H13
      rw[← @List.singleton_append _ true] at H13
      (repeat rw [List.length_append] at H13)
      (repeat rw[List.length_singleton] at H13)
      omega
  . dsimp only [Module.liftR, Module.liftL, cast_eq] at h2
    replace h2 := h2.1 rfl
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    repeat rw [Prod.mk.injEq] at h
    repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . intro elem
      specialize h10 elem
      rename_i X Y _ _
      rw[← List.singleton_append ] at h10
      rw[← @List.singleton_append _ false] at h10
      have Hm := @List.zip_append _ _ [newC] (x_branchD' ++ X) [false] (x_branchB' ++ Y)
      specialize Hm (by simp)
      ac_nf at *
      rw[Hm] at h10
      (repeat rw[List.filter_append] at h10)
      (repeat rw[List.map_append] at h10)
      have H : List.map Prod.fst (List.filter (fun x => x.2 == false) [(newC, false)]) = [newC] := by simp
      dsimp at h10
      rw[H] at h10
      intro h1
      have h1 := List.mem_append_right [newC] h1
      specialize h10 h1
      assumption
    . clear h9 h12 h13 h10 h4 H13
      dsimp
      obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
      dsimp
      rename_i x_merge x_module _ x_tagM _ x_splitD _ _ _
      apply @List.Nodup.perm _ (List.map Prod.fst (List.map Prod.fst (x_merge ++ List.map Prod.fst x_module ++ x_splitD ++ ((newCT, newCD), newCN, newCDI) :: x_branchD' ++ List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) x_tagM.toList)))
      . assumption
      . (repeat rw[List.map_append])
        ac_nf
        rw[List.perm_append_left_iff]
        ac_nf
        rw[List.perm_append_left_iff]
        rw[List.perm_append_left_iff]
        rw[← List.singleton_append]
        rw (occs := [2]) [← List.singleton_append ]
        (repeat rw[← List.append_assoc ])
        (repeat rw[List.map_append])
        rw[← List.append_assoc ]
        rw[List.perm_append_right_iff ]
        apply List.perm_append_comm
    . clear h9 h10 h4 h11 h13 h3 H13
      intro elem h1
      specialize h12 elem
      rename_i left right
      -- aesop
      unfold Graphiti.LoopRewrite.iterate at *
      simp only [Batteries.AssocList.toList] at h1
      grind
    . grind
    . intro tag i n i' H
      rename_i x_merge x_module _ x_tagM _ x_splitD _ _ _
      cases (decEq tag newC.1.1)
      . specialize H14 tag i n i'
        rename_i h
        have HH := @find?_cons_neq _ _ _ tag (newC.1.2, newC.2) newC.1.1 x_tagM h
        rw[HH] at H
        specialize H14 H
        assumption
      . subst tag
        rw[find?_cons_eq] at H
        repeat with_reducible cases ‹_ ∧ _›
        subst_vars
        rename_i H _ _
        obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
        cases H; rename_i i'' H
        constructor
        · grind
        · simp only [List.cons_append, List.map_append, List.map_map,
                    List.map_cons, List.mem_append, List.mem_cons,
                    List.length_cons, List.length_append, List.zip_cons_cons,
                    List.filter_cons_of_neg, List.mem_filter, beq_false,
                    List.filter_cons_of_pos, Bool.not_eq_eq_eq_not, Bool.not_true, forall_eq_or_imp] at *
          grind

/-
# Proof refinment rhsGhost ⊑ lhs
-/

@[simp]
theorem input_rule_isData {input_rule} :
  (lhsEvaled.inputs.find? ↑"i_in") = .some input_rule ->
  T = input_rule.fst := by
  unfold lhsEvaled
  simp; intro h1
  subst_vars; rfl

def init_node_state (s : List Bool × Bool) : Prop :=
  (s.2 = false -> s.1 = []) ∧ (s.2 = true -> s.1 = [false])

omit e in
theorem false_is_init_node_state :
  init_node_state ([false], true) := by simp [init_node_state]

omit e in
theorem empty_is_init_node_state :
  init_node_state ([], false) := by simp [init_node_state]

inductive lhs_is_empty  : lhsType -> Prop where
| intro : ∀ (s : lhsType) muxF init_s,
  ([], [], init_s, [], ([], []), ([], []), ([], []), [], muxF, []) = s ->
  init_node_state init_s ->
  lhs_is_empty s

/-- Take one internal step of `lhsEvaled` with its `k`-th internal rule, inferring the next state. -/
local macro "lhs_step " k:num : tactic => `(tactic| (
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate $k apply List.mem_cons_of_mem); apply List.mem_cons_self
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> first | rfl | (apply Exists.intro; trivial)))

theorem flush_lhs_continue {v muxF} :
  existSR lhsEvaled.internals
    ([], [], ([], true), [(v, true)], ([], []), ([], []), ([], []), [], muxF, [])
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [v], muxF, []) := by
  lhs_step 3; lhs_step 4; lhs_step 5; lhs_step 1; lhs_step 2; lhs_step 7; lhs_step 8
  apply existSR.done

theorem flush_lhs_exit {v muxF} :
  existSR lhsEvaled.internals
    ([], [], ([], true), [(v, false)], ([], []), ([], []), ([], []), [], muxF, [])
    ([v], [], ([false], true), [], ([], []), ([], []), ([], []), [], muxF, []) := by
  lhs_step 3; lhs_step 4; lhs_step 5; lhs_step 1; lhs_step 2; lhs_step 9
  apply existSR.done

/-- A value waiting on the loop-back mux input goes through the mux and into `f`. -/
private theorem flush_lhs_mux_true {x p muxF} :
  f x = p →
  existSR lhsEvaled.internals
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [x], muxF, [])
    ([], [], ([], true), [p], ([], []), ([], []), ([], []), [], muxF, []) := by
  rintro rfl
  lhs_step 0; lhs_step 6; apply existSR.done

/-- A fresh input value goes through the mux and into `f`. -/
private theorem flush_lhs_mux_false {x p muxF init_s} :
  init_node_state init_s →
  f x = p →
  existSR lhsEvaled.internals
    ([], [], init_s, [], ([], []), ([], []), ([], []), [], x :: muxF, [])
    ([], [], ([], true), [p], ([], []), ([], []), ([], []), [], muxF, []) := by
  rintro hi rfl
  obtain rfl | rfl : init_s = ([], false) ∨ init_s = ([false], true) := by
    obtain ⟨l, _ | _⟩ := init_s <;> grind [init_node_state]
  all_goals lhs_step 0; lhs_step 6; apply existSR.done

theorem flush_lhs_loop {m i v n muxF} :
  iterate f i n v →
  m + 1 < n →
  existSR lhsEvaled.internals
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(apply f m i).1], muxF, [])
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(apply f (m + 1) i).1], muxF, []) := by
  intro it hm
  apply existSR_transitive _ _ _ _ (flush_lhs_mux_true (by grind [apply, iterate])) flush_lhs_continue

theorem flush_lhs_init1 {i muxF init_s} :
  init_node_state init_s ->
  (f i).2 = true →
  existSR lhsEvaled.internals
    ([], [], init_s, [], ([], []), ([], []), ([], []), [], i :: muxF, [])
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(f i).1], muxF, []) := by
  intro it hm
  apply existSR_transitive _ _ _ _ (flush_lhs_mux_false it (by grind)) flush_lhs_continue

theorem flush_lhs_init2 {i muxF init_s} :
  init_node_state init_s ->
  (f i).2 = false →
  existSR lhsEvaled.internals
    ([], [], init_s, [], ([], []), ([], []), ([], []), [], i :: muxF, [])
    ([(f i).1], [], ([false], true), [], ([], []), ([], []), ([], []), [], muxF, []) := by
  intro it hm
  apply existSR_transitive _ _ _ _ (flush_lhs_mux_false it (by grind)) flush_lhs_exit

theorem flush_lhs_end {m i v muxF} :
  iterate f i (m + 1) v →
  existSR lhsEvaled.internals
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(apply f m i).1], muxF, [])
    ([v], [], ([false], true), [], ([], []), ([], []), ([], []), [], muxF, []) := by
  intro it
  apply existSR_transitive _ _ _ _ (flush_lhs_mux_true (by grind [apply, iterate])) flush_lhs_exit

theorem flush_lhs_loop_compl {m n i v muxF} :
  iterate f i n v →
  m < n →
  existSR lhsEvaled.internals
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [i], muxF, [])
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(apply f m i).1], muxF, []) := by
  induction m with
  | zero => grind [existSR.done, apply]
  | succ m ihm => grind [existSR_transitive, flush_lhs_loop]

theorem iterate_f_false {i n v} :
  iterate f i n v →
  (f i).2 = false →
  n = 1 ∧ v = (f i).1 := by
  intro hi; have := hi.1 1; grind [iterate, apply]

theorem apply_twice' {m n i} :
  n > 0 →
  apply f n (apply f m i).1 = apply f (n + m) i := by
  induction n with
  | zero => grind
  | succ n ih => cases n <;> grind [apply]

theorem apply_twice {m n i} :
  (apply f n (apply f m i).1).1 = (apply f (n + m) i).1 := by
  cases n <;> grind [apply_twice', apply]

theorem iterate_apply {m n i v} :
  n > 0 →
  iterate f i (n + m) v →
  iterate f (apply f m i).1 n v := by
  grind [iterate, apply_twice', apply]

theorem flush_lhs {i v n muxF init_s} :
  iterate f i n v →
  init_node_state init_s ->
  existSR lhsEvaled.internals
    ([], [], init_s, [], ([], []), ([], []), ([], []), [], i :: muxF, [])
    ([v], [], ([false], true), [], ([], []), ([], []), ([], []), [], muxF, []) := by
  intro hi hn
  cases hb : (f i).2
  · obtain ⟨rfl, rfl⟩ := iterate_f_false hi hb
    apply flush_lhs_init2 hn hb
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by grind [iterate, apply]⟩
    have hk : iterate f (apply f 1 i).1 (k + 1) v := iterate_apply (by omega) hi
    apply existSR_transitive _ _ _ _ (flush_lhs_init1 hn hb)
    apply existSR_transitive _ _ _ _ (flush_lhs_loop_compl hk (m := k) (by omega)) (flush_lhs_end hk)

inductive φ : rhsGhostType -> lhsType -> Prop where
| intro : ∀ (i :rhsGhostType) i_merge i_module i_branchD i_branchB i_tagT i_tagM i_tagD i_splitD i_splitB s_queue_out  s_queue
            (s : lhsType) s_initL s_initB s_module s_splitD s_splitB s_branchD s_branchB s_forkR s_forkL s_muxT s_muxF s_muxC,
  ⟨i_module, ⟨i_branchD, i_branchB⟩, i_merge, ⟨i_tagT, i_tagM, i_tagD ⟩, ⟨i_splitD, i_splitB⟩⟩ = i ->
  ⟨s_queue_out, s_queue, ⟨s_initL, s_initB⟩, s_module, ⟨s_splitD, s_splitB⟩, ⟨s_branchD, s_branchB⟩, ⟨s_forkR, s_forkL⟩, s_muxT, s_muxF, s_muxC ⟩ = s ->
  ((i_tagT.map Prod.snd) ++ (i_tagD.map Prod.fst)) = s_muxF ->
  state_relation i ->
  lhs_is_empty s ->
  φ i s

theorem φ_empty : φ default_rhs default_lhs := by
  constructor <;> try trivial
  · apply state_relation_empty
  · constructor <;> try trivial

omit e in
theorem nodup_in_first {α} {a b c d e : List α} {l} :
  (a ++ (b ++ (c ++ (d ++ e)))).Nodup →
  l ∈ e →
  l ∉ ((a ++ b) ++ c) ++ d := by
  simp; intros; grind

omit e in
private theorem eraseAll_toList_key_ne {α β} [DecidableEq α] {m : AssocList α β} {tag : α} {x : α × β} :
    x ∈ (m.eraseAll tag).toList → x.1 ≠ tag := by
  grind [AssocList.keysList_find?_isSome_iff, AssocList.keysList, AssocList.find?_eraseAll_eq]

omit e in
private theorem nodup_append_toList_key_ne {α β γ δ} [DecidableEq α] {l : List ((α × β) × γ × δ)}
    {m : AssocList α (β × γ × δ)} {tag v x} :
  (((l ++ m.toList.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))).map Prod.fst).map Prod.fst).Nodup →
  (tag, v) ∈ m.toList → x ∈ l → x.1.1 ≠ tag := by
  simp only [List.map_append, List.map_map, List.nodup_append, List.mem_map]
  grind

omit e in
/-- Removing `tag` from the tagger map keeps the tag-set invariant of `state_relation`. -/
private theorem mem_tagT_of_eraseAll {α β γ δ} [DecidableEq α] {l : List ((α × β) × γ × δ)}
    {m : AssocList α (β × γ × δ)} {tagT : List (α × δ)} {tag init elem val iters} :
  (((l ++ m.toList.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))).map Prod.fst).map Prod.fst).Nodup →
  (∀ elem ∈ (l ++ m.toList.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))).map (fun ((x, _), _, y) => (x, y)),
    elem ∈ (tag, init) :: tagT) →
  m.find? tag = some (val, iters, init) →
  elem ∈ (l ++ (m.eraseAll tag).toList.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))).map (fun ((x, _), _, y) => (x, y)) →
  elem ∈ tagT := by
  intro hnodup hmem hfind hin
  have hl := fun x => nodup_append_toList_key_ne (x := x) hnodup (AssocList.find?_in_toList hfind)
  simp only [List.map_append, List.map_map, List.mem_append, List.mem_map] at hin hmem
  obtain ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ := hin
  · grind
  · have := AssocList.in_eraseAll_list' hx
    have := eraseAll_toList_key_ne hx
    grind

theorem state_relation_output_preserved {x_splitD x_splitB x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_merge tag val iters init} :
  state_relation (x_module, (x_branchD, x_branchB), x_merge, ((tag, init) :: x_tagT, x_tagM, x_tagD), (x_splitD, x_splitB)) →
  x_tagM.find? tag = .some (val, iters, init) →
  state_relation (x_module, (x_branchD, x_branchB), x_merge, (x_tagT, x_tagM.eraseAll tag, x_tagD), (x_splitD, x_splitB)) := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨⟩, h1, h2, rfl, rfl, rfl, rfl, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ hfind
  refine .intros _ x_merge x_module x_branchD x_branchB x_tagT (x_tagM.eraseAll tag) x_tagD x_splitD x_splitB _ _ _ _
    rfl h1 h2 rfl rfl rfl rfl h7 h8 (in_eraseAll_noDup _ _ h9) (fun _ => mem_tagT_of_eraseAll h9 h10 hfind) (by grind) h12
    ?_ h14 (by grind) h16
  intro tag' d n i hfind'
  have := AssocList.find?_eraseAll_neg_full hfind'
  grind

/-- Pushing a fresh input `(v, 0, v)` into the tagger preserves `state_relation`. -/
private theorem state_relation_input_preserved {x_module x_branchD x_branchB x_merge x_tagT x_tagM x_tagD x_splitD x_splitB v} :
  state_relation (x_module, (x_branchD, x_branchB), x_merge, (x_tagT, x_tagM, x_tagD), (x_splitD, x_splitB)) →
  state_relation (x_module, (x_branchD, x_branchB), x_merge, (x_tagT, x_tagM, x_tagD.concat (v, 0, v)), (x_splitD, x_splitB)) := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨⟩, h1, h2, rfl, rfl, rfl, rfl, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  refine .intros _ x_merge x_module x_branchD x_branchB x_tagT x_tagM _ x_splitD x_splitB _ _ _ _
    rfl ?_ h2 rfl rfl rfl rfl h7 h8 h9 h10 h11 h12 h13 ?_ h15 ?_ <;>
    grind [iterate_full_complete f (i := v)]

/-- The tag at the head of the tagger queue was iterated to produce the value stored for it. -/
private theorem state_relation_find {x_module x_branchD x_branchB x_merge x_tagT x_tagM x_tagD x_splitD x_splitB tag init val iters init'} :
  state_relation (x_module, (x_branchD, x_branchB), x_merge, ((tag, init) :: x_tagT, x_tagM, x_tagD), (x_splitD, x_splitB)) →
  x_tagM.find? tag = some (val, iters, init') →
  init' = init ∧ iterate f init iters val := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨⟩, -, -, -, -, -, -, -, -, -, -, h11, -, h13, -, -, -⟩ hfind
  obtain ⟨hmem, ⟨hit⟩⟩ := h13 _ _ _ _ hfind
  grind

private theorem φ_iff {i s} :
    φ i s ↔ state_relation i ∧ ∃ init_s, init_node_state init_s ∧
      s = ([], [], init_s, [], ([], []), ([], []), ([], []), [], i.2.2.2.1.1.map Prod.snd ++ i.2.2.2.1.2.2.map Prod.fst, []) := by
  constructor
  · rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨⟩, ⟨⟩, hmuxF, hsr, ⟨_, init_s, ⟨⟩, hinit⟩⟩
    grind
  · rintro ⟨hsr, init_s, hinit, rfl⟩
    exact .intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hsr (.intro _ _ _ rfl hinit)

instance : MatchInterface rhsGhostEvaled lhsEvaled := by
  unfold rhsGhostEvaled lhsEvaled
  solve_match_interface

set_option maxHeartbeats 0 in
theorem refine:
    rhsGhostEvaled ⊑_{φ} lhsEvaled := by
  intro ⟨x1, ⟨i_branchD, i_branchB⟩, i_merge, ⟨i_tagT, i_tagM, i_tagD⟩, ⟨i_splitD, i_splitB⟩⟩ y HPerm
  obtain ⟨hsr, init_s, hinit, rfl⟩ := φ_iff.mp HPerm
  apply Module.comp_refines.mk
  · intro ident ⟨x'1, ⟨_, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩⟩ v Hcontains
    unfold rhsGhostEvaled at *
    dsimp [Module.liftR, Module.liftL] at Hcontains v
    obtain rfl : { inst := InstIdent.top, name := "i_in" } = ident := by
      simpa using PortMap.rule_contains Hcontains
    rw [PortMap.rw_rule_execution (getIO_cons_eq (α := rhsGhostType))] at Hcontains
    unfold PortMap.getIO
    dsimp [reduceAssocListfind?, Module.liftR, Module.liftL] at Hcontains ⊢
    obtain ⟨⟨⟨⟨⟨rfl, rfl, rfl⟩, ⟨⟩⟩, rfl⟩, ⟨⟩⟩, rfl⟩ := Hcontains
    refine ⟨_, _, ?_, existSR.done _, φ_iff.mpr ⟨state_relation_input_preserved hsr, _, hinit, rfl⟩⟩
    simp; rfl
  · intro ident ⟨x'1, ⟨_, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩⟩ v Hcontains
    unfold rhsGhostEvaled at *
    dsimp [Module.liftR, Module.liftL] at Hcontains v
    obtain rfl : { inst := InstIdent.top, name := "o_out" } = ident := by
      simpa using PortMap.rule_contains Hcontains
    rw [PortMap.rw_rule_execution (getIO_cons_eq (α := rhsGhostType))] at Hcontains
    unfold PortMap.getIO
    dsimp [reduceAssocListfind?, Module.liftR, Module.liftL] at Hcontains ⊢
    obtain ⟨⟨⟨⟨⟨⟨tag, init⟩, ⟨iters, init'⟩, rfl, hfind, rfl, rfl⟩, ⟨⟩⟩, rfl⟩, ⟨⟩⟩, rfl⟩ := Hcontains
    obtain ⟨rfl, hit⟩ := state_relation_find hsr hfind
    refine ⟨_, _, flush_lhs hit hinit, ?_,
      φ_iff.mpr ⟨state_relation_output_preserved hsr hfind, _, false_is_init_node_state, rfl⟩⟩
    simp; rfl
  · intro rule ⟨x'1, ⟨_, _⟩, _, ⟨_, _, _⟩, ⟨_, _⟩⟩ hr hrr
    have hmuxF := state_relation_preserve_input _ _ rule hr hrr hsr
    refine ⟨_, existSR.done _, φ_iff.mpr ⟨state_relation_preserve _ _ rule hr hrr hsr, _, hinit, ?_⟩⟩
    simp_all

theorem refines_init :
  Module.refines_initial rhsGhostEvaled lhsEvaled φ := by
  unfold Module.refines_initial; intro i hi
  have hi' := default_rhs_eq hi; subst i
  refine ⟨_, default_lhs_eq, φ_empty⟩

theorem refines : rhsGhostEvaled ⊑ lhsEvaled := ⟨inferInstance, φ, refine, refines_init⟩

noncomputable def verified_rewrite : VerifiedRewrite Env.well_formed rewrite.pattern (rewrite.rewrite (e.types.map ("", ·)) ("", e.max_type)) e.ε where
  ε_ext := ε_rhs_ghost
  ε_ext_wf := ε_rhs_ghost_wf
  ε_compatible := FinEnv.independent_subset_of_union ε_rhs_ghost_independent
  rhs_wf := ghost_rhs_wf
  rhs_wt := ghost_rhs_wt
  lhs_locally_wf := by dsimp [rewrite]; apply lhsLower_locally_wf
  refinement := by
    intros
    apply Module.refines_eq_relax
    apply rhs_ghost_evaled_eq.symm
    rotate_left
    apply refines
    dsimp [rewrite]; rw [Vector.map_map]; dsimp; rw [Vector.map_id]
    apply lhs_evaled_eq.symm

/--
info: 'Graphiti.LoopRewrite.verified_rewrite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms verified_rewrite

end Proof
end Graphiti.LoopRewrite
