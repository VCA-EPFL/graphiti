import Graphiti.Core.ExprLowLemmas
import Graphiti.Core.Rewrites.LoopRewriteCorrect
import Mathlib
import Aesop

namespace Graphiti.LoopRewrite

open Batteries (AssocList)

--open matchGoal

open Lean hiding AssocList
open Meta Elab

open StringModule

section Proof

variable {Data : Type}
variable (DataS : String)
variable (f : Data → Data × Bool)

variable [Inhabited Data]

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

theorem exists_minimal_m {i} {m} :
  (apply f m i).2 = false →
  ∃ m', (apply f m' i).2 = false ∧ (∀ n, n < m' → (apply f n i).snd = true) := by
  induction m using Nat.strong_induction_on; grind

theorem iterate_deterministic {i n i' n2 i'2} :
  iterate f i n i' →
  iterate f i n2 i'2 →
  n = n2 ∧ i' = i'2 := by grind [iterate]

theorem iterate_full_deterministic {i n i' n2 i'2} :
  iterate_full f i n i' →
  iterate_full f i n2 i'2 →
  n = n2 ∧ i' = i'2 := by
  intro ha hb; cases ha <;> cases hb <;> grind [iterate_deterministic, iterate]

theorem iterate_full_complete {i} :
  ∃ n d, iterate_full f i n d := by
  cases Classical.em (∀ m, (apply f m i).snd = true)
  · exists none, none; constructor; assumption
  · simp at *; rename_i h; obtain ⟨x, h⟩ := h
    have := exists_minimal_m f h
    obtain ⟨m', ha⟩ := this
    exists m', (apply f m' i).1
    constructor; constructor <;> try grind
    rw [←ha.1]; constructor; simp
    cases m' <;> grind [apply]

inductive lt_current : Nat → Option Nat → Prop :=
| some {n final} : n < final → lt_current n (some final)
| none {n} : lt_current n none

inductive state_relation : rhsGhostType Data -> Prop where
| intros : ∀ (s :  rhsGhostType Data) x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB x_split_branchT x_split_branchF x_moduleT x_moduleF,
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

def default_lhs : lhsType Data := ⟨default, default, ⟨default, true⟩, default, ⟨default, default⟩ ,⟨default, default⟩, ⟨default, default⟩, default, default, default ⟩

theorem state_relation_empty :
  state_relation f default := by
  constructor <;> try trivial
  · intro elem hin; cases hin
  · intro elem n i' hin; cases hin
  · intro _ hin; cases hin
  · intro _ hin; cases hin
  · constructor
  · intro _ hin; cases hin
  · constructor
  · intro _ _ _ _ hfind; simp at hfind
  · intro _ hin; cases hin
  · intro _ _ hin; cases hin
  · intro _ hin; cases hin

/-
# Proof state_relation_prserve in rhsGhost
-/

theorem alpa {α : Type} {a : α} {l : List α} : a :: l = [a] ++ l := by simp only [List.singleton_append]

attribute [aesop unsafe 50% forward] List.Nodup.cons List.perm_append_singleton
attribute [aesop norm] List.perm_comm

axiom apply_plus_one (i: Data) (n : Nat) : (f (apply f n i).1).1 = (apply f (1 + n) i).1

axiom apply_plus_one_condiction (i: Data) (n : Nat) : (f (apply f n i).1).2 = (apply f (n +1) i).2

axiom apply_true (i : Data) (i' : Option Data) (n : Option Nat) ( k : Nat) : lt_current k n -> (apply f (k + 1) i).2 = true -> iterate_full f i n i' -> lt_current (k + 1) n

axiom apply_false (i : Data) (i' : Option Data) (n : Option Nat) ( k : Nat) : lt_current k n -> (apply f (k + 1) i).2 = false -> iterate_full f i n i' -> some (k + 1) = n


axiom erase_map {α β γ : Type} {a : α} {b : β} {c : γ} {l : List ((α × β) × γ)} {k : Nat} : List.map (Prod.fst ∘ Prod.fst) (List.eraseIdx l k) = (List.map (Prod.fst ∘ Prod.fst) l).eraseIdx k

axiom perm_comm {α : Type} {l1 l2 l3 : List α} : (l1).Perm (l2 ++ l3) -> (l1).Perm (l3 ++ l2)

axiom erase_perm  {α β γ : Type} {a : α} {b : β} {c : γ} {l : List ((α × β) × γ)} (k : Fin (List.length l)): ((List.map (Prod.fst ∘ Prod.fst) l).eraseIdx k ++ [(l[k].1.1)]).Perm (List.map (Prod.fst ∘ Prod.fst) l)

theorem map_fst {α β γ η  : Type} {i : α} {l : List ((α × β) × γ × η)}:  i ∈ (l.map Prod.fst).map Prod.fst -> ∃ i', (i, i') ∈ l.map (fun x => (x.1.1, x.2.2)) := by aesop


axiom getIO_cons_neq {α} {a b x} {xs}:
  a ≠ b ->
  PortMap.getIO (.cons a x xs) b = @PortMap.getIO String _ α xs b

theorem getIO_nil {α} {b}:
  @PortMap.getIO String _ α .nil b = ⟨ Unit, λ _ _ _ => False ⟩ := by aesop

axiom getIO_cons_eq {α} {a x} {xs}:
  @PortMap.getIO String _ α (.cons a x xs) a = x

axiom find?_cons_eq {α β} [DecidableEq α] {a x} {xs : Batteries.AssocList α β}:
  Batteries.AssocList.find? a (xs.cons a x) = x

axiom find?_cons_neq {α β} [DecidableEq α] {a x} y {xs : Batteries.AssocList α β}:
  ¬(a = y) -> Batteries.AssocList.find? a (xs.cons y x) = Batteries.AssocList.find? a xs

axiom forall₂_cons_reverse {α}{β} {R : α → β → Prop} {a b l₁ l₂} :
    List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) ↔ R a b ∧ List.Forall₂ R l₁ l₂

@[simp] axiom find?_eraseAll_neg {α β} { T : α} { T' : α} [DecidableEq α] (a : AssocList α β) (i : β):
  Batteries.AssocList.find? T (AssocList.eraseAllP_TR (fun k x => k == T') a) = some i -> ¬ (T = T') -> (Batteries.AssocList.find? T a = some i) -- := by
  -- intro hfind hne
  -- have := find?_eraseAll_neq (a := a) hne
  -- unfold eraseAll at this
  -- simp only [BEq.beq] at this; rw [eraseAllP_TR_eraseAll] at *; rwa [this] at hfind

@[simp] axiom find?_eraseAll_list {α β} { T : α} [DecidableEq α] (a : AssocList α β):
  List.find? (fun x => x.1 == T) (AssocList.eraseAllP_TR (fun k x => k == T) a).toList = none--  := by
  -- rw [←Batteries.AssocList.findEntry?_eq, ←Option.map_eq_none', ←Batteries.AssocList.find?_eq_findEntry?]
  -- have := find?_eraseAll_eq a T; unfold eraseAll at *; rw [eraseAllP_TR_eraseAll] at *; assumption

theorem state_relation_preserve_input:
  ∀ (s s' : rhsGhostType Data) rule,
    rule ∈ ( rhsGhostEvaled f).internals ->
    rule s s' ->
    state_relation f s ->
    (List.map Prod.snd s.2.2.2.1.1 ++ List.map Prod.fst s.2.2.2.1.2.2) = (List.map Prod.snd s'.2.2.2.1.1 ++ List.map Prod.fst s'.2.2.2.1.2.2) := by
  intro s s' rule hrulein hrule hstate
  dsimp [rhsGhostEvaled] at hrulein
  fin_cases hrulein <;> try grind
  dsimp [Module.liftR, Module.liftL] at *
  grind

axiom in_eraseAll_noDup {α β γ δ} {l : List ((α × β) × γ × δ)} (Ta : α) [DecidableEq α](a : AssocList α (β × γ × δ)):
  (List.map Prod.fst ( List.map Prod.fst (l ++ (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) a.toList)))).Nodup ->
  (List.map Prod.fst ( List.map Prod.fst (l ++ List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) (AssocList.eraseAllP_TR (fun k x => decide (k = Ta)) a).toList))).Nodup

@[simp] axiom in_eraseAll_list {α β} {Ta : α} {elem : (α × β)} [DecidableEq α] (a : AssocList α β):
  elem ∈ (AssocList.eraseAllP_TR (fun k x => decide (k = Ta)) a).toList -> elem ∈ a.toList

@[simp] axiom not_in_eraseAll_list {α β} {Ta : α} {elem : (α × β)} [DecidableEq α] (a : AssocList α β):
  elem ∈ (AssocList.eraseAllP_TR (fun k x => decide (k = Ta)) a).toList -> elem.1 = Ta -> False

axiom notinfirst {A B} {x : List (A × B)} {a} :
  a ∉ List.map Prod.fst x → ∀ y, (a, y) ∉ x

theorem elem_in_third {α} {e : α} {a b c d : List _} :
  e ∈ a ++ (b ++ (c ++ d)) → e ∈ a ++ (b ++ d) := by sorry

theorem elem_in_erase_first {α} {e : α} {a b : List _} {n} :
  e ∈ (List.eraseIdx a n) ++ b → e ∈ a ++ b := by sorry

set_option maxHeartbeats 0 in
theorem state_relation_preserve:
  ∀ (s s' : rhsGhostType Data) rule,
    rule ∈ ( rhsGhostEvaled f).internals ->
    rule s s' ->
    state_relation f s ->
    state_relation f s' := by
  intro s s' rule h1 h2 h3
  let ⟨ x_module, ⟨x_branchD, x_branchB⟩, x_merge, ⟨x_tagT, x_tagM, x_tagD ⟩, ⟨x_splitD, x_splitB⟩⟩ := s
  let ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := s'
  fin_cases h1
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnewnew
    simp at h
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
        · trivial
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
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew'
    simp at h
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
        have H1 := @List.mem_of_get? _ (x_merge) w newC
        simp only [List.get?_eq_getElem?, Fin.is_lt, getElem?_pos, Option.some.injEq] at H1; have H := Eq.symm H
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
        have H1 := @List.mem_filter_of_mem (((TagT × Data) × ℕ × Data) × Bool) (fun x => x.2 == false) _ _ h
        simp only [beq_self_eq_true] at H1
        simp only [forall_const] at H1
        have H := @List.mem_map_of_mem (((TagT × Data) × ℕ × Data) × Bool) ((TagT × Data) × ℕ × Data) (List.filter (fun x => x.2 == false) ((x_branchD ++ x_splitD).zip (x_branchB ++ x_splitB))) ((elem, false)) Prod.fst H1
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
          have H1 := @List.mem_of_get? _ (x_merge) w newC
          simp only [List.get?_eq_getElem?, Fin.is_lt, getElem?_pos, Option.some.injEq] at H1; have H := Eq.symm H
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
          . exact newC.1.1
          . exact newC.1.2
          . exact newC.2
        . exact newC.1.1
        . exact newC.1.2
        . exact newC.2
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
      dsimp [Function.comp] at h1 ⊢
      ac_nf at h1 ⊢; apply elem_in_third; apply elem_in_erase_first; assumption
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    simp only [Prod.mk.injEq] at h
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
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    simp at h
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
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    . obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
      dsimp at h
      simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
      subst_vars
      cases h3
      rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
      simp only [Prod.mk.injEq] at h
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
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    simp only [Prod.mk.injEq] at h
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
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append, Module.liftR, Module.liftL] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all only [Prod.mk.injEq]; repeat with_reducible cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    simp only [Prod.mk.injEq] at h
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
      unfold Graphiti.LoopRewrite.iterate at H14
      unfold Graphiti.LoopRewrite.iterate at Hnew
      unfold Graphiti.LoopRewrite.iterate at Hnew2
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

omit [Inhabited Data] in
@[simp]
theorem input_rule_isData {input_rule} :
  ((lhsEvaled f).inputs.find? ↑"i_in") = .some input_rule ->
  Data = input_rule.fst := by
  unfold lhsEvaled
  simp; intro h1
  subst_vars; rfl

def init_node_state (s : List Bool × Bool) : Prop :=
  (s.2 = false -> s.1 = []) ∧ (s.2 = true -> s.1 = [false])

theorem false_is_init_node_state :
  init_node_state ([false], true) := by simp [init_node_state]

inductive lhs_is_empty  : lhsType Data -> Prop where
| intro : ∀ (s : lhsType Data) muxF init_s,
  ([], [], init_s, [], ([], []), ([], []), ([], []), [], muxF, []) = s ->
  init_node_state init_s ->
  lhs_is_empty s

theorem flush_lhs_continue {v muxF} :
  existSR (lhsEvaled f).internals
    ([], [], ([], true), [(v, true)], ([], []), ([], []), ([], []), [], muxF, [])
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [v], muxF, []) := by
  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 3 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 4 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 5 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 1 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 2 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 7 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 8 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR.done

theorem flush_lhs_exit {v muxF} :
  existSR (lhsEvaled f).internals
    ([], [], ([], true), [(v, false)], ([], []), ([], []), ([], []), [], muxF, [])
    ([v], [], ([false], true), [], ([], []), ([], []), ([], []), [], muxF, []) := by
  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 3 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 4 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 5 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 1 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 2 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR_transitive
  apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
  · (iterate 9 apply List.mem_cons_of_mem); constructor
  · dsimp [Module.connect'', Module.liftR, Module.liftL]
    and_intros <;> try (intro; contradiction)
    intro hwf; clear hwf
    apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    apply Exists.intro _
    dsimp
    and_intros <;> try rfl
  · apply existSR.done

  apply existSR.done

theorem flush_lhs_loop {m i v n muxF} :
  iterate f i n v →
  m + 1 < n →
  existSR (lhsEvaled f).internals
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(apply f m i).1], muxF, [])
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(apply f (m + 1) i).1], muxF, []) := by
  intro it hm
  apply existSR_transitive; rotate_left 1
  · apply flush_lhs_continue
  · unfold lhsEvaled
    apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    · (iterate 0 apply List.mem_cons_of_mem); constructor
    · dsimp [Module.connect'', Module.liftR, Module.liftL]
      and_intros <;> try (intro; contradiction)
      intro hwf; clear hwf
      apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
      apply Exists.intro _
      dsimp
      and_intros <;> try rfl
    · apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
      · (iterate 6 apply List.mem_cons_of_mem); constructor
      · dsimp [Module.connect'', Module.liftR, Module.liftL]
        and_intros <;> try (intro; contradiction)
        intro hwf; clear hwf
        apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        apply Exists.intro _
        dsimp
        and_intros <;> try rfl
        exists true
      · rw [show (f (apply f m i).1) = ((f (apply f m i).1).1, true) by grind [apply, iterate]]; apply existSR.done

theorem flush_lhs_init1 {i muxF init_s} :
  init_node_state init_s ->
  (f i).2 = true →
  existSR (lhsEvaled f).internals
    ([], [], init_s, [], ([], []), ([], []), ([], []), [], i :: muxF, [])
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(f i).1], muxF, []) := by
  intro it hm
  obtain ⟨h1, h2⟩ := init_s
  dsimp [init_node_state] at it
  cases h2b : h2
  · subst h2; obtain ⟨it, -⟩ := it; obtain it := it rfl; subst h1
    apply existSR_transitive; rotate_left 1
    · rw [show (f i).1 = (apply f 1 i).1 by rfl]; apply flush_lhs_continue
    · unfold lhsEvaled
      apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
      · (iterate 0 apply List.mem_cons_of_mem); constructor
      · dsimp [Module.connect'', Module.liftR, Module.liftL]
        and_intros <;> try (intro; contradiction)
        intro hwf; clear hwf
        apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        apply Exists.intro _
        dsimp
        and_intros <;> try rfl
      · apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        · (iterate 6 apply List.mem_cons_of_mem); constructor
        · dsimp [Module.connect'', Module.liftR, Module.liftL]
          and_intros <;> try (intro; contradiction)
          intro hwf; clear hwf
          apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
          apply Exists.intro _
          dsimp
          and_intros <;> try rfl
          exists false
        · rw [show f i = ((f i).1, true) by rw [←hm]]; apply existSR.done
  · subst h2; obtain ⟨-, it⟩ := it; obtain it := it rfl; subst h1
    apply existSR_transitive; rotate_left 1
    · rw [show (f i).1 = (apply f 1 i).1 by rfl]; apply flush_lhs_continue
    · unfold lhsEvaled
      apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
      · (iterate 0 apply List.mem_cons_of_mem); constructor
      · dsimp [Module.connect'', Module.liftR, Module.liftL]
        and_intros <;> try (intro; contradiction)
        intro hwf; clear hwf
        apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        apply Exists.intro _
        dsimp
        and_intros <;> try rfl
      · apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        · (iterate 6 apply List.mem_cons_of_mem); constructor
        · dsimp [Module.connect'', Module.liftR, Module.liftL]
          and_intros <;> try (intro; contradiction)
          intro hwf; clear hwf
          apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
          apply Exists.intro _
          dsimp
          and_intros <;> try rfl
          exists false
        · rw [show f i = ((f i).1, true) by rw [←hm]]; apply existSR.done

theorem flush_lhs_init2 {i muxF init_s} :
  init_node_state init_s ->
  (f i).2 = false →
  existSR (lhsEvaled f).internals
    ([], [], init_s, [], ([], []), ([], []), ([], []), [], i :: muxF, [])
    ([(f i).1], [], ([false], true), [], ([], []), ([], []), ([], []), [], muxF, []) := by
  intro it hm
  obtain ⟨h1, h2⟩ := init_s
  dsimp [init_node_state] at it
  cases h2b : h2
  · subst h2; obtain ⟨it, -⟩ := it; obtain it := it rfl; subst h1
    apply existSR_transitive; rotate_left 1
    · apply flush_lhs_exit
    · unfold lhsEvaled
      apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
      · (iterate 0 apply List.mem_cons_of_mem); constructor
      · dsimp [Module.connect'', Module.liftR, Module.liftL]
        and_intros <;> try (intro; contradiction)
        intro hwf; clear hwf
        apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        apply Exists.intro _
        dsimp
        and_intros <;> try rfl
      · apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        · (iterate 6 apply List.mem_cons_of_mem); constructor
        · dsimp [Module.connect'', Module.liftR, Module.liftL]
          and_intros <;> try (intro; contradiction)
          intro hwf; clear hwf
          apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
          apply Exists.intro _
          dsimp
          and_intros <;> try rfl
          exists false
        · rw [show f i = ((f i).1, false) by rw [←hm]]; apply existSR.done
  · subst h2; obtain ⟨-, it⟩ := it; obtain it := it rfl; subst h1
    apply existSR_transitive; rotate_left 1
    · apply flush_lhs_exit
    · unfold lhsEvaled
      apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
      · (iterate 0 apply List.mem_cons_of_mem); constructor
      · dsimp [Module.connect'', Module.liftR, Module.liftL]
        and_intros <;> try (intro; contradiction)
        intro hwf; clear hwf
        apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        apply Exists.intro _
        dsimp
        and_intros <;> try rfl
      · apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        · (iterate 6 apply List.mem_cons_of_mem); constructor
        · dsimp [Module.connect'', Module.liftR, Module.liftL]
          and_intros <;> try (intro; contradiction)
          intro hwf; clear hwf
          apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
          apply Exists.intro _
          dsimp
          and_intros <;> try rfl
          exists false
        · rw [show f i = ((f i).1, false) by rw [←hm]]; apply existSR.done

theorem flush_lhs_end {m i v muxF} :
  iterate f i (m + 1) v →
  existSR (lhsEvaled f).internals
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(apply f m i).1], muxF, [])
    ([v], [], ([false], true), [], ([], []), ([], []), ([], []), [], muxF, []) := by
  intro it
  apply existSR_transitive; rotate_left 1
  · apply flush_lhs_exit
  · unfold lhsEvaled
    apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
    · (iterate 0 apply List.mem_cons_of_mem); constructor
    · dsimp [Module.connect'', Module.liftR, Module.liftL]
      and_intros <;> try (intro; contradiction)
      intro hwf; clear hwf
      apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
      apply Exists.intro _
      dsimp
      and_intros <;> try rfl
    · apply existSR.step _ (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _) (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
      · (iterate 6 apply List.mem_cons_of_mem); constructor
      · dsimp [Module.connect'', Module.liftR, Module.liftL]
        and_intros <;> try (intro; contradiction)
        intro hwf; clear hwf
        apply Exists.intro (_, _, (_, _), _, (_, _), (_, _), (_, _), _, _, _)
        apply Exists.intro _
        dsimp
        and_intros <;> try rfl
        exists true
      · suffices h : (f (apply f m i).1) = (v, false) by rw [h]; apply existSR.done
        rw [← it.2.1]; rfl

theorem flush_lhs_loop_compl {m n i v muxF} :
  iterate f i n v →
  m < n →
  existSR (lhsEvaled f).internals
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [i], muxF, [])
    ([], [], ([true], true), [], ([], []), ([], []), ([], []), [(apply f m i).1], muxF, []) := by
  induction m with
  | zero => intros; apply existSR.done
  | succ m ihm =>
    intros
    apply existSR_transitive
    · apply ihm <;> grind
    · apply flush_lhs_loop <;> try assumption

theorem iterate_f_false {i n v} :
  iterate f i n v →
  (f i).2 = false →
  n = 1 ∧ v = (f i).1 := by
  intro hiterate hf
  unfold iterate at hiterate
  obtain ⟨hi1, hi2, hi3⟩ := hiterate
  by_cases h : n = 1
  · subst n; dsimp [apply] at hi2
    simp [*]
  · have hn : 1 < n := by omega
    specialize hi1 _ hn; dsimp [apply] at hi1
    grind

theorem apply_twice' {m n i} :
  n > 0 →
  apply f n (apply f m i).1 = apply f (n + m) i := by
  induction n generalizing m with
  | zero => intro h; contradiction
  | succ n ih =>
    intro h
    rw [show n + 1 + m = (n + m) + 1 by omega]
    dsimp [apply]
    by_cases hn : n = 0
    · subst n; dsimp [apply]; rw [show 0 + m = m by omega]
    · rw [ih]; omega

theorem apply_twice {m n i} :
  (apply f n (apply f m i).1).1 = (apply f (n + m) i).1 := by
  by_cases hn : n = 0
  · subst n; dsimp [apply]; rw [show 0 + m = m by omega]
  · rw [apply_twice']; omega

theorem iterate_apply {m n i v} :
  n > 0 →
  iterate f i (n + m) v →
  iterate f (apply f m i).1 n v := by
  unfold iterate
  intro hng ⟨hi1, hi2, hi3⟩; and_intros
  · intro m1 hm1
    by_cases hm1' : m1 = 0
    · subst m1; dsimp [apply]
    · rw [apply_twice']; apply hi1; omega; omega
  · rw [apply_twice']; assumption; omega
  · omega

theorem flush_lhs {i v n muxF init_s} :
  iterate f i n v →
  init_node_state init_s ->
  existSR (lhsEvaled f).internals
    ([], [], init_s, [], ([], []), ([], []), ([], []), [], i :: muxF, [])
    ([v], [], ([false], true), [], ([], []), ([], []), ([], []), [], muxF, []) := by
  intro hi hn
  by_cases hb : (f i).2
  · apply existSR_transitive
    · solve_by_elim [flush_lhs_init1]
    · rw [show (f i) = (apply f 1 i) by rfl]
      by_cases h : n = 2
      · subst n; solve_by_elim [flush_lhs_end]
      · by_cases H : n = 1
        · subst n; have hi' := hi.2.1
          dsimp [apply] at hi'; grind
        · have hn0 := hi.2.2
          have hn2 : 2 < n := by omega
          cases n <;> try contradiction
          rename_i n
          apply existSR_transitive
          · apply flush_lhs_loop_compl
            apply iterate_apply
            exact show n > 0 by omega
            assumption
            exact show n - 1 < n by omega
          · rw [apply_twice]; rw [show n - 1 + 1 = n by omega]
            solve_by_elim [flush_lhs_end]
  · simp only [Bool.not_eq_true] at hb
    obtain ⟨_, _⟩ := iterate_f_false f hi hb; subst_vars
    solve_by_elim [flush_lhs_init2]

inductive φ : rhsGhostType Data -> lhsType Data -> Prop where
| intro : ∀ (i :rhsGhostType Data) i_merge i_module i_branchD i_branchB i_tagT i_tagM i_tagD i_splitD i_splitB s_queue_out  s_queue
            (s : lhsType Data) s_initL s_initB s_module s_splitD s_splitB s_branchD s_branchB s_forkR s_forkL s_muxT s_muxF s_muxC,
  ⟨i_module, ⟨i_branchD, i_branchB⟩, i_merge, ⟨i_tagT, i_tagM, i_tagD ⟩, ⟨i_splitD, i_splitB⟩⟩ = i ->
  ⟨s_queue_out, s_queue, ⟨s_initL, s_initB⟩, s_module, ⟨s_splitD, s_splitB⟩, ⟨s_branchD, s_branchB⟩, ⟨s_forkR, s_forkL⟩, s_muxT, s_muxF, s_muxC ⟩ = s ->
  ((i_tagT.map Prod.snd) ++ (i_tagD.map Prod.fst)) = s_muxF ->
  state_relation f i ->
  lhs_is_empty s ->
  φ i s

theorem φ_empty : φ f default default_lhs := by
  constructor <;> try trivial
  · apply state_relation_empty
  · constructor <;> try trivial

instance : MatchInterface (rhsGhostEvaled f) (lhsEvaled f) := by
  unfold rhsGhostEvaled lhsEvaled
  solve_match_interface

set_option maxHeartbeats 0 in
theorem refine:
    rhsGhostEvaled f ⊑_{φ f} (lhsEvaled f) := by
  intro ⟨ x1, x2 ⟩ y HPerm
  apply Module.comp_refines.mk
  . intro ident ⟨x'1, x'2⟩ v Hcontains
    unfold rhsGhostEvaled at *
    dsimp at Hcontains v
    by_cases heq : { inst := InstIdent.top, name := "i_in" } = ident
    . unfold PortMap.getIO
      subst ident
      rw[PortMap.rw_rule_execution (getIO_cons_eq (α := (rhsGhostType Data)))] at Hcontains

    . unfold PortMap.getIO
      rw[PortMap.rw_rule_execution (getIO_cons_neq heq (α := (rhsGhostType Data)))] at Hcontains
      rw[PortMap.rw_rule_execution (getIO_nil (α := (rhsGhostType Data)) (b := ident))] at Hcontains
      contradiction
  . intro ident ⟨x'1, x'2⟩ v Hcontains
    unfold rhsGhostEvaled at *
    dsimp at Hcontains v
    by_cases heq : { inst := InstIdent.top, name := "o_out" } = ident
    . unfold PortMap.getIO
      subst ident
      rw[PortMap.rw_rule_execution (getIO_cons_eq (α := (rhsGhostType Data)))] at Hcontains
      unfold lhsEvaled
      dsimp
      simp at Hcontains
      repeat cases ‹_ ∧ _›
      subst_vars
      rename_i H _
      cases H; rename_i H
      repeat cases ‹_ ∧ _›
      obtain ⟨⟨i_branchD, i_branchB⟩, i_merge, ⟨i_tagT, i_tagM, i_tagD ⟩, ⟨i_splitD, i_splitB⟩⟩ := x2
      obtain ⟨⟨i_branchD', i_branchB'⟩, i_merge', ⟨i_tagT', i_tagM', i_tagD' ⟩, ⟨i_splitD', i_splitB'⟩⟩ := x'2
      rename_i h1 h2 h3 h4 h5 h6 h7
      simp at h7; simp at h6; simp at h5; simp at h4; simp at h3; simp at h2; simp at h1
      cases h5; rename_i tagv datav h5
      subst_vars
      cases HPerm
      rename_i h8 h2' h3 h4' h5 h6
      simp at h8; simp at h4'
      repeat cases ‹_ ∧ _›
      subst_vars
      cases h4'
      rename_i H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HHH _
      simp at H1
      repeat cases ‹_ ∧ _›
      subst_vars
      cases h1; rename_i n h1; cases h1; rename_i data h1; cases h1; rename_i tag h1
      have HH14 := H14
      specialize H14 tagv v n data
      rw[Batteries.AssocList.find?_eq] at H14
      simp at H14
      specialize H14 tag h1
      cases H14; rename_i H14 H14'
      cases H14
      . subst_vars
        cases h3; rename_i d1 ld h1 h2
        cases h1; rename_i k h3
        simp at h3
        have h4 := iterate_congr f _ _ _ _ _ h3 H14'
        let ⟨ h5, h6⟩ := h4
        subst_vars
        apply Exists.intro ⟨_, _, ⟨_, _⟩, _, ⟨_, _⟩ ,⟨_, _⟩, ⟨_, _⟩, _, _, _⟩;
        apply Exists.intro ⟨_, _, ⟨_, _⟩, _, ⟨_, _⟩ ,⟨_, _⟩, ⟨_, _⟩, _, _, _⟩;
        and_intros
        · apply existSR.done
        · dsimp
        . dsimp
        . constructor <;> (try rfl)
          . simp at h2; assumption
          . constructor <;> (try rfl) <;> (try assumption)
            . rename_i x_tagM _ _ _ _
              unfold AssocList.eraseAll; apply in_eraseAll_noDup tagv x_tagM
              assumption
            . clear h4; intro elem HH
              specialize H11 elem
              cases elem; rename_i tag_elem data_elem
              cases (decEq tagv tag_elem)
              . rw[List.map_append] at HH
                rw[List.mem_append] at HH
                cases HH <;> rename_i HH
                . rename_i x_merge x_module x_branchD x_branchB x_tagM x_tagD x_splitD x_splitB _
                  rw[List.map_append] at H11
                  rw[List.mem_append] at H11
                  specialize H11 (Or.inl HH)
                  simp at H11
                  cases H11 <;> rename_i H11
                  . cases H11
                    subst_vars
                    solve_by_elim
                  . assumption
                . rename_i x_merge x_module x_branchD x_branchB x_tagM x_tagD x_splitD x_splitB _
                  rw[List.map_append] at H11
                  rw[List.mem_append] at H11
                  rename_i x_tagM _ _ _ _ _
                  have HH := List.exists_of_mem_map HH
                  cases HH; rename_i HH
                  cases HH; rename_i HH _
                  have HH := List.exists_of_mem_map HH
                  cases HH; rename_i HH; cases HH; rename_i HH _
                  have HH := in_eraseAll_list _ HH
                  rename_i elem _ _
                  have HH' := List.mem_map_of_mem (f := (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))) HH
                  have HH'' := List.mem_map_of_mem (f := (fun x => match x with | ((x, snd), fst, y) => (x, y))) HH'
                  rename_i h3 _ h1 _  h2 _; clear h1 h2 h3
                  rename_i h; simp at h; subst_vars
                  rename_i h; simp at h
                  cases h ; rename_i h1 h2
                  subst_vars
                  specialize H11 (Or.inr HH'')
                  simp at H11
                  cases H11
                  . rename_i h
                    cases h
                    subst_vars
                    solve_by_elim
                  . assumption
              . subst_vars
                rw[List.map_append] at HH
                rw[List.mem_append] at HH
                cases HH <;> rename_i HH
                . rw[List.map_append] at H11
                  rw[List.mem_append] at H11
                  specialize H11 (Or.inl HH)
                  simp at H11
                  cases H11
                  . subst_vars
                    have h1' := h1
                    have h1 := List.find?_some h1
                    simp at h1
                    subst tag
                    rename_i x_tagM _ _ _ _
                    have h1' := List.mem_of_find?_eq_some  h1'
                    have HH := List.exists_of_mem_map HH
                    cases HH; rename_i HH; cases HH; rename_i HH _
                    rename_i hw; simp at hw; cases hw
                    rw[List.map_append ] at H10; rw[List.map_append ] at H10
                    rw[List.nodup_append] at H10
                    let ⟨_, _, H10 ⟩ := H10
                    -- rw[List.disjoint_right ] at H10
                    have h1' := List.mem_map_of_mem (f := (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))) h1'
                    have h1' := List.mem_map_of_mem (f := Prod.fst) h1'
                    have h1' := List.mem_map_of_mem (f := Prod.fst) h1'
                    -- specialize H10 h1'
                    have HH := List.mem_map_of_mem (f := Prod.fst) HH
                    have HH := List.mem_map_of_mem (f := Prod.fst) HH
                    rename_i w _ _ _ _ _ _ ; rw[w] at HH
                    specialize H10 _ HH _ h1'
                    simp only [ Function.comp_apply, Prod.exists] at H10
                    solve_by_elim
                  . assumption
                . have HH := List.exists_of_mem_map HH
                  cases HH; rename_i HH; cases HH; rename_i HH _
                  have HH := List.exists_of_mem_map HH
                  cases HH; rename_i HH; cases HH; rename_i HH _
                  rename_i h3 _ h1 _  _ _; clear h1 h3
                  rename_i h; simp at h; subst_vars
                  rename_i h; simp at h
                  cases h ; rename_i h1 h2
                  have HH := not_in_eraseAll_list _ HH h1
                  solve_by_elim
            . have H := List.Nodup.of_cons H12
              assumption
            . intro T D N I H1
              have HH1 := H1
              simp at H1
              cases H1; rename_i tag' H1
              cases (decEq T tagv)
              . rename_i x_tagM _ _ _ _
                subst_vars
                have h1' := List.find?_some h1
                simp at h1'
                have H1' := List.find?_some H1
                simp at H1'
                subst tag tag'
                have H1 := List.mem_of_find?_eq_some H1
                have H1 := in_eraseAll_list _ H1
                constructor
                . specialize HH14 T D N I
                  rename_i Hdif _ _
                  have Hh := find?_eraseAll_neg _ _ HH1 Hdif
                  specialize HH14 Hh
                  cases HH14
                  rename_i H _; simp at H
                  cases H
                  . repeat cases ‹_ ∧ _›
                    subst_vars
                    solve_by_elim
                  . assumption
                . specialize HH14 T D N I
                  rename_i Hdif _ _
                  have Hh := find?_eraseAll_neg _ _ HH1 Hdif
                  specialize HH14 Hh
                  cases HH14
                  assumption
              . subst_vars
                rename_i x_tagM _ _ _ _
                have H1' := @find?_eraseAll_list _ _ T _ x_tagM
                unfold AssocList.eraseAll at H1; rw[H1] at H1'
                simp at H1'
            . intro tag i hh1
              have hh := @List.mem_append_right _ (tag, i) [(tagv, data)] i_tagT'
              specialize hh hh1
              specialize HHH tag i hh
              assumption
          . cases h6
            rename_i H1 _
            simp at H1
            repeat cases ‹_ ∧ _›
            subst_vars
            constructor <;> (try rfl)
            constructor <;> assumption
      . simp at H12
        let ⟨ H12, H12' ⟩ := H12
        solve_by_elim
    . unfold PortMap.getIO
      rw[PortMap.rw_rule_execution (getIO_cons_neq heq (α := (rhsGhostType Data)))] at Hcontains
      rw[PortMap.rw_rule_execution (getIO_nil (α := (rhsGhostType Data)) (b := ident))] at Hcontains
      contradiction
  . cases HPerm
    rename_i h_state_relation _ _
    intro rule mid_i hr hrr
    constructor
    . constructor
      . constructor
      . have H := state_relation_preserve f (x1, x2) _ rule hr hrr h_state_relation
        have h := state_relation_preserve_input f (x1, x2) _ rule hr hrr h_state_relation
        constructor <;> ( try rfl)
        . simp at h
          rw[← h]; clear h
          subst_vars
          rename_i h1 _ hf; simp at h1
          cases h1; subst_vars
          simp
          assumption
        . assumption
        . assumption

#print axioms refine

end Proof
end Graphiti.LoopRewrite
