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

inductive state_relation : rhsGhostType Data -> Prop where
| intros : ∀ (s :  rhsGhostType Data) x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB x_split_branchT x_split_branchF x_moduleT x_moduleF,
  ⟨ x_module, ⟨x_branchD, x_branchB⟩, x_merge, ⟨x_tagT, x_tagM, x_tagD ⟩, ⟨x_splitD, x_splitB⟩⟩ = s ->
  ( ∀ elem, elem ∈ x_tagD ->  elem.1 = elem.2.2 ∧ elem.2.1 = 0) ->
  (∀ elem n i', elem ∈ x_merge -> iterate f elem.2.2 n i' -> elem.2.1 ≥ 0 ∧ elem.2.1 < n ∧ elem.1.2 = (apply f elem.2.1 elem.2.2).1) ->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (List.zip (x_branchD ++ x_splitD ) ( x_branchB ++ x_splitB))) = x_split_branchT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (List.zip (x_branchD ++ x_splitD ) (x_branchB ++ x_splitB ))) = x_split_branchF ->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (x_module)) = x_moduleT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (x_module)) = x_moduleF ->
  (∀ elem , elem ∈ x_split_branchT ++ x_moduleT -> ∃ n i', iterate f elem.2.2 n i' ∧
    elem.2.1 > 0 ∧ elem.2.1 < n ∧ elem.1.2 = (apply f elem.2.1 elem.2.2).1) ->
  (∀ elem, elem ∈ x_split_branchF ++ x_moduleF ->  iterate f elem.2.2 elem.2.1 elem.1.2) ->
  ((((x_merge ++ (x_module.map Prod.fst) ++ x_splitD ++ x_branchD ++ x_tagM.toList.map (λ x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))).map Prod.fst).map Prod.fst).Nodup) ->
  (∀ elem, elem ∈ ((x_merge ++ (x_module.map Prod.fst) ++ x_splitD ++ x_branchD ++ x_tagM.toList.map (λ x => ((x.1, x.2.1), x.2.2.1, x.2.2.2))).map (fun ((x, _), _, y) => (x, y)))-> elem ∈ x_tagT) ->
  ((x_tagT.map Prod.fst).Nodup) ->
  (x_branchD ++ x_splitD).length = (x_branchB ++ x_splitB).length ->
  ( ∀ tag d n i, x_tagM.find? tag = some (d, n, i) -> (tag, i ) ∈ x_tagT ∧ iterate f i n d) ->
  ( ∀ d, d ∈ x_tagD -> d.2 = (0, d.1)) ->
  ( ∀ tag i, (tag, i) ∈ x_tagT -> ∃ d n, iterate f i n d) ->
  ( ∀ e, e ∈ x_tagD -> ∃ d n, iterate f e.1 n d) ->
  -- ( ∀ tag i, (i) ∈ x_tagD -> ∃ d n, iterate f i n d) ->
  state_relation s




omit [Inhabited Data] in
@[simp]
theorem input_rule_isData {input_rule} :
  ((lhsEvaled f).inputs.find? ↑"i_in") = .some input_rule ->
  Data = input_rule.fst := by
  unfold lhsEvaled
  simp; intro h1
  subst_vars; rfl

inductive lhs_is_empty  : lhsType Data -> Prop where
| intro : ∀  (s :  lhsType Data) s_queue_out s_initL s_initB,
          ⟨s_queue_out, [], ⟨s_initL, s_initB⟩, [], ⟨[], []⟩ ,⟨[], []⟩, ⟨[], []⟩, [], [], [] ⟩ = s ->
          (s_initB = true -> s_initL = []) ∧ (s_initB = false ->  s_initL = [false]) ->
          lhs_is_empty s

axiom flushing_lhs' {s i s_queue_out s_initL s_initB} :
  ⟨s_queue_out, [], ⟨s_initL, s_initB⟩, [], ⟨[], []⟩ ,⟨[], []⟩, ⟨[], []⟩, [i], [], [] ⟩ = s ->
  (s_initB = true -> s_initL = []) ∧ (s_initB = false ->  s_initL = [false]) ->
  ∃ s'' n v, existSR (lhsEvaled f).internals s s''
    ∧ s'' = ⟨s_queue_out.concat v, [], ⟨[false], false⟩, [], ⟨[], []⟩ ,⟨[], []⟩, ⟨[], []⟩, [], [], [] ⟩
    ∧ iterate f i n v

axiom iterate_congr  (i i' a' : Data) (n : Nat) ( k : Nat) : iterate f i n i' -> iterate f i k a' -> n = k ∧ i' = a'


theorem flushing_lhs {n v} {s i s_queue_out s_initL s_initB} :
  ⟨s_queue_out, [], ⟨s_initL, s_initB⟩, [], ⟨[], []⟩ ,⟨[], []⟩, ⟨[], []⟩, [i], [], [] ⟩ = s ->
  (s_initB = true -> s_initL = []) ∧ (s_initB = false ->  s_initL = [false]) ->
  iterate f i n v ->
  ∃ s'', existSR (lhsEvaled f).internals s s''
    ∧ s'' = ⟨s_queue_out.concat v, [], ⟨[false], false⟩, [], ⟨[], []⟩ ,⟨[], []⟩, ⟨[], []⟩, [], [], [] ⟩
  := by
  intros
  have := flushing_lhs' (by assumption) (by assumption) (by assumption)
  have ⟨a, b, c, d, e, f⟩ := this
  rename_i iter; have := iterate_congr _ _ _ _ _ _ iter f; cases this; subst_vars
  apply Exists.intro; and_intros <;> trivial

theorem iterate_complete {s : lhsType Data} {i s_queue_out s_initL s_initB} :
  ⟨s_queue_out, [], ⟨s_initL, s_initB⟩, [], ⟨[], []⟩ ,⟨[], []⟩, ⟨[], []⟩, [i], [], [] ⟩ = s ->
  (s_initB = true -> s_initL = []) ∧ (s_initB = false ->  s_initL = [false]) ->
  ∃ v n, iterate f i n v := by
  intros; have := flushing_lhs' (by assumption) (by assumption) (by assumption)
  have ⟨a, b, c, d, e, f⟩ := this
  constructor; constructor; assumption

inductive φ: rhsGhostType Data -> lhsType Data -> Prop where
| intro : ∀ (i :rhsGhostType Data) i_merge i_module i_branchD i_branchB i_tagT i_tagM i_tagD i_splitD i_splitB i_out s_queue_out  s_queue
            (s : lhsType Data) s_initL s_initB s_module s_splitD s_splitB s_branchD s_branchB s_forkR s_forkL s_muxB s_muxI s_muxC,
    ⟨i_module, ⟨i_branchD, i_branchB⟩, i_merge, ⟨i_tagT, i_tagM, i_tagD ⟩, ⟨i_splitD, i_splitB⟩⟩ = i ->
    ⟨s_queue_out, s_queue, ⟨s_initL, s_initB⟩, s_module, ⟨s_splitD, s_splitB⟩ ,⟨s_branchD, s_branchB⟩, ⟨s_forkR, s_forkL⟩, s_muxB, s_muxI, s_muxC ⟩ = s ->
    ((i_tagT.map Prod.snd) ++ (i_tagD.map Prod.fst)) = i_out ->
    List.Forall₂ (fun (a : Data) (b : Data) => ∃ n, iterate f b n a) s_queue_out i_out ->
    state_relation f i ->
    lhs_is_empty s ->
    φ i s

instance : MatchInterface (rhsGhostEvaled f) (lhsEvaled f) := by
  unfold rhsGhostEvaled lhsEvaled
  solve_match_interface



/-
# Proof state_relation_prserve in rhsGhost
-/

theorem alpa {α : Type} {a : α} {l : List α} : a :: l = [a] ++ l := by simp only [List.singleton_append]

attribute [aesop unsafe 50% forward] List.Nodup.cons List.perm_append_singleton
attribute [aesop norm] List.perm_comm

axiom apply_plus_one (i: Data) (n : Nat) : (f (apply f n i).1).1 = (apply f (1 + n) i).1

axiom apply_plus_one_condiction (i: Data) (n : Nat) : (f (apply f n i).1).2 = (apply f (n +1) i).2

axiom apply_true (i i' : Data) (n : Nat) ( k : Nat) : k < n -> (apply f (k + 1) i).2 = true -> iterate f i n i' -> k + 1 < n

axiom apply_false (i i' : Data) (n : Nat) ( k : Nat) : k < n -> (apply f (k + 1) i).2 = false -> iterate f i n i' -> k + 1 = n


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
    simp_all only [Prod.mk.injEq]; repeat cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnewnew
    simp at h
    repeat cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . clear h9 h10 h12
      intro elem h1
      specializeAll elem
      constructor
      . rw[← List.singleton_append] at *
        aesop (add norm List.mem_append_right) (config := {useDefaultSimpSet := false})
      . rw[← List.singleton_append] at *
        aesop (add norm List.mem_append_right) (config := {useDefaultSimpSet := false})
    . clear h9 h10 h12 H13 H14 H15
      intro elem n i' h1 h2
      specializeAll elem
      specializeAll n
      specializeAll i'
      simp_all only [List.append_assoc, Prod.mk.eta, List.map_append, List.map_map, List.mem_cons,
        forall_eq_or_imp, Prod.forall, ge_iff_le, zero_le, true_and, forall_const]
      cases h1
      . subst_vars
        -- aesop
        rename_i left right
        unfold Graphiti.LoopRewrite.iterate at h2
        unfold Graphiti.LoopRewrite.iterate at Hnew
        unfold Graphiti.LoopRewrite.iterate at Hnewnew
        simp_all only [gt_iff_lt, true_and]
        obtain ⟨fst, snd⟩ := s
        obtain ⟨fst_1, snd_1⟩ := s'
        obtain ⟨fst_2, snd_2⟩ := elem
        obtain ⟨fst_3, snd⟩ := snd
        obtain ⟨fst_4, snd_1⟩ := snd_1
        obtain ⟨fst_2, snd_3⟩ := fst_2
        obtain ⟨fst_5, snd_2⟩ := snd_2
        obtain ⟨fst_3, snd_4⟩ := fst_3
        obtain ⟨fst_6, snd⟩ := snd
        obtain ⟨fst_4, snd_5⟩ := fst_4
        obtain ⟨fst_7, snd_1⟩ := snd_1
        obtain ⟨left_1, right_1⟩ := h2
        obtain ⟨left_2, right_2⟩ := h3
        obtain ⟨left_3, right_3⟩ := Hnewnew
        obtain ⟨fst_8, snd⟩ := snd
        obtain ⟨fst_9, snd_1⟩ := snd_1
        obtain ⟨left_4, right_1⟩ := right_1
        obtain ⟨left_2, right_4⟩ := left_2
        obtain ⟨w, h⟩ := left_3
        obtain ⟨fst_8, snd_6⟩ := fst_8
        obtain ⟨fst_10, snd⟩ := snd
        obtain ⟨fst_9, snd_7⟩ := fst_9
        obtain ⟨fst_11, snd_1⟩ := snd_1
        obtain ⟨w_1, h⟩ := h
        obtain ⟨fst_12, snd_6⟩ := snd_6
        obtain ⟨fst_13, snd_7⟩ := snd_7
        obtain ⟨left_3, right_5⟩ := h
        obtain ⟨left_5, right_5⟩ := right_5
        subst right_4
        rfl
      . -- aesop
        unfold Graphiti.LoopRewrite.iterate at Hnewnew
        unfold Graphiti.LoopRewrite.iterate at h2
        unfold Graphiti.LoopRewrite.iterate at Hnew
        simp_all only [gt_iff_lt, forall_const, and_self]
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
      . (repeat rw[List.map_append] at h11)
        ac_nf at *
    . rename_i h14 h15
      clear h10 h9 h4 h11 h14 h15
      intro elem h1
      specialize h12 elem
      by_cases elem = (newC.1.1, newC.2.2)
      . obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
        simp at h1
        simp_all
      . obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
        subst_vars
        simp at h1
        simp_all
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
      . simp_all
      . assumption
    . clear h10 h9 h4  H13 H14 h3 h11 h12
      intro d h1
      specialize H15 d
      simp at H15
      -- aesop
      unfold Graphiti.LoopRewrite.iterate at Hnew
      unfold Graphiti.LoopRewrite.iterate at Hnewnew
      simp_all only [gt_iff_lt, List.mem_cons, forall_eq_or_imp, Prod.forall, or_true, forall_const]
    . intro tag i h1
      rename_i x_tagT _ _ _ _ _
      rw[List.mem_append] at h1
      cases h1 <;> rename_i h1
      . specialize Hnew tag i h1; assumption
      . simp at h1; subst_vars
        obtain ⟨⟨newC11, newC12⟩, newC21, newC22⟩ := newC
        cases h1
        clear H14
        dsimp at Hnewnew
        specialize Hnewnew (i, newC21, newC22)
        specialize Hnewnew (by simp)
        dsimp at Hnewnew; assumption
    · intros; apply Hnewnew; simp [*]
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all; repeat cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew'
    simp at h
    repeat cases ‹_ ∧ _›
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
        simp at H
        rename_i x_merge _ _ w _
        have H1 := @List.mem_of_get? _ (x_merge) w newC
        simp at H1; have H := Eq.symm H
        specialize H1 H
        obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
        specialize h12  (newCT, newCDI)
        have H1' := @List.mem_map_of_mem _ _ x_merge ((newCT, newCD), newCN, newCDI) (fun x => match x with | ((x, _), _, y) => (x, y)) H1
        (repeat rw[List.map_append] at h12)
        have H1' := List.mem_append_left (List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) (List.map Prod.fst x_module) ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) x_splitD ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) x_branchD ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) x_tagM.toList)) H1'
        dsimp at H1'
        simp only [] at h12
        ac_nf at *
        specialize h12 H1'
        specialize Hnew newCT newCDI h12
        cases Hnew; rename_i i Hnew; cases Hnew; rename_i n Hnew
        specialize h4 ((newCT, newCD), newCN, newCDI) n i H1 Hnew
        simp at h4
        constructor; constructor; rotate_left
        . exact i
        . exact n
        subst_vars
        simp
        cases h4
        have HT := apply_true f newCDI i n newCN
        rename_i hh
        specialize HT hh
        --simp at HT
        constructor
        . have hf := apply_plus_one f newCDI newCN; rename_i H
          rw[← H] at hf; assumption
        . constructor
          . rename_i Hf _ _ H
            simp only[] at Hf
            rw[H] at Hf
            rw[apply_plus_one_condiction] at Hf
            specialize HT Hf Hnew; omega
          . assumption
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
        simp only [] at H1; simp only [beq_self_eq_true] at H1
        simp only [forall_const] at H1
        have H := @List.mem_map_of_mem (((TagT × Data) × ℕ × Data) × Bool) ((TagT × Data) × ℕ × Data) (List.filter (fun x => x.2 == false) ((x_branchD ++ x_splitD).zip (x_branchB ++ x_splitB))) ((elem, false)) Prod.fst H1
        simp only [] at H
        have H := List.mem_append_left (List.map Prod.fst (List.filter (fun x => x.2 == false) x_module)) H
        specialize h10 H; assumption
      . cases h <;> rename_i h
        . simp_all only [and_self, implies_true, ge_iff_le, zero_le, true_and, Prod.forall, List.append_assoc,
                         Prod.mk.eta, List.map_append, List.map_map, List.mem_append, List.mem_map, Prod.exists, Function.comp_apply,
                         exists_and_right, Bool.exists_bool, Prod.mk.injEq, exists_eq_right_right, exists_eq_right, List.length_append,
                         AssocList.find?_eq, Option.map_eq_some', forall_exists_index, beq_false, List.mem_filter, Bool.not_eq_eq_eq_not,
                         Bool.not_true, or_true, forall_const]
        . cases h;
          rename_i x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB _ _ _
          rename_i H _ _; cases H; rename_i H; cases H; rename_i H
          simp at H
          rename_i w _
          have H1 := @List.mem_of_get? _ (x_merge) w newC
          simp at H1; have H := Eq.symm H
          specialize H1 H
          obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
          specialize h12  (newCT, newCDI)
          have H1' := @List.mem_map_of_mem _ _ x_merge ((newCT, newCD), newCN, newCDI) (fun x => match x with | ((x, _), _, y) => (x, y)) H1
          (repeat rw[List.map_append] at h12)
          have H1' := List.mem_append_left (List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) (List.map Prod.fst x_module) ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) x_splitD ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) x_branchD ++ List.map (fun x => match x with | ((x, snd), fst, y) => (x, y)) (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) x_tagM.toList)) H1'
          dsimp at H1'
          simp only [] at h12
          ac_nf at *
          specialize h12 H1'
          specialize Hnew newCT newCDI h12
          cases Hnew; rename_i i Hnew; cases Hnew; rename_i n Hnew
          specialize h4 ((newCT, newCD), newCN, newCDI) n i H1 Hnew
          simp at h4
          subst_vars; simp
          cases h4
          have HH := apply_false f newCDI i n newCN
          rename_i h
          rename_i Hf _ _ H
          simp only[] at Hf
          rw[H] at Hf
          rw[apply_plus_one_condiction] at Hf
          specialize HH h Hf Hnew
          rw[← HH] at Hnew
          dsimp at h10
          unfold iterate; and_intros
          . intro k hh
            subst n
            cases Hnew; rename_i H _
            apply H
            omega
          . rw [H,apply_plus_one]
            have ho : 1 + newCN = newCN + 1 := by omega
            rw[ho]
            generalize apply f (newCN + 1) newCDI = y at *
            cases y; congr
          . omega
    . clear h9 h12 h13 h10 h4
      unfold liftF2
      unfold liftF
      simp_all
      rename_i H
      cases H; rename_i l H
      cases H; rename_i H1 H2
      subst x_merge'
      simp_all
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
        simp
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
      have HH := List.Nodup.perm h11 H
      rw[← List.singleton_append] at *
      (repeat rw[ ← List.append_assoc])
      rw[ ← List.append_assoc] at HH
      rw[ ← List.append_assoc] at HH
      rw[ ← List.append_assoc] at HH
      rw[ ← List.append_assoc] at HH
      assumption
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
      simp_all
      cases h1
      . constructor
        aesop ( add safe forward List.mem_of_mem_eraseIdx) (config := {useDefaultSimpSet := false})
      . rename_i h
        cases h
        . aesop (config := {useDefaultSimpSet := false})
        . rename_i h; cases h
          . constructor
            constructor; rotate_left
            . exact newCT
            . constructor; rotate_left
              . exact newCD
              . constructor; rotate_left
                . exact newCN
                . aesop
          . aesop (config := {useDefaultSimpSet := false})
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all; repeat cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    simp at h
    repeat cases ‹_ ∧ _›
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
      simp_all
      (repeat rw[← List.append_assoc])
      rw[List.nodup_middle] at h11
      rename_i x_branch _ _ _ _ _ x_split _
      rw[List.nodup_middle]
      ac_nf at *
    . clear h9 h10 h4 h11 h13 h3 H13 Hnew H15
      intro elem h1
      specialize h12 elem
      aesop
    . clear h3 h4 h13 h11 h12 h9 h10
      (repeat rw [← List.append_assoc ])
      (repeat rw [List.length_append])
      (repeat rw [List.length_append] at H13)
      rw[H13]
      simp
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
    dsimp at h
    simp_all; repeat cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    simp at h
    repeat cases ‹_ ∧ _›
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
      --have H : List.map Prod.fst [newC] = [newC.1] := by simp
      --rw[H] at h11
      simp_all
      (repeat rw[← List.append_assoc])
      (repeat rw[← List.append_assoc] at h11)
      rename_i x_merge x_module _ _ _ _ _ _
      rw[@List.nodup_middle _  _ (List.map (Prod.fst ∘ Prod.fst) x_merge ++ List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module)] at h11
      rw[List.nodup_middle]
      ac_nf at *
    . clear h9 h10 h4 h11 h13 h3 H13
      intro elem h1
      specialize h12 elem
      aesop
    . clear h3 h4 h13 h11 h12 h9 h10
      (repeat rw [← List.append_assoc ])
      (repeat rw [List.length_append])
      rw[← List.singleton_append ] at H13
      (repeat rw [List.length_append] at H13)
      rw[← H13]
      ac_nf at *
  . replace h2 := h2.1 rfl
    simp only [List.concat_eq_append] at *
    obtain ⟨cons, newC, h⟩ := h2
    . obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
      dsimp at h
      simp_all; repeat cases ‹_ ∧ _›
      subst_vars
      cases h3
      rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
      simp at h
      repeat cases ‹_ ∧ _›
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
    simp_all; repeat cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    simp at h
    repeat cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . clear h10 h12 H13 h13
      intro elem n i' h1 h2
      specialize h4 elem n i'
      specialize h9 elem
      cases h1
      . simp_all
        cases h9; rename_i n' h9
        cases h9; rename_i h9
        repeat cases ‹_ ∧ _›
        constructor
        . rename_i H _ _ _ _ _ _; cases H; rename_i H
          unfold iterate at H
          cases H; rename_i h _ _ Hf _ _ H _
          by_cases hn : n < n'
          . specialize H n hn
            generalize hh : apply f n newC.2.2 = y at *
            cases y
            simp at H; subst_vars; simp at Hf
          . omega
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
      simp
      (repeat rw [← List.append_assoc])
      have h := @List.perm_middle _ newC.1.1 (List.map (Prod.fst ∘ Prod.fst) x_merge ++ List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module ++ List.map (Prod.fst ∘ Prod.fst) x_splitD ) (List.map (Prod.fst ∘ Prod.fst) x_branchD' ++ List.map (Prod.fst ∘ Prod.fst ∘ fun x => ((x.1, x.2.1), x.2.2)) x_tagM.toList)
      ac_nf at *
    . clear h9 h10 h4 h11 h13 h3 H13 Hnew
      intro elem h1
      specialize h12 elem
      aesop
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
    simp_all; repeat cases ‹_ ∧ _›
    subst_vars
    cases h3
    rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15 Hnew Hnew2
    simp at h
    repeat cases ‹_ ∧ _›
    subst_vars
    constructor <;> (try rfl) <;> (try assumption)
    . intro elem
      specialize h10 elem
      rename_i X Y _ _
      rw[← List.singleton_append ] at h10
      rw[← @List.singleton_append _ false] at h10
      have Hm := @List.zip_append _ _ [newC] (x_branchD' ++ X) [false] (x_branchB' ++ Y)
      specialize Hm ( by simp)
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
      simp_all only [AssocList.find?_eq, Option.map_eq_some_iff, Prod.exists, exists_eq_right, gt_iff_lt,
        forall_exists_index, Prod.forall, Prod.mk.injEq, List.append_assoc, Prod.mk.eta, Batteries.AssocList.toList,
        List.map_cons, List.map_append, List.map_map, List.mem_append, List.mem_map, Function.comp_apply,
        exists_and_right, Bool.exists_bool, List.mem_cons, List.cons_append]
      obtain ⟨fst, snd⟩ := s
      obtain ⟨fst_1, snd_1⟩ := s'
      obtain ⟨fst_2, snd_2⟩ := newC
      obtain ⟨fst_3, snd_3⟩ := elem
      obtain ⟨fst_4, snd⟩ := snd
      obtain ⟨fst_5, snd_1⟩ := snd_1
      obtain ⟨fst_2, snd_4⟩ := fst_2
      obtain ⟨fst_6, snd_2⟩ := snd_2
      obtain ⟨fst_4, snd_5⟩ := fst_4
      obtain ⟨fst_7, snd⟩ := snd
      obtain ⟨fst_5, snd_6⟩ := fst_5
      obtain ⟨fst_8, snd_1⟩ := snd_1
      obtain ⟨w, h⟩ := left
      obtain ⟨fst_9, snd⟩ := snd
      obtain ⟨fst_10, snd_1⟩ := snd_1
      obtain ⟨fst_9, snd_7⟩ := fst_9
      obtain ⟨fst_11, snd⟩ := snd
      obtain ⟨fst_10, snd_8⟩ := fst_10
      obtain ⟨fst_12, snd_1⟩ := snd_1
      obtain ⟨fst_13, snd_7⟩ := snd_7
      obtain ⟨fst_14, snd_8⟩ := snd_8
      simp_all only [Prod.mk.injEq, exists_eq_right_right, exists_and_right, exists_eq_right]
      cases h1 with
      | inl h_1 => simp_all only [true_or, forall_const]
      | inr h_2 =>
        cases h_2 with
        | inl h_1 => simp_all only [true_or, or_true, forall_const]
        | inr h_3 =>
          cases h_3 with
          | inl h_1 => simp_all only [true_or, or_true, forall_const]
          | inr h_2 =>
            cases h_2 with
            | inl h_1 => simp_all only [true_or, or_true, forall_const]
            | inr h_3 =>
              cases h_3 with
              | inl h_1 => simp_all only [and_self, true_or, or_true, forall_const]
              | inr h_2 => simp_all only [or_true, forall_const]
    . dsimp at H13
      omega
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
        simp at H
        repeat cases ‹_ ∧ _›
        subst_vars
        rename_i H _ _ ; cases H; rename_i i'' H
        constructor
        · have inright : ∀ {A} (l1 l2 : List A) (a : A), a ∈ l2 → a ∈ l1 ++ l2 := by intros; simp [List.mem_append_left, *]
          specialize h12 (newC.1.1, newC.2.2) (by (repeat rw[List.map_append]); dsimp; ac_nf; apply inright; apply inright; apply inright; simp)
          obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
          rename_i h; cases h
          assumption
        · specialize h10 newC
            (by (repeat rw[List.map_append]); skip; simp [List.zip, List.filter, List.map])
          obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
          dsimp at *
          rename_i h; cases h
          assumption


/-
# Proof refinment rhsGhost ⊑ lhs
-/

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
      -- unfold lhsEvaled
      dsimp
      cases HPerm
      subst_vars
      have HH := @flushing_lhs Data f _
      rename_i H_lhs _
      cases H_lhs
      rename_i He _
      cases He
      have : ∃ i n, iterate f v n i :=
        iterate_complete (s := (‹List Data›, [], (‹List Bool›, ‹Bool›), [], ([], []), ([], []), ([], []), [v], [], [])) f rfl (by assumption)
      have this' := this
      obtain ⟨i_v, n_v, Hiter_v ⟩ := this
      rename List Data => s_queue_out_d
      rename Bool => s_initB
      rename List Bool => s_initL
      rename _ ∧ _ => init_P
      obtain HH := HH (s := (s_queue_out_d, [], (s_initL, s_initB), [], ([], []), ([], []), ([], []), [v], [], [])) rfl (by assumption) (by assumption)
      obtain ⟨ s'', HH, HEQ ⟩ := HH
      cases HEQ
      apply Exists.intro ⟨_, _, ⟨_, _⟩, _, ⟨_, _⟩ ,⟨_, _⟩, ⟨_, _⟩, _, _, _⟩ ; constructor; constructor
      . unfold lhsEvaled; rw[PortMap.rw_rule_execution (by rw[find?_cons_eq])]
        dsimp; constructor; and_intros <;> (try rfl)
        rfl
      . and_intros
        . apply HH
        . dsimp
          constructor <;> (try rfl) <;> try dsimp; rotate_right 2
          . rename_i h _ _ _ _
            cases h
            subst_vars
            rename_i H1 H2 H3 H4 H5 H6 H7 H8 H9
            cases H9
            rename_i H _ _ _ _ _ _ _ _ _ _ _ _ _ _; simp at H
            repeat cases ‹_ ∧ _›
            subst_vars
            rename_i hh1 hh2 hh3 hh4 hh5 hh6
            simp at hh1; simp at hh2; simp at hh3; simp at hh4; simp at hh5; simp at hh6
            rw[hh6]
            rw[List.concat_eq_append]
            rw[List.map_append]
            rw[← List.append_assoc]
            rw[← @List.unzip_fst _ _ [(v, 0, v)]]
            simp
            rw[← List.append_assoc]
            rw[forall₂_cons_reverse]
            constructor
            . constructor; rotate_left
              . exact n_v
              . unfold iterate
                constructor
                . assumption
                . constructor
                  . assumption
                  . solve_by_elim
            . rw[hh5]
              assumption
          . rename_i h _ _ _
            cases h
            rename_i H1 H2 H3 H4 H5 H6 H7 H8 _ _ _ _ _ _ _ HH _
            cases H1
            repeat cases ‹_ ∧ _›
            subst_vars
            rename_i hh1 hh2 hh3 hh4 hh5 hh6
            simp at hh1; simp at hh2; simp at hh3; simp at hh4; simp at hh5; simp at hh6
            constructor <;> (try rfl) <;> dsimp
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              intro elem h1
              simp at hh6; rw[hh6] at h1
              rw[List.mem_append] at h1
              cases h1 <;> rename_i h1
              . simp at h1
                rename_i Hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                specialize H2 elem h1; assumption
              . simp only [List.mem_singleton] at h1
                aesop(config := {useDefaultSimpSet := false})
            . rename_i H _ _ _ _ _ _ _ _ _ _ _ _ _ _; -- simp at H
              repeat cases ‹_ ∧ _›
              subst_vars
              assumption
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              dsimp
              assumption
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              dsimp
              assumption
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              dsimp
              assumption
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              dsimp
              assumption
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              dsimp
              assumption
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              dsimp
              assumption
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              dsimp
              assumption
            . let ⟨ branch, _, _, split⟩ := x'2
              let ⟨ _, _ ⟩ := split
              let ⟨ _, _ ⟩ := branch
              simp at hh3; simp at hh1
              repeat cases ‹_ ∧ _›
              subst_vars
              dsimp
              intro elem h1
              simp at hh6; rw[hh6] at h1
              rw[List.mem_append] at h1
              cases h1 <;> rename_i h1
              . simp at h1
                rename_i Hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                specialize Hh elem h1; assumption
              . simp only [List.mem_singleton] at h1
                aesop(config := {useDefaultSimpSet := false})
            . intro tag i h1
              rw[hh5] at h1
              specialize HH tag i h1
              assumption
            · rw[hh6]; intro eleme hlist
              rw [List.mem_append] at hlist
              cases hlist
              · solve_by_elim
              · rename_i hlist
                simp at hlist
                cases hlist
                assumption
          . constructor <;> (try rfl)
            . simp
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
