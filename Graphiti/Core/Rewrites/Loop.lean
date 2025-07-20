import Graphiti.Core.Rewrites.LoopRewrite
import Graphiti.Core.ExprLowLemmas
import Graphiti.Core.Rewrites.LoopRewriteCorrect
import Mathlib
import Aesop

--import Graphiti.Core.Rewrites.MatchGoal

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



def apply (n : Nat) (i : Data) : Data × Bool :=
match n with
| 0 => f i
| n' + 1 => f (apply n' i).fst

def iterate (i: Data) (n : Nat) (i': Data) : Prop :=
  (∀ m, m < n -> (apply f m i).snd = true) ∧ apply f n i = (i', false)


-- theorem compute_n (i : Data) :
--   ∃ n i', iterate f i n i' = true := by
-- constructor; constructor
-- . unfold iterate
--   simp
--   and_intros
--   . intro m h1
--     unfold apply;

omit [Inhabited Data] in
@[simp]
theorem input_rule_isData {input_rule} :
  ((lhsEvaled f).inputs.find? ↑"i_in") = .some input_rule ->
  Data = input_rule.fst := by
  unfold lhsEvaled
  simp; intro h1
  subst_vars; rfl

#check lhsEvaled


-- theorem flushing (n : Nat) input_rule s i i' s' s_int
--   (h : ((lhsEvaled f).inputs.find? ↑"i_in") = .some input_rule) :
--   input_rule.snd s i s' ->
--   check_output f n (input_rule_isData f h i) i' ->
--   existSR (lhsEvaled f).internals s' s_int ->
--   ∃ s'', existSR (lhsEvaled f).internals s_int s'' ∧ s''.1 = i' := by admit

--Invariant flush



inductive flush_relation : lhsType Data -> Prop where
| intros : ∀ (s : lhsType Data) x_bag x_initL x_initB x_module x_splitD x_splitB x_branchD1 x_branchB x_forkR x_forkL x_muxB x_muxI x_muxC  x_branchD,
  ⟨x_bag, ⟨x_initL, x_initB⟩, x_module, ⟨x_splitD, x_splitB⟩ ,⟨x_branchD1, x_branchB⟩, ⟨x_forkR, x_forkL⟩, x_muxB, x_muxI, x_muxC ⟩ = s ->
  List.map Prod.fst (List.filter (fun x => x.2 == some true) (List.zip x_branchD1 x_branchB)) = x_branchD ->
  (x_module.map Prod.fst ++ x_splitD ++ x_branchD ++ x_muxB = []
    ∨
    ∃ elem, x_module.map Prod.fst ++ x_splitD ++ x_branchD ++ x_muxB = [elem]) ->
  (x_initB = false -> x_splitB ++ x_forkL ++ x_initL ++ x_muxC ++ x_module.map Prod.snd = []) ->
  (x_initB = true -> ∃ elem, x_splitB ++ x_forkL ++ x_initL ++ x_muxC ++ x_module.map Prod.snd = [elem]) ->
  flush_relation s


inductive computation_relation : (lhsType Data) -> (Data) -> Prop where
| intros : ∀ (s : lhsType Data) x_bag x_initL x_initB x_module x_splitD x_splitB x_branchD x_branchB x_forkR x_forkL x_muxB x_muxI x_muxC  (i_in : Data),
  ⟨x_bag, ⟨x_initL, x_initB⟩, x_module, ⟨x_splitD, x_splitB⟩ ,⟨x_branchD, x_branchB⟩, ⟨x_forkR, x_forkL⟩, x_muxB, x_muxI, x_muxC ⟩ = s ->
  (∃ elem, x_branchD = [elem] -> x_splitB ++ x_forkL ++ x_initL ++ x_muxC ++ x_module.map Prod.snd = [true]) ->
  ( ∀ n k i',
    iterate f i_in n i' ->
    k ≤ n ->
    (k < n -> x_module = [(apply f k i_in )] ∧ x_module.map Prod.snd = [true]) ->
    (k = n -> x_module = [(apply f n i_in )] ∧ x_module.map Prod.snd = [false]) ->
    (x_splitB = [true] -> k < n ∧  x_splitD = [(apply f k i_in )].map Prod.fst) ->
    (x_splitB = [false] -> k = n ∧  x_splitD = [(apply f k i_in )].map Prod.fst)) ->
  computation_relation s i_in

inductive state_relation : lhsType Data -> Data -> Prop where
| base: ∀ (s : lhsType Data) i_in,
  flush_relation s ->
  computation_relation f s i_in ->
  state_relation s i_in


#print lhsEvaled


@[aesop unsafe 90% forward]
theorem one_element {α : Type _ } (l1 l2 l3 l4 l5 : List α) ( a : α) :
  l1 ++ (l2 ++ ([a] ++ (l3 ++ (l4 ++ l5)))) = [a] -> l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ l5 = [] := by
--aesop (add norm [List.append_right_eq_self, List.append_left_eq_self ])
admit

@[aesop unsafe 90% forward]
theorem one_element2 {α : Type _ } (l1 l2 l3 l4 l5 : List α) ( a : α) :
  l1 ++ ([a] ++ (l2 ++ (l3 ++ (l4 ++ l5)))) = [a] -> l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] ∧ l5 = [] := by
--aesop (add norm [List.append_right_eq_self, List.append_left_eq_self ])
admit

@[aesop unsafe 10% forward]
theorem one_element1 {α : Type _ } (l1 l2 l3 l4 : List α) ( a : α) :
  l1 ++ ([a] ++ (l2 ++ (l3 ++ l4))) = [a] -> l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] := by
--aesop (add norm [List.append_right_eq_self, List.append_left_eq_self ])
admit

@[aesop unsafe 10% forward]
theorem one_element3 {α : Type _ } (l1 l2 l3 l4 : List α) ( a : α) :
  l1 ++ (l2 ++ (l3 ++ (l4 ++ [a]))) = [a] -> l1 = [] ∧ l2 = [] ∧ l3 = [] ∧ l4 = [] := by
--aesop (add norm [List.append_right_eq_self, List.append_left_eq_self ])
admit

@[aesop unsafe 5% forward]
theorem one_element4 {α : Type _ } (l1 l2 l3: List α) ( a : α) :
  l1 ++ (l2 ++ (l3 ++ [a])) = [a] -> l1 = [] ∧ l2 = [] ∧ l3 = []:= by
--aesop (add norm [List.append_right_eq_self, List.append_left_eq_self ])
admit

-- @[aesop safe apply]
-- theorem one_element_different {α : Type _ } (i : Nat) (l1 l2 l3 l4 : List α) (a b : α):
--   List.insertIdx i a (l1 ++ l2 ++ l3 ++ l4) = [b] -> (a = b) := by admit


@[aesop unsafe 90% forward]
theorem one_element_different {α : Type _ } (l1 l2 l3 l4 l5 : List α) (a b : α):
  l1 ++ (l2 ++ ([a] ++ (l3 ++ (l4 ++ l5)))) = [b] -> (a = b) := by admit


@[aesop  unsafe 90% forward]
theorem one_element_different2 {α : Type _ } (l1 l2 l3 l4 l5 : List α) (a b : α):
  l1 ++ ([a] ++ (l2 ++ (l3 ++ (l4 ++ l5)))) = [b] -> (a = b) := by admit

@[aesop unsafe 50% forward]
theorem one_element_different1 {α : Type _ } (l1 l2 l3 l4: List α) (a b : α):
  l1 ++ ([a] ++ (l2 ++ (l3 ++ l4))) = [b] -> (a = b) := by admit

@[aesop unsafe 50% forward]
theorem one_element_different3 {α : Type _ } (l1 l2 l3 l4: List α) (a b : α):
  l1 ++ (l2 ++ (l3 ++ (l4 ++ [a]))) = [b] -> (a = b) := by admit

@[aesop unsafe 10% forward]
theorem one_element_different4 {α : Type _ } (l1 l2 l3: List α) (a b : α):
  l1 ++ (l2 ++ (l3 ++ [a])) = [b] -> (a = b) := by admit

theorem List.of_mem_zip_neg {α : Type _}  {β : Type _}  {a : α}  {b : β}  {l₁ : List α} {l₂ : List β} :
(a, b) ∉ l₁.zip l₂ → a ∉ l₁ ∧ b ∉ l₂ := by admit

theorem inclusion { α : Type } {a y : α} {l : List α} (h₁ : a ∉ l) (h₂ : a ∈ l ++ [y]) : a = y :=
  by admit --  mem_of_ne_of_mem

set_option maxHeartbeats 1000000

--add_aesop_rules simp [List.append_cons]

-- attribute [-simp] List.singleton_append
-- attribute [-simp] List.append_cons

theorem only_one_data_in_flight:
  ∀ (s s' : lhsType Data) i_in rule,
    rule ∈ (lhsEvaled f).internals ->
    rule s s' ->
    state_relation f s i_in ->
    state_relation f s' i_in := by
  intro s s' i_in rule h1 h2 h3
  let ⟨x_bag, ⟨x_initL, x_initB⟩, x_module, ⟨x_splitD, x_splitB⟩ ,⟨x_branchD, x_branchB⟩, ⟨x_forkR, x_forkL⟩, x_muxB, x_muxI, x_muxC ⟩ := s
  let ⟨x_bag', ⟨x_initL', x_initB'⟩, x_module', ⟨x_splitD', x_splitB'⟩ ,⟨x_branchD', x_branchB'⟩, ⟨x_forkR', x_forkL'⟩, x_muxB', x_muxI', x_muxC'⟩ := s'
  fin_cases h1
  . dsimp at h2
    obtain ⟨h2, _⟩ := h2
    specialize h2 rfl
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨x_bag'_int, ⟨x_initL'_int, x_initB'_int⟩, x_module'_int, ⟨x_splitD'_int, x_splitB'_int⟩ ,⟨x_branchD'_int, x_branchB'_int⟩, ⟨x_forkR'_int, x_forkL'_int⟩, x_muxB'_int, x_muxI'_int, x_muxC'_int⟩ := cons
    dsimp at h
    simp_all; repeat cases ‹_ ∧ _›
    --let ⟨⟨⟨h4, ⟨h15, ⟨⟨h20, h26⟩, ⟨h21, h27⟩, ⟨h22, h28⟩, h23, h24, h25⟩⟩⟩, h5⟩ , ⟨⟨⟨⟨⟨⟨ h6, h13, h14⟩, ⟨h12, h17⟩⟩, ⟨h11, h16⟩⟩, ⟨h10, h18⟩⟩, h8⟩, ⟨h9, h19⟩⟩, h7⟩ := h
    subst_vars
    rcases h3 with ⟨ h3, h3'⟩
  --   constructor
  --   . cases h3
  --     rename_i h3 _ _
  --     constructor
  --     . rfl
  --     . simp_all; rfl
  --     . cases h3 <;> simp_all
  --     . cases h3
  --       . cases x_initB <;> simp_all
  --       . cases x_initB <;> simp_all
  --     . cases x_initB <;> simp_all
  --       . repeat cases ‹_ ∧ _›; subst_vars
  --         rename_i H3
  --         cases H3 <;> rename_i H3
  --         . simp_all; apply Or.inl
  --           cases newC
  --           . rw[List.append_cons] at *; ac_nf at *;
  --             aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --           . rw[List.append_cons] at *; ac_nf at *
  --             aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . simp_all; apply Or.inr
  --           cases newC
  --           . rw[List.append_cons] at *; ac_nf at *
  --             aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --           . rw[List.append_cons] at *; ac_nf at *
  --             aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --   . cases h3'; constructor <;> try rfl
  --     . rename_i H1 H2 _
  --       simp at H1
  --       repeat cases ‹_ ∧ _›
  --       subst_vars
  --       cases H2; rename_i elem H2
  --       apply Exists.intro elem
  --       intro h; specialize H2 h
  --       rename_i B _ _ _ _ _ _ _ _ _ _ _ _
  --       cases B
  --       . rename_i H1; simp at H1
  --         repeat cases  ‹_ ∧ _›
  --         subst_vars
  --         cases h3
  --         rename_i h3 _ _ _ _
  --         simp at h3
  --         repeat cases  ‹_ ∧ _›
  --         subst_vars
  --         simp_all only [List.map_cons, List.map_nil, List.append_assoc, List.cons_ne_self,
  --           imp_false, not_true_eq_false]
  --       . rename_i H1; simp at H1
  --         repeat cases  ‹_ ∧ _›
  --         subst_vars
  --         cases h3
  --         rename_i h3 _ _ _ _
  --         simp at h3
  --         repeat cases  ‹_ ∧ _›
  --         subst_vars
  --         cases newC
  --         . rename_i h1 h2 h3 h4; clear h1
  --           rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . rename_i h1 h2 h3 h4; clear h1
  --           rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --     . rename_i H1 _ _
  --       simp at H1
  --       repeat cases  ‹_ ∧ _›
  --       subst_vars
  --       assumption
  -- . dsimp at h2
  --   obtain ⟨h2, _⟩ := h2
  --   specialize h2 rfl
  --   obtain ⟨cons, newC, h⟩ := h2
  --   obtain ⟨x_bag'_int, ⟨x_initL'_int, x_initB'_int⟩, x_module'_int, ⟨x_splitD'_int, x_splitB'_int⟩ ,⟨x_branchD'_int, x_branchB'_int⟩, ⟨x_forkR'_int, x_forkL'_int⟩, x_muxB'_int, x_muxI'_int, x_muxC'_int⟩ := cons
  --   dsimp at h
  --   repeat cases ‹_ ∧ _›
  --   subst_vars
  --   rcases h3 with ⟨ h3, h3'⟩
  --   unfold lhsType at *
  --   constructor
  --   . cases h3
  --     rename_i h3 _ _
  --     constructor <;> try rfl
  --     . cases h3
  --       . simp_all
  --       . repeat cases  ‹_ ∧ _›
  --         subst_vars
  --         simp_all
  --     . cases h3
  --       . simp_all
  --       . simp_all
  --     . simp_all
  --       repeat cases ‹_ ∧ _›
  --       subst_vars
  --       rename_i H3
  --       cases H3 <;> rename_i H3
  --       . apply Or.inl
  --         cases newC
  --         . rw[List.append_cons] at *; ac_nf at *; clear h3 h3'
  --           aesop (config := {useDefaultSimpSet := false}) --(erase  one_element1)
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --       . apply Or.inr
  --         cases newC
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . rw[List.append_cons] at *; ac_nf at *; clear ‹_ ∨  _›
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false}) --(erase  one_element1)
  --   . cases h3'; constructor <;> try rfl
  --     . simp_all;  rename_i H1 H2 _
  --       repeat cases ‹_ ∧ _›
  --       subst_vars
  --       cases H2; rename_i elem H2
  --       apply Exists.intro elem
  --       intro h; specialize H2 h
  --       rename_i B _ _ _ _ _ _ _ _ _ _ _
  --       cases B
  --       . cases h3
  --         rename_i h3 _ _ _ _
  --         simp at h3
  --         repeat cases ‹_ ∧ _›
  --         subst_vars; simp_all
  --         cases newC
  --         . rename_i h1 h2 h3 ; clear h1
  --           rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . rename_i h1 h2 h3 ; clear h1
  --           rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --       . cases h3
  --         rename_i h3 _ _ _ _
  --         simp at h3
  --         repeat cases ‹_ ∧ _›
  --         subst_vars; simp_all
  --         cases newC
  --         . rename_i h1 h2 h3 ; clear h1
  --           repeat rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . rename_i h1 h2 h3 ; clear h1
  --           repeat rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --     . rename_i H1 _ _
  --       simp at H1
  --       repeat cases  ‹_ ∧ _›
  --       subst_vars
  --       simp_all
  --       assumption
  . admit
  . admit
  . dsimp at h2
    obtain ⟨h2, _⟩ := h2
    specialize h2 rfl
    obtain ⟨cons, newC, h⟩ := h2
    obtain ⟨x_bag'_int, ⟨x_initL'_int, x_initB'_int⟩, x_module'_int, ⟨x_splitD'_int, x_splitB'_int⟩ ,⟨x_branchD'_int, x_branchB'_int⟩, ⟨x_forkR'_int, x_forkL'_int⟩, x_muxB'_int, x_muxI'_int, x_muxC'_int⟩ := cons
    dsimp at h
    repeat cases ‹_ ∧ _›
    subst_vars
    rcases h3 with ⟨ h3, h3'⟩
    unfold lhsType at *
    constructor
    . cases h3
      rename_i h3 _ _
      constructor <;> try rfl
      . cases h3
        . simp_all
          repeat cases ‹_ ∧ _›
          subst_vars
          cases newC
          . constructor
            intro a b H
            rename_i H1 _
            specialize H1 a b
            cases b
            . simp_all
            . simp_all; rename_i b
              cases b
              . simp_all
              . simp_all
                apply List.of_mem_zip_neg at H1
                cases H1; rename_i H1
                apply List.mem_zip at H
                cases H; rename_i H
                rw[List.mem_append] at H
                simp at H1
            admit
          . admit
        . repeat cases  ‹_ ∧ _›
          subst_vars
          simp_all
      . cases h3
        . simp_all
        . simp at *
          repeat cases  ‹_ ∧ _›
          subst_vars; clear h3'
          simp_all
      . simp_all
    . cases h3'; constructor <;> try rfl
      . simp_all
      . rename_i H1 _ _
        simp at H1
        repeat cases  ‹_ ∧ _›
        subst_vars
        simp_all only [AssocList.find?_eq, Batteries.AssocList.toList, beq_self_eq_true,
          List.find?_cons_of_pos, Option.map_some', Option.some.injEq, not_true_eq_false,
          implies_true, Prod.mk.injEq, List.append_assoc, List.map_cons, List.map_nil, and_self]
        assumption
  -- . dsimp at h2
  --   obtain ⟨h2, _⟩ := h2
  --   specialize h2 rfl
  --   obtain ⟨cons, newC, h⟩ := h2
  --   obtain ⟨x_bag'_int, ⟨x_initL'_int, x_initB'_int⟩, x_module'_int, ⟨x_splitD'_int, x_splitB'_int⟩ ,⟨x_branchD'_int, x_branchB'_int⟩, ⟨x_forkR'_int, x_forkL'_int⟩, x_muxB'_int, x_muxI'_int, x_muxC'_int⟩ := cons
  --   simp at h
  --   repeat cases ‹_ ∧ _›
  --   subst_vars
  --   rcases h3 with ⟨ h3, h3'⟩
  --   unfold lhsType at *
  --   constructor
  --   . cases h3
  --     rename_i h3 _ _
  --     constructor <;> try rfl
  --     . cases h3
  --       . simp_all
  --       . simp_all
  --     . cases h3
  --       . simp_all
  --       . simp_all
  --     . simp at *
  --       repeat cases ‹_ ∧ _›
  --       subst_vars
  --       rename_i H3
  --       simp_all
  --       cases H3 <;> rename_i H3
  --       . apply Or.inl
  --         obtain ⟨ newCD, newCB ⟩ := newC
  --         cases newCB
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --       . apply Or.inr
  --         obtain ⟨ newCD, newCB ⟩ := newC
  --         cases newCB
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --   . cases h3'; constructor <;> try rfl
  --     . simp_all;  rename_i H1 H2 _
  --       repeat cases ‹_ ∧ _›
  --       subst_vars
  --       cases H2; rename_i elem H2
  --       apply Exists.intro elem
  --       intro h; specialize H2 h
  --       rename_i B _ _ _ _ _ _ _ _ _ _ _
  --       cases B
  --       . cases h3
  --         simp_all
  --         repeat cases ‹_ ∧ _›
  --         subst_vars
  --         obtain ⟨ newCD, newCB ⟩ := newC
  --         cases newCB <;> simp_all
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --       . cases h3
  --         rename_i h3 _ _ _ _
  --         simp at h3
  --         repeat cases ‹_ ∧ _›
  --         subst_vars; simp_all
  --         obtain ⟨ newCD, newCB ⟩ := newC
  --         cases newCB <;> simp_all
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --         . rw[List.append_cons] at *; ac_nf at *
  --           aesop (add safe (by contradiction)) (config := {useDefaultSimpSet := false})
  --     . rename_i H1 _ _
  --       simp at H1
  --       repeat cases  ‹_ ∧ _›
  --       subst_vars
  --       intro n k i' h1 h2 h4 h5 h6
  --       simp_all
  --       unfold iterate at h1
  --       cases h1
  --       rename_i h
  --       cases h3; rename_i h _ _ _
  --       simp at h
  --       repeat cases  ‹_ ∧ _›
  --       subst_vars
  --       simp_all
  --       repeat cases  ‹_ ∧ _›
  --       subst_vars
  --       rw[ ← Nat.lt_add_one_iff] at h4
  --       have H := Nat.eq_of_le_of_lt_succ h2 h4
  --       simp_all











end Proof
end Graphiti.LoopRewrite
