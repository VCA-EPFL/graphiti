/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martina Camaioni
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import Graphiti.Core.Simp
import Graphiti.Core.Module
import Graphiti.Core.ModuleReduction
import Graphiti.Core.ExprLow
import Graphiti.Core.Component
import Graphiti.Core.KernelRefl
import Graphiti.Core.Reduce
import Graphiti.Core.List
import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Tactic
import Graphiti.Core.Rewrites.MuxTaggedRewrite

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace Graphiti.MuxTaggedRewrite

abbrev Ident := Nat

def ε (Tag T : Type _) : IdentMap String (TModule String) :=
  [ ("join", ⟨ _, StringModule.join Tag T ⟩)
  , ("mux", ⟨ _, StringModule.mux T ⟩)
  , ("tagged_mux", ⟨ _, StringModule.mux (Tag × T) ⟩)
  , ("fork", ⟨ _, StringModule.fork2 Bool⟩)
  , ("joinC", ⟨ _, StringModule.joinC Tag T Bool ⟩)
  , ("muxC", ⟨ _, StringModule.muxC T ⟩)
  , ("branch", ⟨ _, StringModule.branch Tag ⟩)
  ].toAssocList

def lhsNames := (rewrite.rewrite []).get rfl |>.input_expr.build_module_names
def lhs_intNames := lhsLower_int.build_module_names
def rhsNames := (rewrite.rewrite []).get rfl |>.output_expr.build_module_names

def lhsModuleType (Tag T : Type _) : Type := by
  precomputeTac [T| (rewrite.rewrite []).get rfl |>.input_expr, ε Tag T ] by
    -- ExprHigh reduction
    dsimp [drunfold_defs, ExprHigh.extract, List.foldlM]
    simp (disch := simp) only [AssocList.find?_cons_eq, AssocList.find?_cons_neq]; dsimp
    simp
    -- Lowering reduction -> creates ExprLow
    dsimp [ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry]
    -- Unfold build_module
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    -- Reduce environment access
    simp [ε]

def lhs_intModuleType (Tag T : Type _) : Type := by
  precomputeTac [T| lhsLower_int, ε Tag T ] by
    dsimp [drunfold_defs, ExprHigh.extract, List.foldlM]
    simp (disch := simp) only [AssocList.find?_cons_eq, AssocList.find?_cons_neq]; dsimp
    simp
    -- Lowering reduction -> creates ExprLow
    dsimp [ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry]
    -- Unfold build_module
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp [ε]

attribute [drcomponents] toString

def_module lhsModule (Tag T : Type _) : StringModule (lhsModuleType Tag T) :=
  [e| (rewrite.rewrite []).get rfl |>.input_expr, ε Tag T ]
reduction_by
  dr_reduce_module
  (dsimp -failIfUnchanged [drunfold_defs, ExprHigh.extract, List.foldlM]
   rw [rw_opaque (by simp -failIfUnchanged (disch := simp) only [drcompute, ↓reduceIte]; rfl)]
   dsimp -failIfUnchanged [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
         , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
   rw [rw_opaque (by simp -failIfUnchanged (disch := simp) only [ε, drcompute, ↓reduceIte]; rfl)]
   dsimp -failIfUnchanged [drcomponents]
   dsimp -failIfUnchanged [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter]; simp (disch := simp) only [drcompute, ↓reduceIte]
   dsimp -failIfUnchanged [Module.product, Module.liftL, Module.liftR]
   dsimp -failIfUnchanged [Module.connect']
   simp -failIfUnchanged (disch := simp) only [drcompute, ↓reduceIte]
   conv =>
     pattern (occs := *) Module.connect'' _ _
     all_goals
       rw [(Module.connect''_dep_rw (h := by simp -failIfUnchanged (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp -failIfUnchanged)
                                (h' := by simp -failIfUnchanged (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp -failIfUnchanged))]
   unfold Module.connect''
   dsimp -failIfUnchanged)

@[drunfold] def lhs_intModule (Tag T : Type _) : StringModule (lhs_intModuleType Tag T) := by
  precomputeTac [e| lhsLower_int, ε Tag T ] by
    dsimp [drunfold_defs, ExprHigh.extract, List.foldlM]
    rw [rw_opaque (by simp (disch := simp) only [drcompute, ↓reduceIte]; rfl)]
    dsimp [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
          , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [rw_opaque (by simp (disch := simp) only [ε, drcompute, ↓reduceIte]; rfl)]
    dsimp [drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter]; simp (disch := simp) only [drcompute, ↓reduceIte]
    dsimp [Module.product, Module.liftL, Module.liftR]
    dsimp [Module.connect']
    simp (disch := simp) only [drcompute, ↓reduceIte]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp)
                                 (h' := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp))]
    unfold Module.connect''
    dsimp

def rhsModuleType (Tag T : Type _) : Type := by
  precomputeTac [T| (rewrite.rewrite []).get rfl |>.output_expr, ε Tag T ] by
    dsimp [drunfold_defs, ExprHigh.extract, List.foldlM]
    -- simp (disch := simp) only [AssocList.find?_cons_eq, AssocList.find?_cons_neq]; dsimp
    -- simp
    -- Lowering reduction -> creates ExprLow
    dsimp [ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry]
    -- Unfold build_module
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp [ε]

-- #reduce rhsNames
-- #reduce rhsModuleType

@[drunfold] def rhsModule (Tag T : Type _) : StringModule (rhsModuleType Tag T) := by
  precomputeTac [e| (rewrite.rewrite []).get rfl |>.output_expr, ε Tag T ] by
    dsimp [drunfold_defs, ExprHigh.extract, List.foldlM]
    rw [rw_opaque (by simp -failIfUnchanged (disch := simp) only [drcompute, ↓reduceIte]; rfl)]
    dsimp [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
          , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [rw_opaque (by simp (disch := simp) only [ε, drcompute, ↓reduceIte]; rfl)]
    dsimp [drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter]; simp (disch := simp) only [drcompute, ↓reduceIte]
    dsimp [Module.product, Module.liftL, Module.liftR]
    dsimp [Module.connect']
    simp (disch := simp) only [drcompute, ↓reduceIte]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp)
                                 (h' := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp))]
    unfold Module.connect''
    dsimp

attribute [dmod] Batteries.AssocList.find? BEq.beq

-- instance {Tag T} : MatchInterface (rhsModule Tag T) (lhs_intModule Tag T) where
--   input_types := by
--     intro ident;
--     by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).inputs)
--     · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
--     · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
--       simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
--       simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
--       rcases ident with ⟨ i1, i2 ⟩;
--       repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
--       sorry
--   output_types := by
--     intro ident;
--     by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).outputs)
--     · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
--     · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
--       simp at h'
--       simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
--       rcases ident with ⟨ i1, i2 ⟩;
--       repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
--       rfl
--   inputs_present := by sorry
--   outputs_present := by sorry

-- instance {Tag T} : MatchInterface  (lhs_intModule Tag T) (lhsModule Tag T) where
--   input_types := by
--     intro ident;
--     by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).inputs)
--     · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
--     · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
--       simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
--       simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
--       rcases ident with ⟨ i1, i2 ⟩;
--       repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
--       sorry
--   output_types := by
--     intro ident;
--     by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).outputs)
--     · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
--     · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
--       simp at h'
--       simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
--       rcases ident with ⟨ i1, i2 ⟩;
--       repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
--       rfl
--   inputs_present := by sorry
--   outputs_present := by sorry

-- #reduce rhsNames
-- #reduce rhsModuleType

-- #reduce lhsNames
-- #reduce lhsModuleType

-- #reduce lhs_intNames
-- #reduce lhs_intModuleType



-- def φ {Tag T} (state_rhs : rhsModuleType Tag T) (state_lhs : lhs_intModuleType Tag T) : Prop :=
--   omit [Inhabited Data] in theorem
--   let ⟨⟨y_join_tag, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩ := state_lhs
--   x_muxT.map Prod.snd ++ x_join1_r = List.map Prod.fst (List.filter (fun x => x.2 == true) y_join_r) ++ y_muxT ∧
--   x_muxF.map Prod.snd ++ x_join2_r = List.map Prod.fst (List.filter (fun x => x.2 == false) y_join_r) ++ y_muxF ∧
--   x_muxC ++ x_fork.2 = List.map Prod.snd y_join_r ++ y_muxC ∧
--   List.map Prod.fst (List.filter (fun x => x.2 == some true) (List.zipWithAll (fun a b => (a, b)) (y_join_tag) ((List.map Prod.snd y_join_r) ++ y_muxC ))) =
--   ((List.filterMap (fun | (some tag, some true) => some tag | _ => none) (List.zipWithAll (fun a b => (a, b)) (x_branch_tag) (x_branchC ++ x_fork.1)))) ++ x_join1_l ++ List.map Prod.fst x_muxT

--   -- List.map Prod.fst (List.filter (fun x => x.2 == false) (List.zipWithAll y_join_tag ((List.map Prod.snd y_join_r) ++ y_muxC ))) =
--   -- List.map Prod.fst (List.filter (fun x => x.2 == false) (List.zipWithAll x_branch_tag (x_branchC ++ x_fork.1))) ++ x_join2_l ++ List.map Prod.snd x_muxF ∧
--   -- y_muxC.head? = some true → y_muxT = [] ∧
--   -- y_muxC.head? = some false → y_muxF = []

-- def φ' {Tag T} (state_rhs : rhsModuleType Tag T) (state_lhs : lhs_intModuleType Tag T) : Prop :=
--   let ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩ := state_rhs
--   let ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩ := state_lhs
--   x_muxT.map Prod.snd ++ x_join1_r = List.map Prod.fst (List.filter (fun x => x.2 == true) y_join_r) ++ y_muxT ∧
--   x_muxF.map Prod.snd ++ x_join2_r = List.map Prod.fst (List.filter (fun x => x.2 == false) y_join_r) ++ y_muxF ∧
--   x_muxC = List.map Prod.snd y_join_r ++ y_muxC ∧
--   x_muxT.map Prod.fst ++ x_join1_l ++ x_fork  = y_join_l ∧
--   x_muxF.map Prod.fst ++ x_join2_l ++ x_fork   = y_join_l

-- theorem add_element {α} (l l' l'' : List α) : l ++ l' = l ++ l'' -> l' = l'' := by
--   intro h
--   revert h
--   induction l
--   . simp
--   . rename_i a tail h1
--     simp


-- theorem lhs_internal_correctness {Tag T}:
--   ∀ (x : rhsModuleType Tag T) (y : lhs_intModuleType Tag T), φ' x y -> ∃ y',
--     existSR [fun st st' =>
--     ∃ a b a_1 a_2 b_1 a_3,
--       ((false :: b_1 = st.2.2.2 ∧ a_1 = st.2.1 ∧ a_3 :: a_2 = st.2.2.1) ∧ st.1 = (a, b)) ∧
--           (st'.1.2 = b ++ [(a_3, false)] ∧ st'.1.1 = a) ∧ (a_1, a_2, b_1) = st'.2 ∨
--         ((true :: b_1 = st.2.2.2 ∧ a_3 :: a_1 = st.2.1 ∧ a_2 = st.2.2.1) ∧ st.1 = (a, b)) ∧
--           (st'.1.2 = b ++ [(a_3, true)] ∧ st'.1.1 = a) ∧ (a_1, a_2, b_1) = st'.2] y y'
--     ∧ φ x y' := by
--     intro x ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩ φ
--     revert y_join_r y_muxT y_muxF y_join_l x
--     induction y_muxC with
--     | nil =>
--       intros
--       constructor; constructor; constructor; constructor
--       . rename_i H; cases H
--         . simp_all only [beq_true, beq_false, List.append_nil, List.append_assoc]
--       . rename_i H; cases H
--         and_intros <;> simp_all
--     | cons currC y_muxC h =>
--       cases currC
--       . intro x y_join_l y_join_r y_muxT y_muxF φ
--         rcases y_muxF with _ | ⟨ output, y_muxF ⟩
--         . subst_vars
--           constructor; constructor
--           . constructor
--           . rcases φ with ⟨ φ₁, φ₂ ⟩
--             simp at φ₂
--             rcases φ₂ with ⟨ _, _, _, _ ⟩
--             simp at φ₁
--             constructor
--             . simp; subst_vars; assumption
--             . and_intros <;> subst_vars <;> try simp <;> try assumption
--               . rename_i hr
--                 cases x
--                 simp at hr
--                 simp; assumption
--         . subst_vars
--           subst_vars
--           rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
--           have : Graphiti.MuxTaggedRewrite.φ' (x_fork, (x_muxT, x_muxF, x_muxC), (x_join1_l, x_join1_r), x_join2_l, x_join2_r)
--                 ((y_join_l, y_join_r ++ [(output, false)]), y_muxT, y_muxF, y_muxC) := by
--             rcases φ with ⟨ φ₁, φ₂, φ₃, φ₄, φ₅ ⟩
--             unfold φ'; and_intros
--             all_goals simp_all
--           specialize h _ _ _ _ _ this
--           rcases h with ⟨ yl, h ⟩
--           apply Exists.intro ((_, _), (_, (_, _))); constructor
--           . apply existSR.step _ ((_, _), (_, (_, _))) _
--             . constructor
--             . constructor; constructor;constructor;
--               constructor; exists y_muxC, output
--               simp; and_intros
--               rfl; rfl; rfl; rfl; rfl; rfl; rfl; rfl; rfl
--             . apply h.left
--           . apply h.right
--       . intro x y_join_l y_join_r y_muxT y_muxF φ
--         rcases y_muxT with _ | ⟨ output, y_muxT ⟩
--         . subst_vars
--           constructor; constructor
--           . constructor
--           . rcases φ with ⟨ φ₁, φ₂ ⟩
--             simp at φ₂
--             rcases φ₂ with ⟨ _, _, _, _ ⟩
--             simp at φ₁
--             constructor
--             . simp; subst_vars; assumption
--             . and_intros <;> subst_vars <;> try simp <;> try assumption
--               . rename_i hr
--                 cases x
--                 simp at hr
--                 simp; assumption
--         . subst_vars
--           subst_vars
--           rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
--           have : Graphiti.MuxTaggedRewrite.φ' (x_fork, (x_muxT, x_muxF, x_muxC), (x_join1_l, x_join1_r), x_join2_l, x_join2_r)
--                 ((y_join_l, y_join_r ++ [(output, true)]), y_muxT, y_muxF, y_muxC) := by
--             rcases φ with ⟨ φ₁, φ₂, φ₃, φ₄, φ₅ ⟩
--             unfold φ'; and_intros
--             all_goals simp_all
--           specialize h _ _ _ _ _ this
--           rcases h with ⟨ yl, h ⟩
--           apply Exists.intro ((_, _), (_, (_, _))); constructor
--           . apply existSR.step _ ((_, _), (_, (_, _))) _
--             . constructor
--             . constructor; constructor;constructor;
--               constructor; exists y_muxC, output
--               simp; and_intros
--               rfl; rfl; rfl; rfl; rfl; rfl; rfl; rfl; rfl
--             . apply h.left
--           . apply h.right









-- @[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
--   subst_vars; rfl

-- theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
--         (h : m = m' := by reduce; rfl) :
--   m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
--   constructor <;> (intros; subst h; assumption)

-- theorem sigma_rw_simp {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
--         (h : m = m' := by simp [drunfold,drcompute,seval]; rfl) :
--   m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
--   constructor <;> (intros; subst h; assumption)

-- theorem correct_threeway_merge'' {Tag T: Type _} [DecidableEq T]:
--   rhsModule Tag T ⊑_{φ} lhs_intModule Tag T := by
--   intro x y HPerm
--   constructor
--   . admit
--   -- . intro ident new_i v Hcontains Hsem
--   --   rcases HPerm with ⟨ h₁, h₂, h₃, h₄, h₅, h₆, h₇ ⟩
--   --   have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
--   --   fin_cases Hkeys
--   --   . simp [drunfold,drcompute,seval] at Hsem ⊢
--   --     rw[sigma_rw_simp] at Hsem; simp at Hsem
--   --     rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
--   --     subst_vars
--   --     apply Exists.intro ((_, _), (_, (_, _)))
--   --     rw [sigma_rw_simp]; dsimp
--   --     constructor
--   --     .  (repeat constructor) <;> rfl
--   --     . constructor; constructor
--   --       . constructor
--   --       . simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
--   --         rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
--   --         simp at Hsem₂
--   --         rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
--   --         constructor
--   --         . simp
--   --           subst_vars
--   --           simp at *; assumption
--   --         . and_intros <;> (try subst_vars) <;> (try simp[*]) <;> (try assumption)
--   --           . simp_all only [beq_true, beq_false, List.append_assoc]
--   --             rw[← h₄]; simp
--   --           . simp_all only [beq_true, beq_false, List.append_assoc]
--   --             rw[← h₅]; simp
--   --   . simp [drunfold,drcompute,seval] at Hsem ⊢
--   --     rw[sigma_rw_simp] at Hsem; simp at Hsem
--   --     rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
--   --     rcases y with ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩
--   --     subst_vars
--   --     apply Exists.intro ((_, _), (_, (_, _)))
--   --     rw [sigma_rw_simp]; dsimp
--   --     constructor
--   --     . (repeat constructor) <;> rfl
--   --     . apply lhs_internal_correctness
--   --       simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
--   --       rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
--   --       simp at Hsem₂
--   --       simp at Hsem₁
--   --       rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
--   --       constructor <;> subst_vars <;> simp_all
--   --   . simp [drunfold,drcompute,seval] at Hsem ⊢
--   --     rw[sigma_rw_simp] at Hsem; simp at Hsem
--   --     rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
--   --     rcases y with ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩
--   --     subst_vars
--   --     apply Exists.intro ((_, _), (_, (_, _)))
--   --     rw [sigma_rw_simp]; dsimp
--   --     constructor
--   --     . (repeat constructor) <;> rfl
--   --     . apply lhs_internal_correctness
--   --       simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
--   --       rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
--   --       simp at Hsem₂
--   --       simp at Hsem₁
--   --       rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
--   --       subst_vars
--   --       constructor <;> simp_all
--   --       . rw[ ← List.append_assoc]
--   --         rw[ ← List.append_assoc]
--   --         simp_rw[← h₁]
--   --   . simp [drunfold,drcompute,seval] at Hsem ⊢
--   --     rw[sigma_rw_simp] at Hsem; simp at Hsem
--   --     rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
--   --     rcases y with ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩
--   --     subst_vars
--   --     apply Exists.intro ((_, _), (_, (_, _)))
--   --     rw [sigma_rw_simp]; dsimp
--   --     constructor
--   --     . (repeat constructor) <;> rfl
--   --     . apply lhs_internal_correctness
--   --       simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
--   --       rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
--   --       simp at Hsem₂
--   --       simp at Hsem₁
--   --       rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
--   --       subst_vars
--   --       constructor <;> simp_all
--   --       . rw[ ← List.append_assoc]
--   --         rw[ ← List.append_assoc]
--   --         simp_rw[← h₂]
--   . intro ident new_i v Hcontains Hsem
--     rcases HPerm with ⟨ h₁, h₂, h₃, h₄, h₅, h₆, h₇ ⟩
--     have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
--     fin_cases Hkeys
--     . simp [drunfold,drcompute,seval] at Hsem ⊢
--       rw[sigma_rw_simp] at Hsem; simp at Hsem
--       rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
--       rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
--       rcases y with ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩
--       subst_vars
--       rcases v with ⟨ouput_tag,ouput⟩
--       simp at Hsem
--       rcases Hsem with ⟨⟨⟨ H₁, H₂,H₃ ⟩ | ⟨H₄, H₅, H₆⟩⟩,  H₁₁⟩ <;> rename_i Hsem <;> rcases Hsem with ⟨ ⟨ H₇, H₈ ⟩, H₉, H₁₀⟩
--       <;> subst_vars <;> simp_all
--       . rw[List.cons_eq_append] at h₂
--         rcases h₂ with ⟨p₁, p₂, p₃ ⟩ | ⟨rest, p₂, p₃ ⟩
--         . simp at p₁
--           rcases y_join_r with _ | ⟨y_joint_r_h, y_join_r_t⟩
--           . simp at H₁; rw[← H₁] at h₇; simp at h₇
--           . simp at p₁
--             rcases y_joint_r_h with ⟨ a, b ⟩
--             specialize p₁ a; cases p₁
--             simp at H₁; rcases H₁ with ⟨ k, j ⟩
--             subst k; simp_all
--         . rcases y_join_r with _ | ⟨y_joint_r_h, y_join_r_t⟩
--           . simp_all
--           . apply Exists.intro ((_, _), (_, (_, _)))
--             rw [sigma_rw_simp]; dsimp
--             constructor
--             . (repeat constructor) <;> (try rfl)
--               . rw[← h₅]
--               . left
--                 simp_all
--                 constructor
--                 . cases y_joint_r_h; simp at p₂; simp at H₁; simp_all
--                 . rfl
--             . constructor; constructor
--               . constructor
--               . unfold φ; and_intros
--                 . simp
--                   subst_vars
--                   cases y_joint_r_h
--                   simp_all
--                 . cases y_joint_r_h; simp_all
--                 . cases y_joint_r_h; simp_all
--                 . rcases y_joint_r_h with ⟨ y_join_value, y_joint_condiction ⟩
--                   simp_all
--                   rcases p₂ with ⟨ p₂, p₂' ⟩
--                   rcases H₁ with ⟨ H₁, H₁'⟩

--                   rw[List.cons_eq_append] at h₅
--                   rcases h₅ with ⟨p₁, p₂, p₃ ⟩ | ⟨rest, p₂, p₃ ⟩


--                   rw[← h₅]
--                   simp



end Graphiti.MuxTaggedRewrite
