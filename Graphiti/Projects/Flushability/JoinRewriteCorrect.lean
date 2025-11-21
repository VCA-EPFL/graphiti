/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Hamza Remmal
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq
import Mathlib.Tactic

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
import Graphiti.Core.Rewrites.JoinRewrite

import Graphiti.Projects.Flushability.ModuleWellformeness
import Graphiti.Projects.Flushability.SimulationRelation
import Graphiti.Projects.Flushability.DeterministicModule
import Graphiti.Projects.Flushability.ConfluentModule
import Graphiti.Projects.Flushability.FlushedModule
import Graphiti.Projects.Flushability.Outputability

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace Graphiti.JoinRewrite

open StringModule

abbrev Ident := Nat

-- abbrev S₁ := "S1"
-- abbrev S₂ := "S2"
-- abbrev S₃ := "S3"
variable {T₁ T₂ T₃ : Type}
variable (S₁ S₂ S₃ : String)

@[drunfold_defs]
def rewriteLhsRhs : DefiniteRewrite String String := ⟨lhsLower S₁ S₂ S₃, rhsLower S₁ S₂ S₃⟩

def environmentLhs : IdentMap String (TModule1 String) := lhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd
def environmentRhs : IdentMap String (TModule1 String) := rhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd

@[drenv] theorem find?_join1_data : (Batteries.AssocList.find? ("join " ++ S₁ ++ " " ++ S₂) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ T₂⟩ := by stop
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join " ++ S₁ ++ " " ++ S₂) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : ("join " ++ S₁ ++ " " ++ S₂ == "join " ++ S₁ ++ " " ++ S₂) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join2_data : (Batteries.AssocList.find? ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join (T₁ × T₂) T₃⟩ := by stop
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join1_data2 : (Batteries.AssocList.find? ("join " ++ S₂ ++ " " ++ S₃) (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₂ T₃⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == "join " ++ S₂ ++ " " ++ S₃) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == "join " ++ S₂ ++ " " ++ S₃) = false := by sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : ("join " ++ S₂ ++ " " ++ S₃ == "join " ++ S₂ ++ " " ++ S₃) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join2_data2 : (Batteries.AssocList.find? ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ (T₂ × T₃)⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")")) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_pure_data2 : (Batteries.AssocList.find? ("pure (" ++ S₁ ++ "×(" ++ S₂ ++ "×" ++ S₃ ++ ")) ((" ++ S₁ ++ "×" ++ S₂ ++ ")×" ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, pure λ ((a, b, c) : T₁ × (T₂ × T₃)) => ((a, b), c)⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})") = false := by sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})") = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

variable (T₁ T₂ T₃) in
include T₁ T₂ T₃ in
seal environmentLhs in
def_module lhsModuleType : Type :=
  [T| (rewriteLhsRhs S₁ S₂ S₃).input_expr, (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_join2_data, find?_join1_data]
  dsimp

variable (T₁ T₂ T₃) in
seal environmentLhs in
def_module lhsModule : StringModule (lhsModuleType T₁ T₂ T₃) :=
  [e| (rewriteLhsRhs S₁ S₂ S₃).input_expr, (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃).find? ]
reduction_by
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [Module.liftL, Module.liftR, drcomponents])

variable (T₁ T₂ T₃) in
seal environmentRhs in
def_module rhsModuleType : Type :=
  [T| (rewriteLhsRhs S₁ S₂ S₃).output_expr, (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_pure_data2, find?_join2_data2, find?_join2_data, find?_join1_data, find?_join1_data2]
  dsimp

variable (T₁ T₂ T₃) in
seal environmentRhs in
def_module rhsModule : StringModule (rhsModuleType T₁ T₂ T₃) :=
  [e| (rewriteLhsRhs S₁ S₂ S₃).output_expr, (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃).find? ]

---------------------------------------------------------------------------------------------------

section MatchInterface

instance : MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by
  dsimp [rhsModule, lhsModule]
  solve_match_interface

end MatchInterface

section Flushability

private inductive partially_flushed: lhsModuleType T₁ T₂ T₃ -> Prop where
| lhs: ∀ lower arb, partially_flushed ⟨lower, [], arb⟩
| rhs: ∀ lower arb, partially_flushed ⟨lower, arb, []⟩

private theorem pf_is_partially_flushed:
  ∀ s, pf (lhsModule T₁ T₂ T₃) s → partially_flushed s :=
by
  intro ⟨s1, s2, s3⟩ hr; dsimp [lhsModuleType, lhsModule] at *
  specialize hr ?r (by simp; rfl)
  cases s2 <;> cases s3 <;> try constructor
  exfalso
  apply hr ⟨⟨_, _⟩, ⟨_, _⟩⟩
  dsimp
  iterate 5 (apply Exists.intro _)
  and_intros <;> rfl

private theorem partially_flushed_is_pf:
  ∀ s, partially_flushed s → pf (lhsModule T₁ T₂ T₃) s :=
by
  intro s h
  cases h
  all_goals
    unfold pf
    intros rule hᵣ _ h
    simp [lhsModule] at hᵣ <;> subst hᵣ
    simp at h

instance: Flushable (lhsModule T₁ T₂ T₃) := by
  constructor
  intro ⟨⟨l1, l2⟩, ⟨l3, l4⟩⟩
  induction l3 generalizing l1 l2 l4 with
  | nil =>
    apply pf_is_flushable
    apply partially_flushed_is_pf
    constructor
  | cons x xs ih =>
    cases l4 with
    | nil =>
      apply pf_is_flushable
      apply partially_flushed_is_pf
      constructor
    | cons head tail =>
      specialize ih (l1 ++ [(x, head)]) l2 tail
      obtain ⟨ ⟨⟨_, _⟩, ⟨_, _⟩⟩, _, _⟩ := ih
      apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
      constructor
      . apply existSR.step _ ⟨ ⟨ _, _ ⟩, _, _ ⟩ _
        . unfold lhsModule; simp; rfl
        . repeat apply Exists.intro
          and_intros <;> rfl
        . assumption
      . assumption

-- "if we pop an output from a flushed state, the resulting state is also flushed"
-- TODO: This can be removed if we embed the flushability in the output rules too
instance: OutputPreservesFlushability (lhsModule T₁ T₂ T₃) := by
  constructor
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ hpf h₁
  apply pf_is_partially_flushed at hpf
  apply partially_flushed_is_pf
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains <;> subst HContains
    dsimp [lhsModule] at h₁
    rw [PortMap.rw_rule_execution] at h₁
    repeat
      cases ‹_ ∧ _›; simp at *
    subst_vars
    cases hpf <;> constructor
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

end Flushability

section Coercions

variable {ident: InternalPort String}

-- TODO: Dervies the coercions automatically from the match interfaces
instance: Coe ((rhsModule T₁ T₂ T₃).inputs.getIO ident).fst ((lhsModule T₁ T₂ T₃).inputs.getIO ident).fst where
  coe := by
    have: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
    intro
    simpa [<- this.input_types]

instance: Coe ((rhsModule T₁ T₂ T₃).outputs.getIO ident).fst ((lhsModule T₁ T₂ T₃).outputs.getIO ident).fst where
  coe := by
    have: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
    intro h
    simpa [<- this.output_types]

-- TODO: Make this cast a coercion
def cast:
  ((flushed (rhsModule T₁ T₂ T₃)).inputs.getIO ident).fst = ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).fst :=
by
  have: MatchInterface (flushed (rhsModule T₁ T₂ T₃)) (rhsModule T₁ T₂ T₃) := by infer_instance
  rw [this.input_types ident]
  have: MatchInterface (flushed (lhsModule T₁ T₂ T₃)) (lhsModule T₁ T₂ T₃) := by infer_instance
  rw [this.input_types ident]
  have: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
  exact this.input_types ident

-- TODO: Make this cast a coercion
def cast':
  ((flushed (rhsModule T₁ T₂ T₃)).outputs.getIO ident).fst = ((flushed (lhsModule T₁ T₂ T₃)).outputs.getIO ident).fst :=
by
  dsimp [flushed]
  have: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
  exact this.output_types ident

end Coercions

section SimulationRelation

def ψ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  let ⟨⟨j2l, j2r⟩, ⟨j1l, j1r⟩⟩ := lhs
  let ⟨⟨j2l', j2r'⟩, ⟨⟨j1l', j1r'⟩, p⟩⟩ := rhs
  (j2l.map Prod.fst ++ j1l = p.map (Prod.fst ∘ Prod.fst) ++ j2l') ∧
  (j2l.map Prod.snd ++ j1r = p.map ((Prod.snd ∘ Prod.fst)) ++ j2r'.map Prod.fst ++ j1l') ∧
  (j2r = p.map Prod.snd ++ j2r'.map Prod.snd ++ j1r')

private theorem ψ_holds_over_internals_spec:
  ∀ i s s', ψ i s → existSR (lhsModule T₁ T₂ T₃).internals s s' → ψ i s' :=
by
  intro ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ s s' Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold lhsModule at Hrule; simp at Hrule
    subst_vars
    obtain ⟨_, _, _, _, _, _, _, _⟩ := c
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
    rename_i a _ _ _ _ _ b; simp at a b
    obtain ⟨ ⟨_, _⟩, ⟨_, _⟩⟩ := a
    obtain ⟨ ⟨_, _⟩ , ⟨_, _⟩⟩ := b
    unfold ψ at *; simp at *
    subst_vars
    obtain ⟨ _, ⟨_, _⟩ ⟩ := Hψ
    simp; and_intros <;> simp_all
    grind [ψ]

private theorem ψ_holds_over_internals_impl:
  ∀ i i' s, ψ i s → existSR (rhsModule T₁ T₂ T₃).internals i i' → ψ i' s :=
by
  intro i i' ⟨⟨_, _⟩, ⟨_, _⟩⟩ Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold rhsModule at Hrule; simp at Hrule
    cases Hrule <;> subst_vars
    . let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> try simp <;> grind
      grind
    . obtain ⟨_, _, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩ := c
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _⟩ := synth2
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> simp
      . assumption
      . assumption

private theorem internals_preserves_ψ: ∀ i i' s s',
  ψ i s → existSR (rhsModule T₁ T₂ T₃).internals i i' → existSR (lhsModule T₁ T₂ T₃).internals s s' → ψ i' s' :=
by
  intros i i' s s' _ _ _
  have: ψ i s' := by
    apply ψ_holds_over_internals_spec <;> assumption
  apply ψ_holds_over_internals_impl <;> assumption

private theorem inputs_preserves_ψ: ∀ ident i₁ i₂ v s₁ s₂,
  ψ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).inputs.getIO ident).snd i₁ ↑v i₂
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ ↑v s₂
  → ψ i₂ s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩  h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).inputs.contains ident
  . simp [rhsModule] at HContains
    rcases HContains with h | h | h <;> subst h
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      --
      subst_vars
      --
      dsimp [ψ]
      and_intros
      . rw [<- List.append_assoc, <- List.append_assoc]
        congr
      . assumption
      . rfl
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      subst_vars
      dsimp [ψ]
      and_intros
      . assumption
      . rw [<- List.append_assoc, <- List.append_assoc]
        congr
      . rfl
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      --
      subst_vars
      --
      dsimp [ψ]
      and_intros
      . assumption
      . assumption
      . simp
  . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains)

private theorem outputs_preserves_ψ: ∀ ident i₁ i₂ v s₁ s₂,
  ψ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ ↑v s₂
  → ψ i₂ s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [rhsModule] at HContains; subst HContains
    unfold rhsModule at h₂
    rw [PortMap.rw_rule_execution] at h₂; simp at h₂
    repeat
      cases ‹_ ∧ _›
    simp at *
    cases ‹_ ∧ _›
    subst_vars

    dsimp [ψ]
    and_intros <;> simp at * <;> assumption
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

instance: SimulationRelation ψ (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := {
  inputs_preserved    := inputs_preserves_ψ
  internals_preserved := internals_preserves_ψ
  outputs_preserved   := outputs_preserves_ψ
  initial_state_preserves := by
    intro ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := h₁
    obtain ⟨⟨_, _⟩, _, _⟩ := h₂
    trivial
}

end SimulationRelation

section Determinism

private theorem input_rules_deterministic: ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₃
  → s₂ = s₃ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
  . simp [lhsModule] at HContains
    rcases HContains with h | h | h <;> subst h
    all_goals
      dsimp [lhsModule] at h₁ h₂
      rw [PortMap.rw_rule_execution] at h₁ h₂
      dsimp at h₁ h₂
      repeat
        cases ‹_ ∧ _›
        try simp at *
        try subst_vars
      rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

private theorem internal_rules_deterministic:
  ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals , ∀ s₁ s₂ s₃, rule s₁ s₂ → rule s₁ s₃ → s₂ = s₃ :=
by
  intro _ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  simp [lhsModule] at *
  subst_vars
  dsimp at h₁ h₂
  obtain ⟨_, _, _, _, _, _, _⟩ := h₁
  obtain ⟨_, _, _, _, _, _, _⟩ := h₂
  repeat
    cases ‹_ ∧ _›
    try simp at *
    try subst_vars
  rfl

private theorem output_rules_deterministic: ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₃
  → s₂ = s₃ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains; subst HContains
    dsimp [lhsModule] at h₁ h₂
    rw [PortMap.rw_rule_execution] at h₁ h₂
    dsimp at h₁ h₂
    repeat
      cases ‹_ ∧ _›
      try simp at *
      try subst_vars
    rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

instance: Deterministic (lhsModule T₁ T₂ T₃) :=
  {
    input_deterministic    := input_rules_deterministic
    internal_deterministic := internal_rules_deterministic
    output_deterministic   := output_rules_deterministic
  }

end Determinism

section Confluence

-- TODO: This module is GloballyConfluent
instance: QuasiConfluent (lhsModule T₁ T₂ T₃) := by sorry -- infer_instance

end Confluence

section Outputability

-- TODO: This representation means direct outputable
-- TODO: Note, in this example, an outputable state that is flushed is a direct one
--       Can we generalize this somehow?
--       Do we need to define outputabilty of rhs?
--       I've observed that we can come up with a congruence class definition in some flushable modules.
--       Can we do the same for outputability?
--       Can φ be somekind of "congruence" classes inclusion?
-- NOTE: an outputable state that is flushed (in normal form) doesn't necessary means it's a direct-outputable
--       and being a direct outputable doesn't mean it is in a flushed state (normal form)
--       I believe that in a well-formed module, and flushed-outputable state must be direct-outputable
--       It correlates with real life, internal rules are just modeling a behaviour that happens in real life
inductive outputable_state: lhsModuleType T₁ T₂ T₃ → Prop where
| direct: ∀ v₁ v₂ q₁ q₂ q₃ q₄, outputable_state ⟨⟨v₁ :: q₁, v₂ :: q₂⟩, q₃, q₄⟩
--| indirect: ∀ v₁ v₂ v₃ q₁ q₂ q₃ q₄, outputable_state ⟨⟨q₁, v₃ :: q₂⟩, v₁ :: q₃, v₂ :: q₄⟩

end Outputability

---------------------------------------------------------------------------------------------------

inductive at_least_single_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ v q₁ q₂ q₃ q₄, at_least_single_internal ⟨⟨v :: q₃, q₄⟩, ⟨q₁, q₂⟩⟩

theorem f₆: ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁
  → pf ((lhsModule T₁ T₂ T₃)) s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → at_least_single_internal s₁ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).outputs.contains ident
  .
    simp [rhsModule] at HContains <;> subst HContains
    --
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    obtain ⟨⟨_, _, _⟩, _, _⟩ := h₃
    obtain ⟨_, _, _⟩ := h₁
    subst_vars
    --
    apply pf_is_partially_flushed at h₂
    cases h₂
    . rename_i h₁ h₂
      simp at h₁ h₂
      sorry -- TODO: Reasoning about the length again?
    . rename_i h₁ h₂
      simp at h₁ h₂
      sorry -- TODO: Reasoning about the length again?
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

-- move to have a reasoning about atleast one in internal
-- we case only on once over queues that are in the top queue
theorem f₅: ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁ -- TODO: Remove this assumption
  → at_least_single_internal s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂ -- TODO: Remove this assumption
  → ∃ s₂, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ ↑v s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v s₁ h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).outputs.contains ident
  . simp [rhsModule] at HContains <;> subst HContains
    --
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    obtain ⟨⟨_, _, _⟩, _, _⟩ := h₃
    subst_vars
    --
    cases h₂
    obtain ⟨_, _, _⟩ := h₁
    apply Exists.intro ⟨⟨_, _⟩, ⟨_, _⟩⟩
    unfold lhsModule
    rw [PortMap.rw_rule_execution]
    simp
    and_intros
    . rw [List.map_cons, List.map_cons] at *
      simp at *
      iterate 2
        cases ‹_ ∧ _›
      apply Prod.ext <;> assumption
    . rfl
    . rwa [List.map_cons] at *
    . rfl
    . rfl
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

-- TODO: This is basically wellformess of a module?
--       I don't really need wellformness, I need to be able to close the gap
--       Basically, confluence between inputs and internals
--       How do I formulate it in all the confluence contexts
-- TODO: Get rid of this theorem
theorem lhs_can_always_input: ∀ ident s₁ v,
  (lhsModule T₁ T₂ T₃).inputs.contains ident → ∃ s₂, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ h
  simp [lhsModule] at h
  rcases h with h | h | h <;> subst h
  all_goals
    apply Exists.intro ⟨⟨_ , _⟩, ⟨_ , _⟩⟩
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    simp <;> and_intros <;> rfl

-- NOTE: To generalize this statement, the underlying module must:
--            - be able to input an element (can we call this the wellformness of a module?)
--            - be able to eventually reach a flushed state
-- Generalize it to if a module can input and it is flushable, then the flushable can input
-- Converse don't need flushability
theorem flhs_can_always_input [flhs: Flushable (lhsModule T₁ T₂ T₃)]:
  ∀ ident s₁ v,
  (lhsModule T₁ T₂ T₃).inputs.contains ident
  → ∃ s₂, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s₁ v s₂ :=
by
  intro ident s₁ v h
  obtain ⟨s₃, _⟩ := lhs_can_always_input ident s₁ (flushed_preserves_input_over_getIO.mp v) h
  obtain ⟨s₄, _⟩ := flhs.flushable s₃
  use s₄
  have := flushed_inputs_are_rflushed (lhsModule T₁ T₂ T₃) ident
  rw [PortMap.rw_rule_execution this]
  dsimp [rflushed]
  use s₃ <;> and_intros <;> assumption

---------------------------------------------------------------------------------------------------

theorem lengthify {T₁: Type _} (a b: List T₁): a = b → a.length = b.length := by
  intro heq; rw [heq]

theorem dropify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.drop l l₁ = List.drop l l₂ := by
  intro heq; rw [heq]

theorem product_is_list_zip {T₁ T₂: Type _} (x: List (T₁ × T₂)):
  x = List.zip (List.map Prod.fst x) (List.map Prod.snd x) :=
by
  induction x with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.zip_cons_cons, <- ih]

theorem append_iff {α} {a b c d : List α}:
  a.length = c.length → (a ++ b = c ++ d ↔ a = c ∧ b = d) :=
by
  intro lengths
  constructor
  . intro h
    and_intros
    . replace h := congrArg (List.take a.length) h
      rw [List.take_left, lengths, List.take_left] at h
      assumption
    . apply dropify a.length at h
      rw [List.drop_left, lengths, List.drop_left] at h
      assumption
  . intro ⟨_, _⟩; subst_vars; rfl

---------------------------------------------------------------------------------------------------

variable [MatchInterface (rhsModule T₁ T₂ T₃) (flushed (lhsModule T₁ T₂ T₃))] in
theorem refines₀'': rhsModule T₁ T₂ T₃ ⊑_{ψ} flushed (lhsModule T₁ T₂ T₃) := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  . intros
    sorry
  . intros
    use init_s
    simp only [exists_and_left]
    apply And.intro
    . apply existSR_reflexive
    . sorry
  . intros
    sorry

---------------------------------------------------------------------------------------------------
-------------------------- NON-FLUSHED, NON-INDUCTIVE ψ PROOF (BASELINE) --------------------------
---------------------------------------------------------------------------------------------------

section DirectRefinement

def φ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  (ψ rhs lhs) ∧ (partially_flushed lhs)

theorem refines₀: rhsModule T₁ T₂ T₃ ⊑_{φ} lhsModule T₁ T₂ T₃ := by
  have flhs: Flushable (lhsModule T₁ T₂ T₃) := by infer_instance
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i
      unfold rhsModule at HContains; simp at HContains

      rcases HContains with h | h | h
        <;> subst_vars <;> simp <;> rw [PortMap.rw_rule_execution] at a <;> simp at a
      . obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp only [eq_mp_eq_cast, cast_eq, List.concat_eq_append, and_self]
        . -- verify that the invariant holds when we flush the system
          obtain ⟨s', ⟨_, _⟩⟩ := flhs.flushable ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩ -- We flush the system to reach s'
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . simp only [<- List.append_assoc, List.append_left_inj]
                  assumption
                . assumption
                . rfl
              . assumption
            . apply pf_is_partially_flushed <;> assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := flhs.flushable ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
                  assumption
                . rfl
              . assumption
            . apply pf_is_partially_flushed <;> assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r ++ [s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := flhs.flushable ⟨⟨sj2l, sj2r ++ [s]⟩, sj1l, sj1r⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r  ++ [s]⟩, sj1l, sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
              . assumption
            . apply pf_is_partially_flushed <;> assumption
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    · use init_s
      rw [exists_and_left]
      and_intros
      . apply existSR_reflexive
      . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
        obtain ⟨⟨ij2l, ij2r⟩, ⟨ij1l, ij1r⟩, ip⟩ := init_i
        obtain ⟨⟨ij2l', ij2r'⟩, ⟨ij1l', ij1r'⟩, ip'⟩ := i
        unfold rhsModule at HContains; simp at HContains
        rcases HContains with h <;> subst_vars <;> simp
        rw [PortMap.rw_rule_execution (by simp [PortMap.getIO]; rfl)] at hrule <;>
        simp at hrule
        obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := hrule
        repeat cases ‹_∧_›
        subst_vars
        rename_i hlval hrval hpf
        dsimp at *
        rename_i htmp; cases htmp
        cases hpf
        · simp at hlval; simp at *
          rw [<- List.take_append_drop ij2l.length (List.map Prod.fst ij2r ++ ij1l)] at hrval
          --rw [<- List.append_assoc (List.map (Prod.snd ∘ Prod.fst) ip')] at hrval
          --rw [<- List.append.eq_2 _ _ ((List.map (Prod.snd ∘ Prod.fst) ip' ++ List.take ij2l.length (List.map Prod.fst ij2r' ++ ij1l'))] at hrval
          rw [show v.1.2 ::
              (List.map (Prod.snd ∘ Prod.fst) ip' ++
                (List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l) ++
                  List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l))) = v.1.2 ::
              (List.map (Prod.snd ∘ Prod.fst) ip' ++
                List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l)) ++
                  List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l) by simp] at hrval
          rw [append_iff] at hrval
          obtain ⟨hrvall, _⟩ := hrval
          . subst_vars
            apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
            and_intros <;> dsimp
            · rewrite [product_is_list_zip sj2l, hlval, hrvall]; rfl
            · apply lengthify at hlval; simp at hlval
              apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
              rw [List.append_nil, <- List.zip_eq_zipWith, List.map_fst_zip]
              simp [hrvall] -- lia + assumption in context
            . apply lengthify at hlval; simp at hlval
              apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
              rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
              . simp only [List.append_assoc, List.take_append_drop]
              . simp only [List.length_append, List.length_map, List.length_take, add_le_add_iff_left, inf_le_left]
            · rewrite [List.append_assoc]; rfl
            · constructor
          . apply lengthify at hlval; simp at hlval
            apply lengthify at hrval; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrval
            simp only [hlval, List.length_map, List.length_cons, List.length_append, List.length_take,
              add_left_inj, add_right_inj, left_eq_inf] -- lengthify the goal
            simp only [le_iff_exists_add, <- hrval, add_right_inj, exists_eq'] -- lia
        . simp at hrval; simp at *
          rw [<- List.take_append_drop (ij2r.length + ij1l.length) ij2l] at hlval
          rw [show v.1.1 ::
              (List.map (Prod.fst ∘ Prod.fst) ip' ++
                (List.take (ij2r.length + ij1l.length) ij2l ++
                  List.drop (ij2r.length + ij1l.length) ij2l)) = v.1.1 ::
              (List.map (Prod.fst ∘ Prod.fst) ip' ++
                List.take (ij2r.length + ij1l.length) ij2l) ++
                  List.drop (ij2r.length + ij1l.length) ij2l by simp] at hlval
          rw [append_iff] at hlval
          obtain ⟨hlvall, hlvalr⟩ := hlval
          . subst_vars
            apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
            . and_intros <;> dsimp
              . rewrite [product_is_list_zip sj2l, hrval, hlvall]; rfl
              . apply lengthify at hrval; simp at hrval
                apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
                simp [<- List.zip_eq_zipWith, List.map_fst_zip, hlvall]
              . apply lengthify at hrval; simp at hrval
                apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
                rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
                . simp
                . simp [hlvall]
              . simp
              . constructor
          . apply lengthify at hrval; simp [add_comm _ 1, add_right_inj, add_assoc] at hrval
            apply lengthify at hlval; simp [hrval, add_comm _ 1, add_left_inj, add_assoc] at hlval
            simp only [hrval, List.length_map, List.length_cons, add_comm _ 1, add_right_inj, List.length_append, List.length_take, left_eq_inf] -- lengthify the goal
            simp only [le_iff_exists_add, <- hlval, add_right_inj, exists_eq', add_assoc] -- lia
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros rule mid_i _ _
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . unfold φ at *
      obtain ⟨_, _⟩ := Hφ
      apply And.intro
      . apply ψ_holds_over_internals_impl init_i
        . assumption
        . apply existSR_single_step <;> assumption
      . assumption

end DirectRefinement

---------------------------------------------------------------------------------------------------
--------- TODO: Make a spec of unflushing?
---------------------------------------------------------------------------------------------------

inductive empty_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ q₁ q₂ q₃, empty_internal ⟨⟨[], q₃⟩, ⟨q₁, q₂⟩⟩

inductive single_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ v q₁ q₂ q₃, single_internal ⟨⟨[v], q₃⟩, ⟨q₁, q₂⟩⟩

theorem f': ∀ s₁ s₂, ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals,
  empty_internal s₁
  → rule s₁ s₂
  → single_internal s₂ :=
by
  intro ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ rule h₁ h₂ h₃
  simp [lhsModule] at h₁
  subst h₁

  cases h₂
  dsimp at h₃
  simp at h₃
  obtain ⟨_, _, _, _, _, _, _⟩ := h₃
  repeat
    cases ‹_ ∧ _›
  subst_vars
  constructor

theorem f₃: ∀ ident s₁ s₂ v,
  single_internal s₁
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → empty_internal s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ _ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- fetch the single output port ident
    simp [lhsModule] at HContains; subst HContains
    unfold lhsModule at h₂
    rw [PortMap.rw_rule_execution] at h₂
    dsimp at h₂
    simp at h₂
    repeat
      cases ‹_ ∧ _›
    subst_vars
    cases h₁
    constructor
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

---------------------------------------------------------------------------------------------------
---------
---------------------------------------------------------------------------------------------------

def φ₃ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) :=
  ψ rhs lhs ∧ empty_internal lhs

theorem f₁: ∀ ident i₁ i₂ v s₁, ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals,
  φ₃ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → ∃ s₂, rule s₁ s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ v ⟨⟨_, _⟩,⟨_, _⟩⟩ rule h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- Fetch the output rule
    simp [rhsModule] at HContains; subst HContains
    obtain ⟨hψ, h₂⟩ := h₂
    cases h₂
    dsimp [ψ] at hψ
    obtain ⟨_, _, _⟩ := hψ
    subst_vars
    -- work on h₃
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    repeat
      cases ‹_ ∧ _›
    subst_vars
    -- work on h₁
    simp [lhsModule] at h₁; subst h₁
    dsimp
    apply Exists.intro ⟨⟨_, _⟩,⟨_, _⟩⟩
    repeat
      apply Exists.intro
    simp
    and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem f'': ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁
  → single_internal s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂
  → ∃ s₂, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ ↑v s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ _ ⟨⟨_, _⟩,⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [rhsModule] at HContains; subst HContains
    unfold rhsModule at h₃; rw [PortMap.rw_rule_execution] at h₃; simp at h₃
    cases h₂
    dsimp [ψ] at h₁
    repeat
      cases ‹_ ∧ _›
    subst_vars
    unfold lhsModule
    apply Exists.intro ⟨⟨_, _⟩,⟨_, _⟩⟩
    rw [PortMap.rw_rule_execution]; dsimp
    and_intros
    . simp at *
      iterate 2 cases ‹_ ∧ _›
      and_intros
      . apply Prod.ext <;> assumption
      . rfl
    . rfl
    . rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem refines₃: rhsModule T₁ T₂ T₃ ⊑_{φ₃} lhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hψ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i

      unfold rhsModule at HContains; simp at HContains
      rcases HContains with h | h | h <;> subst_vars <;> simp
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp -- TODO: Remove this simp here
        . -- verify that the invariant holds when we flush the system
          use ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨h, _, _⟩, hₑ⟩ := Hψ
            dsimp [φ₃, ψ]
            and_intros
            . rw [<- List.append_assoc, <- List.append_assoc, h]
            . assumption
            . assumption
            . cases hₑ; constructor
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst = _ := by dsimp [reducePortMapgetIO]
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [heq.mp s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . use ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [heq.mp s]⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨_, h, _⟩, hₑ⟩ := Hψ
            subst_vars
            dsimp [φ₃, ψ]
            and_intros
            . assumption
            . rw [<- List.append_assoc, <- List.append_assoc, h]
            . rfl
            . cases hₑ; constructor
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst = _ := by dsimp [reducePortMapgetIO]
        use ⟨⟨sj2l, sj2r ++ [heq.mp s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . use ⟨⟨sj2l, sj2r ++ [heq.mp s]⟩, sj1l, sj1r⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨_, _, _⟩, hₑ⟩ := Hψ
            subst_vars
            dsimp [φ₃, ψ]
            and_intros
            . assumption
            . assumption
            . rw [<- List.append_assoc]
            . cases hₑ; constructor
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . obtain ⟨rule, h⟩: ∃ rule, rule ∈ (lhsModule T₁ T₂ T₃).internals := by simp [lhsModule]
      obtain ⟨almost_mid_s, _⟩ : ∃ almost_mid_s, rule init_s almost_mid_s := by
        apply (f₁ _ init_i i) at Hψ
        . specialize Hψ hrule
          assumption
        . assumption
      use almost_mid_s
      rw [exists_and_left]
      and_intros
      . apply existSR_single_step <;> assumption
      . unfold φ₃ at Hψ
        obtain ⟨_, _⟩ := Hψ
        have hₛ: single_internal almost_mid_s := by
          apply f' <;> assumption
        have: existSR (lhsModule T₁ T₂ T₃).internals init_s almost_mid_s := by
          apply existSR_single_step <;> assumption
        have hψ: ψ init_i almost_mid_s := by
          apply ψ_holds_over_internals_spec <;> assumption
        clear this
        have: ∃ mid_s, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd almost_mid_s ↑v mid_s := by
          apply f'' <;> assumption
        obtain ⟨mid_s, _⟩ := this
        use mid_s
        apply And.intro
        . assumption
        . unfold φ₃
          apply And.intro
          . apply outputs_preserves_ψ <;> assumption
          . apply f₃ <;> assumption
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . obtain ⟨_, _⟩ := Hψ
      . apply And.intro
        . apply ψ_holds_over_internals_impl init_i
          . assumption
          . apply existSR_single_step <;> assumption
        . assumption

---------------------------------------------------------------------------------------------------
--------------------------
---------------------------------------------------------------------------------------------------

def φ₄ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  ψ rhs lhs ∧ pf (lhsModule T₁ T₂ T₃) lhs

-- TODO: Can I use only ψ?
theorem refines₄:
  flushed (rhsModule T₁ T₂ T₃) ⊑_{φ₄} flushed (lhsModule T₁ T₂ T₃) :=
by
  have mm: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
  have sr: SimulationRelation ψ (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
  have opfm: OutputPreservesFlushability (lhsModule T₁ T₂ T₃) := by infer_instance
  unfold Module.refines_φ
  intro init_i init_s Hψ
  apply Module.comp_refines.mk
  . -- inputs rules
    intro ident mid_i v h₁
    -- TODO: This is basicall the inputability property here
    obtain ⟨s', h₂⟩ : ∃ s', ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd init_s (cast.mp v) s' := by
      apply flhs_can_always_input
      apply PortMap.rule_contains at h₁
      rw [flushed_preserves_ports] at h₁
      rwa [@match_interface_inputs_contains _ _ _ _ (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃)] at h₁
    use s', s'
    apply And.intro
    . assumption
    . apply And.intro
      . apply existSR_reflexive
      . unfold φ₄; apply And.intro
        . rw [PortMap.rw_rule_execution (flushed_inputs_are_rflushed _ _)] at h₁
          rw [PortMap.rw_rule_execution (flushed_inputs_are_rflushed _ _)] at h₂
          obtain ⟨s₁, _, h₁⟩ := h₁
          obtain ⟨s₂, _, h₂⟩ := h₂
          obtain ⟨_, _⟩ := Hψ -- TODO: This can be removed if we go down to ψ instead of φ₄
          apply flushesTo_implies_reachable at h₁
          apply flushesTo_implies_reachable at h₂
          simp at *
          have: ψ s₁ s₂ := by
            apply sr.inputs_preserved _ init_i _ _ init_s _ <;> simpa
          apply sr.internals_preserved <;> simpa
        . apply flushed_modules_has_flushed_states <;> assumption
  . -- outputs rules
    intro ident mid_i v h₁
    use init_s
    rw [exists_and_left]
    apply And.intro
    . apply existSR_reflexive
    . obtain ⟨_, _⟩ := Hψ
      obtain ⟨s', _⟩: ∃ s', ((flushed (lhsModule T₁ T₂ T₃)).outputs.getIO ident).snd init_s (cast'.mp v) s' := by
        have: at_least_single_internal init_s := by
          apply f₆ <;> assumption
        dsimp [flushed] at *
        apply f₅ <;> assumption
      use s'
      apply And.intro
      . assumption
      . dsimp [flushed] at *
        unfold φ₄; apply And.intro
        . apply sr.outputs_preserved <;> assumption
        . apply opfm.rule <;> assumption
  . --internal rules
    intros _ mid_i h₁ _
    dsimp [flushed] at *
    use init_s
    apply And.intro
    . apply existSR_reflexive
    . obtain ⟨_, _⟩ := Hψ
      apply And.intro
      . contradiction
      . assumption

end Graphiti.JoinRewrite
