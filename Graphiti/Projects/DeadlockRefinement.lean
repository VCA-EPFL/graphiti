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

open Batteries (AssocList)

namespace Graphiti

  variable {Ident S : Type} [DecidableEq Ident] (m : Module Ident S)

  -- m with an ε-transition.
  -- In terms of trace semantics, the empty trace is valid for m1, but not
  -- necessarily for m
  @[drcomponents]
  def m1 : Module Ident S :=
    {
      inputs := m.inputs,
      outputs := m.outputs,
      internals := (λ s s' => s = s') :: m.internals,
      init_state := m.init_state,
    }

  instance : MatchInterface (m1 m) m := by
    apply MatchInterface_simpler
    <;> intros _ <;> rfl

  instance : MatchInterface m (m1 m) := by
    apply MatchInterface_simpler
    <;> intros _ <;> rfl

  def φ1 (i s : S) : Prop := i = s

  theorem φ1_initial : Module.refines_initial (m1 m) m φ1 := by
    intro i _; exists i

  theorem φ1_initial' : Module.refines_initial m (m1 m) φ1 := by
    intro i _; exists i

  theorem refines_ϕ1 : (m1 m) ⊑_{φ1} m := by
    intro i s hphi
    <;> subst i
    constructor
    · intro ident mid_i v hrule
      exists mid_i, mid_i
      and_intros
      · dsimp [drcomponents] at hrule; exact hrule
      · constructor
      · rfl
    · intro ident mid_i v hrule
      exists s, mid_i
      and_intros
      · constructor
      · dsimp [drcomponents] at hrule; exact hrule
      · rfl
    · intro rule mid_i hrule1 hrule2
      simp [drcomponents] at hrule1
      exists mid_i
      and_intros
      · cases hrule1
        · subst rule; subst s; constructor
        · rename_i hrule1
          exact existSR.step _ _ _ _ hrule1 hrule2 (by constructor)
      · rfl

  theorem refines_ϕ1' : m ⊑_{φ1} (m1 m) := by
    intro i s hphi
    <;> subst i
    constructor
    · intro ident mid_i v hrule
      exists mid_i, mid_i
      and_intros
      · dsimp [drcomponents]; exact hrule
      · constructor
      · rfl
    · intro ident mid_i v hrule
      exists s, mid_i
      and_intros
      · constructor
      · dsimp [drcomponents]; exact hrule
      · rfl
    · intro rule mid_i hrule1 hrule2
      simp [drcomponents] at hrule1
      exists mid_i
      and_intros
      · apply existSR.step
        · dsimp [drcomponents]; right; exact hrule1
        · exact hrule2
        · constructor
      · rfl

  @[drcomponents]
  def m2 : Module Ident (S × Bool) :=
    {
      inputs := m.inputs.mapVal (λ _ r => ⟨r.1, λ s v s' => r.2 s.1 v s'.1⟩)
      outputs := m.outputs.mapVal (λ _ r => ⟨r.1, λ s v s' => r.2 s.1 v s'.1 ∧ s.2 = false⟩),
      internals := (λ s s' => s.1 = s'.1 ∧ s'.2 = true) :: m.internals.map (λ r => λ s s' => r s.1 s'.1 ∧ s.2 = s'.2),
      init_state := (λ s => m.init_state s.1 ∧ s.2 = false),
    }

  instance : MatchInterface (m2 m) m := by
    apply MatchInterface_simpler
    <;> intros _
    <;> dsimp [drcomponents]
    <;> rw [AssocList.mapVal_mapVal]

  instance : MatchInterface m (m2 m) := by
    apply MatchInterface_simpler
    <;> intros _
    <;> dsimp [drcomponents]
    <;> rw [AssocList.mapVal_mapVal]

  def φ2 (i : S × Bool) (s : S) : Prop := i.1 = s

  def φ2' (i : S) (s : S × Bool) : Prop := i = s.1

  theorem φ2_initial : Module.refines_initial (m2 m) m φ2 := by
    intro i h; exists i.1; and_intros
    · dsimp [drcomponents] at h; obtain ⟨hf, _⟩ := h; exact hf
    · rfl

  theorem φ2_initial' : Module.refines_initial m (m2 m) φ2' := by
    intro i h; exists (i, false); and_intros

  theorem refines_ϕ2 : (m2 m) ⊑_{φ2} m := by
    intro i s hphi
    subst s
    constructor
    · intro ident mid_i v hrule
      exists mid_i.1, mid_i.1
      and_intros
      · dsimp [drcomponents] at hrule
        sorry
      · constructor
      · rfl
    · intro ident mid_i v hrule
      sorry
    · intro rule mid_i hrule1 hrule2
      exists mid_i.1
      and_intros
      · -- Two cases:
        -- · The internal rule is the deadlocking one.
        -- It does not modify m.1, we are ok.
        -- · The interal rule is almost the same as an i.1 state
        sorry
      · rfl

end Graphiti
