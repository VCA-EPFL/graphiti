/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.ModuleLemmas
public import Graphiti.Core.StateTransition

@[expose] public section

namespace Graphiti

inductive IOEvent (Ident : Type _) : Type _ where
| input : InternalPort Ident → (Σ (T : Type _), T) → IOEvent Ident
| output : InternalPort Ident → (Σ (T : Type _), T) → IOEvent Ident

@[simp] abbrev Trace Ident := List (IOEvent Ident)

namespace Module

section StateTransition

variable (Ident : Type _)
variable [DecidableEq Ident]
variable (S : Type _)

structure State where
  state : S
  module : Module Ident S

variable {Ident} {S}

inductive step : State Ident S → Trace Ident → State Ident S → Prop where
| input {st ident s' v v'} :
  (st.module.inputs.getIO ident).snd st.state v s' →
  v' = ⟨(st.module.inputs.getIO ident).fst, v⟩ →
  step st [.input ident v'] ⟨s', st.module⟩
| output {st ident s' v v'} :
  (st.module.outputs.getIO ident).snd st.state v s' →
  v' = ⟨(st.module.outputs.getIO ident).fst, v⟩ →
  step st [.output ident v'] ⟨s', st.module⟩
| internal {st r s'} :
  r ∈ st.module.internals →
  r st.state s' →
  step st [] ⟨s', st.module⟩

def state_transition (m : Module Ident S) : StateTransition (State Ident S) (IOEvent Ident) where
  init := fun s => m.init_state s.state ∧ s.module = m
  step := step

theorem existSR_implies_empty_steps {m : Module Ident S} {s1 s2} :
  existSR m.internals s1 s2 →
  @star _ _ (state_transition m) ⟨s1, m⟩ [] ⟨s2, m⟩ := by
  intro h
  induction h with
  | done => apply @star.refl _ _ (state_transition m)
  | step init mid final rule hin hrule hexists ih =>
    rw [show [] = [] ++ [] by rfl]
    apply @star.step _ _ (state_transition m)
    rotate_left; apply ih
    constructor <;> assumption

end StateTransition

section TraceInclusion

variable {Ident : Type _}
variable [DecidableEq Ident]
variable {S I : Type _}
variable (imp : Module Ident I)
variable (spec : Module Ident S)

def imp_behaviour := @behaviour _ _ (state_transition imp)

def spec_behaviour := @behaviour _ _ (state_transition spec)

def trace_inclusion : Prop :=
  ∀ l, imp_behaviour imp l → spec_behaviour spec l

section Refinement

variable [mm : MatchInterface imp spec]

theorem refines_implies_step_preservation {φ} :
  imp ⊑_{φ} spec →
  ∀ i s i' e,
    φ i s →
    (state_transition imp).step ⟨i, imp⟩ e i' →
    ∃ s',
      @star _ _ (state_transition spec) ⟨s, spec⟩ e s'
      ∧ φ i'.state s'.state := by
  intros href i s i' e hphi hstep
  cases hstep with
  | @input ident i' v v' step =>
    subst v'
    dsimp at *; dsimp at v
    rcases href _ _ hphi with ⟨inp, out, int⟩; clear href out int
    obtain ⟨s1, s2, h1, h2, h3⟩ := inp ident i' v step; clear inp
    exists ⟨s2, spec⟩
    and_intros
    · rw [show [IOEvent.input ident ⟨(imp.inputs.getIO ident).fst, v⟩] = [IOEvent.input ident ⟨(imp.inputs.getIO ident).fst, v⟩] ++ [] by rfl]
      apply @star.trans_star _ _ (state_transition spec)
      · apply @star.plus_one _ _ (state_transition spec)
        constructor
        · apply h1
        · simp; apply MatchInterface.input_types
      · apply existSR_implies_empty_steps; assumption
    · assumption
  | @output ident i' v v' step =>
    subst v'
    dsimp at *; dsimp at v
    rcases href _ _ hphi with ⟨inp, out, int⟩; clear href inp int
    obtain ⟨s1, s2, h1, h2, h3⟩ := out ident i' v step; clear out
    exists ⟨s2, spec⟩
    and_intros
    · rw [show [IOEvent.output ident ⟨(imp.outputs.getIO ident).fst, v⟩] = [] ++ [IOEvent.output ident ⟨(imp.outputs.getIO ident).fst, v⟩] by rfl]
      apply @star.trans_star _ _ (state_transition spec)
      · apply existSR_implies_empty_steps; assumption
      · apply @star.plus_one _ _ (state_transition spec)
        constructor
        · apply h2
        · simp; apply MatchInterface.output_types
    · assumption
  | @internal r i' hin hrule =>
    dsimp at *
    rcases href _ _ hphi with ⟨inp, out, int⟩; clear href inp out
    obtain ⟨s1, h1, h2⟩ := int r i' hin hrule; clear int
    exists ⟨s1, spec⟩
    and_intros
    · apply existSR_implies_empty_steps <;> assumption
    · assumption

theorem step_preserve_mod {i1 e i2} (h : (state_transition imp).step i1 e i2) :
  i2.module = i1.module := by
    obtain ⟨_, _⟩ := i1; cases h <;> rfl

theorem steps_preserve_mod {i1 e i2} (h : @star _ _ (state_transition imp) i1 e i2) :
  i2.module = i1.module := by
    induction h with
    | refl => rfl
    | step i1 i2 i3 ei1 ei2 Hi1 Hi2 HR => rw [HR]; exact step_preserve_mod _ Hi1

theorem refines_implies_star_preservation {φ} :
  imp ⊑_{φ} spec →
  ∀ i s i' e,
    @star _ _ (state_transition imp) i e i' →
    i.module = imp →
    φ i.state s →
    ∃ s',
      @star _ _ (state_transition spec) ⟨s, spec⟩ e s'
      ∧ φ i'.state s'.state := by
  intro href i s i' e hstar hmod hphi
  induction hstar generalizing s with
  | refl =>
    exists ⟨s, spec⟩; and_intros
    · apply @star.refl _ _ (state_transition spec)
    · assumption
  | step i1 i2 i3 ei1 ei2 Hi1 Hi2 HR =>
    have hblee :
      (state_transition imp).step ⟨i1.state, imp⟩ ei1 i2 := by
        obtain ⟨_, _⟩ := i1; dsimp at *; subst imp; exact Hi1
    obtain ⟨s2, Hs2, Hs2phi⟩ :=
      refines_implies_step_preservation _ _ href i1.state s i2 ei1 hphi hblee
    have Hi2imp := step_preserve_mod _ hblee
    obtain ⟨s3, Hs3, Hs3phi⟩ := HR s2.state Hi2imp Hs2phi
    exists s3
    and_intros <;> try assumption
    apply @star.trans_star _ _ (state_transition spec) _ _ _ _ _ Hs2
    have hs2 : s2 = ⟨s2.state, spec⟩ := by
      cases s2; dsimp; congr; exact steps_preserve_mod _ Hs2
    rwa [hs2]

end Refinement

theorem refines_implies_trace_inclusion :
  imp ⊑ spec →
  trace_inclusion imp spec := by
    intro ⟨mm, φ, H1, H2⟩ l ⟨i1, i2, ⟨Hi1_init, Hi1_mod⟩, Hi2⟩
    obtain ⟨s1, Hs1_init, Hs1_φ⟩ := H2 i1.state Hi1_init
    exists ⟨s1, spec⟩
    obtain ⟨s2, Hs2_1, Hs2_2⟩ :=
      refines_implies_star_preservation _ _ H1 i1 s1 i2 l Hi2 Hi1_mod Hs1_φ
    exists s2

end TraceInclusion

end Module

end Graphiti
