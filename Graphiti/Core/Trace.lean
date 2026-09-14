/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Graph.ModuleLemmas
public import Graphiti.Core.StateTransition

@[expose] public section

namespace Graphiti

inductive IOEvent (Ident : Type _) : Type _ where
| input : InternalPort Ident → (Σ (T : Type*), T) → IOEvent Ident
| output : InternalPort Ident → (Σ (T : Type*), T) → IOEvent Ident

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
  | step _ _ _ _ hin hrule _ ih =>
    simpa using @star.step _ _ (state_transition m) _ _ _ [] [] (by constructor <;> assumption) ih

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

/-- A step followed by internal steps of `m` is a trace of `m`. -/
private theorem star_step_existSR {m : Module Ident S} {st e s1 s2} :
    (state_transition m).step st e ⟨s1, m⟩ → existSR m.internals s1 s2 →
    @star _ _ (state_transition m) st e ⟨s2, m⟩ := by
  intro h1 h2
  simpa using @star.trans_star _ _ (state_transition m) _ _ _ _ []
    (@star.plus_one _ _ (state_transition m) _ _ _ h1) (existSR_implies_empty_steps h2)

/-- Internal steps of `m` followed by a step is a trace of `m`. -/
private theorem star_existSR_step {m : Module Ident S} {s s1 e st} :
    existSR m.internals s s1 → (state_transition m).step ⟨s1, m⟩ e st →
    @star _ _ (state_transition m) ⟨s, m⟩ e st := by
  intro h1 h2
  simpa using @star.trans_star _ _ (state_transition m) _ _ _ [] _
    (existSR_implies_empty_steps h1) (@star.plus_one _ _ (state_transition m) _ _ _ h2)

private theorem sigma_mk_mp {α β : Type _} (h : α = β) (v : α) : (⟨α, v⟩ : Σ T, T) = ⟨β, h.mp v⟩ := by
  subst h; rfl

theorem refines_implies_step_preservation {φ} :
  imp ⊑_{φ} spec →
  ∀ i s i' e,
    φ i s →
    (state_transition imp).step ⟨i, imp⟩ e i' →
    ∃ s',
      @star _ _ (state_transition spec) ⟨s, spec⟩ e s'
      ∧ φ i'.state s'.state := by
  intro href i s i' e hphi hstep
  have hr := href _ _ hphi
  cases hstep with
  | @input ident _ v _ hstep h =>
    obtain ⟨s1, s2, h1, h2, h3⟩ := hr.inputs _ _ _ hstep
    have := star_step_existSR (step.input (st := ⟨s, spec⟩) h1 (sigma_mk_mp _ v)) h2
    grind
  | @output ident _ v _ hstep h =>
    obtain ⟨s1, s2, h1, h2, h3⟩ := hr.outputs _ _ _ hstep
    have := star_existSR_step h1 (step.output (st := ⟨s1, spec⟩) h2 (sigma_mk_mp _ v))
    grind
  | internal hin hrule =>
    obtain ⟨s1, h1, h2⟩ := hr.internals _ _ hin hrule
    have := existSR_implies_empty_steps h1
    grind

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
    have := @star.refl _ _ (state_transition spec) ⟨s, spec⟩
    grind
  | step i1 i2 i3 e1 e2 hstep _ ih =>
    obtain ⟨i1, _⟩ := i1; subst hmod
    obtain ⟨⟨s2, m2⟩, hs2, hphi2⟩ := refines_implies_step_preservation _ _ href i1 s i2 e1 hphi hstep
    obtain rfl : spec = m2 := (steps_preserve_mod _ hs2).symm
    obtain ⟨s3, hs3, hphi3⟩ := ih s2 (step_preserve_mod _ hstep) hphi2
    have := @star.trans_star _ _ (state_transition spec) _ _ _ _ _ hs2 hs3
    grind

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
