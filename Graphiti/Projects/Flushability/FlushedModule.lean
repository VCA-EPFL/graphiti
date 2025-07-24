/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Mathlib.Tactic

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas

import Graphiti.Projects.Flushability.ConfluentModule
import Graphiti.Projects.Flushability.RuleSwapping
import Graphiti.Projects.Flushability.DeterministicModule
import Graphiti.Projects.Flushability.SimulationRelation
import Graphiti.Projects.Flushability.Outputability

-- TODO: Move this to a more global file
@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

-- TODO: Move this to a more global file
theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

namespace Graphiti

variable {Ident S : Type _}

section Flushability

def pf (mod: Module Ident S) (s: S): Prop :=
  ∀ r ∈ mod.internals, ∀ s', ¬ r s s'

--TODO: Make it a structure?
inductive flushesTo: (Module Ident S) → S → S → Prop where
| mk: ∀ mod s₁ s₂,
  existSR mod.internals s₁ s₂
  → pf mod s₂
  → flushesTo mod s₁ s₂

def flushable (mod: Module Ident S) (s: S): Prop :=
  ∃ s', flushesTo mod s s'

class Flushable (mod: Module Ident S): Prop where
 flushable: ∀ s, flushable mod s

-- TODO: Add notations here

end Flushability

section FlushedModules

def rflushed (mod: Module Ident S) (rule: RelIO S): RelIO S :=
  ⟨rule.1 , λ s ret s'' => ∃ s', rule.2 s ret s' ∧ flushesTo mod s' s''⟩

def isflushed (mod: Module Ident S) :=
  mod.init_state
  --λ s => ∃ s', mod.init_state s ∧ flushesTo mod s s' (Wrong definition, s itself is not flushed)
  --λ s => ∃ s', mod.init_state s' ∧ flushesTo mod s' s
  --λ s => mod.init_state s ∧ pf mod s
  --λ s => mod.init_state s ∧ flushable mod s

-- TODO: Should we make internal rules instead be a single rule using the flushesTo relation?
-- TODO: Should we make the output rules flush too?
-- TODO: With all of these changes, should we make a hierarchy of flushes modules (weaker and stronger than the above definition)?
def flushed (mod: Module Ident S): Module Ident S :=
  {
    inputs     := mod.inputs.mapVal (λ _ v => rflushed mod v) -- transform all the rules to flushed rules
    internals  := []                                          -- no more internal rules, inputs takes up the role of internals
    outputs    := mod.outputs                                 -- output rules remains unchanges
    init_state := isflushed mod                                -- Make sure the initial state is also flushed (use `iflushed`?)
  }

end FlushedModules

section MatchInterface

variable {mod: Module Ident S}

theorem preserves_input_types:
  (flushed mod).inputs.mapVal (λ _ v => Sigma.fst v) = mod.inputs.mapVal (λ _ v => Sigma.fst v) :=
by
  rw [flushed, Batteries.AssocList.mapVal_mapVal]
  dsimp [rflushed]

theorem flushed_preserves_outputs:
  (flushed mod).outputs = mod.outputs :=
by
  rfl

variable [DecidableEq Ident]

theorem flushed_preserves_input_over_getIO:
  ∀ {ident}, ((flushed mod).inputs.getIO ident).fst = (mod.inputs.getIO ident).fst :=
by
  intro ident
  unfold PortMap.getIO
  iterate 2 rw [<- Option.getD_map Sigma.fst]
  iterate 2 rw [Batteries.AssocList.find?_map_comm]
  rw [preserves_input_types]

theorem flushed_preserves_input_over_getIO':
  ∀ {ident}, (mod.inputs.getIO ident).fst = ((flushed mod).inputs.getIO ident).fst :=
by
  intro; symm; apply flushed_preserves_input_over_getIO

theorem flushed_preserves_ports:
  ∀ ident, (flushed mod).inputs.contains ident ↔ mod.inputs.contains ident :=
by
  intro ident
  dsimp [flushed]
  cases mod.inputs with
  | nil => simp [Batteries.AssocList.mapVal]
  | cons k hd tl =>
      dsimp [Batteries.AssocList.mapVal, Batteries.AssocList.contains, Batteries.AssocList.any] at *
      by_cases h: k = ident
      . subst h; simp
      . have: (k == ident) = false := decide_eq_false h
        simp [this]

instance: MatchInterface (flushed mod) mod := by
  rw [MatchInterface_simpler_iff]
  rw [preserves_input_types, flushed_preserves_outputs]
  intros <;> and_intros <;> rfl

instance: MatchInterface mod (flushed mod) := by
  haveI: MatchInterface (flushed mod) mod := by infer_instance
  apply MatchInterface_symmetric <;> assumption

omit S mod in -- TODO: Looks like this omit is a noop
instance {S₁ S₂: Type _} (mod₁: Module Ident S₁) (mod₂: Module Ident S₂) [MatchInterface mod₁ mod₂]: MatchInterface (flushed mod₁) (flushed mod₂) := by
  have: MatchInterface (flushed mod₁) mod₁ := by infer_instance
  have: MatchInterface mod₂ (flushed mod₂) := by infer_instance
  have: MatchInterface mod₁ (flushed mod₂) := by
    apply MatchInterface_transitive <;> assumption
  apply MatchInterface_transitive <;> assumption

end MatchInterface

section FlushabilityLemmas

variable {mod: Module Ident S}

theorem everystate_is_pf_in_flushed:
  ∀ s, pf (flushed mod) s :=
by
  simp [pf, flushed]

theorem pf_is_terminal:
  ∀ s₁ s₂, pf mod s₁ → existSR mod.internals s₁ s₂ → s₁ = s₂ :=
by
  intro s₁ s₂ h₁ h₂
  cases h₂ with
  | done => rfl
  | step _ mid _ rule h₃ =>
    specialize h₁ rule h₃ mid
    contradiction

lemma flushesTo_implies_pf:
  ∀ s₁ {s₂}, flushesTo mod s₁ s₂ → pf mod s₂ :=
by
  intro _ _ h
  cases h
  assumption

lemma flushesTo_implies_reachable:
  ∀ {s₁} {s₂}, flushesTo mod s₁ s₂ → existSR mod.internals s₁ s₂ :=
by
  intro _ _ h
  cases h
  assumption

lemma flushesTo_implies_flushable:
  ∀ {s₁} {s₂}, flushesTo mod s₁ s₂ → flushable mod s₁ :=
by
  sorry

theorem flushesTo_reflexive:
  ∀ {s}, pf mod s → flushesTo mod s s :=
by
  intro s h
  constructor
  . apply existSR_reflexive
  . exact h

theorem flushesTo_transitive:
  ∀ {s₁} s₂ {s₃}, flushesTo mod s₁ s₂ → flushesTo mod s₂ s₃ → flushesTo mod s₁ s₃ :=
by
  intro s₁ s₂ s₃ h₁ h₂
  constructor
  . apply flushesTo_implies_reachable at h₁
    apply flushesTo_implies_reachable at h₂
    apply existSR_transitive
    . exact h₁
    . exact h₂
  . apply flushesTo_implies_pf
    exact h₂

theorem flushesTo_antisymmetric:
  ∀ s₁ s₂, flushesTo mod s₁ s₂ → flushesTo mod s₂ s₁ → s₁ = s₂ :=
by
  intro s₁ s₂ h₁ h₂
  have: pf mod s₁ := by apply flushesTo_implies_pf <;> assumption
  apply pf_is_terminal at this
  apply flushesTo_implies_reachable at h₁
  apply this
  assumption

theorem pf_is_flushable:
  ∀ s, pf mod s → flushable mod s :=
by
  intro s h
  use s
  exact flushesTo_reflexive h

instance: Flushable (flushed mod) := {
  flushable := by
    dsimp [flushable]
    intro s <;> use s
    apply flushesTo_reflexive
    apply everystate_is_pf_in_flushed
}

end FlushabilityLemmas

section FlushableModules

variable {S₁ S₂: Type _}
variable (mod₁: Module Ident S₁) (mod₂: Module Ident S₂)
variable [DecidableEq Ident]
variable [fl₁: Flushable mod₁] [fl₂: Flushable mod₂]

def φ₁ (s₁: S₁)(s₂: S₂): Prop := pf mod₁ s₁ ∧ pf mod₂ s₂

instance [MatchInterface mod₁ mod₂]: WeakSimulationRelation (φ₁ mod₁ mod₂) mod₁ mod₂ := {
  inputs_preserved := by
    intro ident i₁ i₂ v s₁ s₂
    obtain ⟨i₃, hi₃⟩ := fl₁.flushable i₂
    obtain ⟨s₃, hs₃⟩ := fl₂.flushable s₂
    use i₃, s₃
    intros
    and_intros
    . apply flushesTo_implies_pf <;> assumption
    . apply flushesTo_implies_pf <;> assumption
  internals_preserved := by
    intros i₁ s₁
    obtain ⟨i₂, hi₂⟩ := fl₁.flushable i₁
    obtain ⟨s₂, hs₂⟩ := fl₂.flushable s₁
    use i₂, s₂
    intros
    and_intros
    . apply flushesTo_implies_pf <;> assumption
    . apply flushesTo_implies_pf <;> assumption
  outputs_preserved := by
    intro ident i₁ i₂ v s₁ s₂
    obtain ⟨i₃, hi₃⟩ := fl₁.flushable i₂
    obtain ⟨s₃, hs₃⟩ := fl₂.flushable s₂
    use i₃, s₃
    intros
    and_intros
    . apply flushesTo_implies_pf <;> assumption
    . apply flushesTo_implies_pf <;> assumption
  initial_state_preserves := by
    sorry -- Wellformness of the module should solve this
}

end FlushableModules

section QuasiConfluentModules

variable [DecidableEq Ident]
variable {mod: Module Ident S}
variable [qc: QuasiConfluent mod]

-- TODO: Can I weaken the requirements to only need LocalConfluence?
theorem newrule:
  ∀ s₁ s₂ s₃, existSR mod.internals s₁ s₂ → flushesTo mod s₁ s₃ → flushesTo mod s₂ s₃ :=
by
  intro _ _ s₃ h₁ h₂
  obtain ⟨h₂, g⟩ := h₂
  constructor
  . induction h₁ with
    | done => assumption
    | step _ mid _ rule h₃ _ _ ih =>
      apply ih <;> clear ih
      have: ∃ s₄, existSR mod.internals mid s₄ ∧ existSR mod.internals s₃ s₄ := by
        apply qc.internals <;> assumption
      obtain ⟨s₄, _, _⟩ := this
      have: s₃ = s₄ := by
        apply pf_is_terminal <;> assumption
      subst this
      assumption
  . assumption

-- TODO: This is basically a rewritting of the newrule
theorem flushable_reached_from_flushable:
  ∀ s₁ s₂, flushable mod s₁ → existSR mod.internals s₁ s₂ → flushable mod s₂ :=
by
  intros s₁ s₂ h₁ h₂
  obtain ⟨s₃, _⟩ := h₁
  use s₃
  apply newrule <;> assumption

end QuasiConfluentModules

section GloballyConfluentModules

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable {mod: Module Ident S}
variable [gc: GloballyConfluent mod]

-- TODO: Can we reduce it to quasi/locally-confluent?
theorem flushed_is_unique:
  ∀ s, flushable mod s → ∃! s', flushesTo mod s s' :=
by
  intro s h
  obtain ⟨s₂, h₁⟩ := h
  use s₂ <;> dsimp
  and_intros
  . assumption
  . intro y h₂
    have: pf mod s₂ := by apply flushesTo_implies_pf at h₁ <;> assumption
    have: pf mod y := by apply flushesTo_implies_pf at h₂ <;> assumption
    apply flushesTo_implies_reachable at h₁
    apply flushesTo_implies_reachable at h₂
    obtain ⟨w, _, _⟩ := gc.internals s s₂ y h₁ h₂
    have: s₂ = w := by apply pf_is_terminal <;> assumption
    subst this
    apply pf_is_terminal <;> assumption

end GloballyConfluentModules

section
  variable (mod: Module Ident S)
  variable [DecidableEq Ident]

-- TODO: Find a better name
theorem flushed_inputs_are_rflushed: ∀ ident,
  (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) :=
by
  intros ident
  dsimp [flushed, rflushed, PortMap.getIO]
  rw [Batteries.AssocList.find?_mapVal]
  by_cases h: mod.inputs.contains ident
  . rw [<- Batteries.AssocList.contains_find?_iff] at h
    obtain ⟨_, h⟩ := h; rw [h]
    dsimp only [Option.map_some, Option.getD_some]
  . apply Batteries.AssocList.contains_none at h
    rw [h]; dsimp
    simp only [false_and, exists_false]

-- TODO: LocalConfluence should be enough here if newrule holds with local confluence
theorem flushed_reachable_from_nonflushed [lc: QuasiConfluent mod] : ∀ ident s₁ v s₂ s₃,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₃
  → (mod.inputs.getIO ident).snd s₁ (flushed_preserves_input_over_getIO.mp v) s₂
  → existSR mod.internals s₂ s₃ :=
by
  intro ident s₁ v s₂ s₃ h₁ h₂
  have := flushed_inputs_are_rflushed mod ident
  rw [sigma_rw this] at h₁
  dsimp [rflushed] at h₁
  obtain ⟨w, _, _, _⟩ := h₁
  have: ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals w s₄ := by
    apply lc.inputs <;> assumption
  obtain ⟨s₄, _, _⟩ := this
  have: existSR mod.internals s₄ s₃ := by
    have: flushesTo mod w s₃ := by
      constructor <;> assumption
    have: flushesTo mod s₄ s₃ := by
      apply newrule <;> assumption
    obtain ⟨_, _⟩ := this
    assumption
  apply existSR_transitive <;> assumption

theorem flushed_modules_has_flushed_states: ∀ ident s₁ v s₂,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₂ → pf mod s₂ :=
by
  intro ident _ _ _ h
  have HContains: (flushed mod).inputs.contains ident := by
    apply PortMap.rule_contains <;> assumption
  simp only [flushed_preserves_ports] at HContains
  have: ∃ mrule, mod.inputs.find? ident = some mrule := by
    rw [Batteries.AssocList.contains_find?_iff] <;> assumption
  obtain ⟨_, h₂⟩ := this
  apply PortMap.getIO_some at h₂
  subst h₂
  have: (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) := by
    apply flushed_inputs_are_rflushed <;> assumption
  clear HContains
  rw [sigma_rw (by assumption)] at h
  dsimp [rflushed] at h
  obtain ⟨_, _, _, _⟩ := h
  assumption

end

section Idempotence

variable {mod: Module Ident S}

theorem rflushed_idempotent:
  ∀ rule, rflushed mod (rflushed mod rule) = rflushed mod rule :=
by
  intros
  simp [rflushed]
  funext s ret s''
  apply propext
  constructor
  . intro ⟨_, ⟨w, _, _⟩, _⟩
    use w
    and_intros
    . assumption
    . apply flushesTo_transitive <;> assumption
  . intro ⟨w, _⟩
    use s''
    and_intros
    . use w
    . apply flushesTo_reflexive
      apply flushesTo_implies_pf
      cases ‹_ ∧ _›
      assumption

theorem findaname:
  ∀ s₁ s₂, flushesTo (flushed mod) s₁ s₂ → s₁ = s₂ :=
by
  intros _ _ h
  obtain ⟨h, _⟩ := h
  -- TODO: Make this a lemma, that in a flushed module, nothing is reachable
  dsimp [flushed] at h
  apply existSR_norules
  assumption

private theorem rflushed_idempotent':
  ∀ rule, rflushed (flushed mod) (rflushed mod rule) = rflushed mod rule :=
by
  intros
  rw (occs := .pos [1])[rflushed]
  rw (occs := .pos [4])[rflushed]
  congr
  funext s ret s''
  apply propext
  constructor
  . intro ⟨s', h₁, h₂⟩
    obtain ⟨w, _, _⟩ :=  h₁
    use w
    and_intros
    . assumption
    . apply findaname at h₂
      rwa [← h₂]
  . intro ⟨s', h₁, h₂⟩
    dsimp [rflushed]
    use s''
    and_intros
    . use s'
    . apply flushesTo_reflexive
      apply everystate_is_pf_in_flushed

theorem flushed_idempotent:
  flushed (flushed mod) = flushed mod :=
by
  -- TODO: Why can't I merge both rw by giving both positions to the first one? Bug in the tactic?
  rw (occs := .pos [1]) [flushed]
  rw (occs := .pos [5]) [flushed]
  ext
  . dsimp
    rw (occs := .pos [2]) [flushed] <;> dsimp
    rw [Batteries.AssocList.mapVal_mapVal]
    congr <;> funext _ rule
    exact rflushed_idempotent' rule
  . dsimp [flushed]
  . dsimp [flushed] <;> rfl -- TODO: Why do we have this form in the goal. What did ext do?
  . dsimp [flushed]
    sorry -- This doesn't hold at the moment

end Idempotence

section Confluence

-- TODO: Can we derive the confluence properties of a flushed module from the confluence properties
--       of the underlying module?

end Confluence

section Determinism

variable {mod: Module Ident S}
variable [DecidableEq Ident]

instance: DeterministicInternals (flushed mod) := {
  internal_deterministic := by
    intros
    dsimp [flushed] at *
    contradiction
}

instance [dt: DeterministicOutputs mod]: DeterministicOutputs (flushed mod) := {
  output_deterministic := by
    intros
    dsimp [flushed] at *
    apply dt.output_deterministic <;> assumption
}

instance [dt: DeterministicInputs mod] [gc: GloballyConfluent mod]: DeterministicInputs (flushed mod) := {
  input_deterministic := by
    intros ident s₁ v s₂ s₃ h₁ h₂
    rw [sigma_rw (flushed_inputs_are_rflushed _ _)] at *
    obtain ⟨w₁, _, h₁⟩ := h₁
    obtain ⟨w₂, _, h₂⟩ := h₂
    have: w₁ = w₂ := by apply dt.input_deterministic <;> assumption
    subst this
    have := by apply flushesTo_implies_flushable at h₁ <;> assumption
    apply flushed_is_unique at this
    obtain ⟨w, _, h⟩ := this
    have := by apply h s₃ <;> assumption
    subst this
    apply h
    exact h₁
}

-- TODO: This should be derived from above
instance [DeterministicInputs mod] [DeterministicOutputs mod] [GloballyConfluent mod]: Deterministic (flushed mod) := by infer_instance

-- TODO: Is this actually correct to have?
instance [Deterministic (flushed mod)]: Deterministic mod := {
  input_deterministic    := sorry
  internal_deterministic := sorry
  output_deterministic   := sorry
}

end Determinism

section SimulationRelation

variable [DecidableEq Ident]
variable {S₁ S₂: Type _}
variable {mod₁: Module Ident S₁}
variable {mod₂: Module Ident S₂}
variable {φ: S₁ → S₂ → Prop}
variable [MatchInterface mod₁ mod₂]

instance [sr: SimulationRelation φ mod₁ mod₂]: SimulationRelation φ (flushed mod₁) (flushed mod₂) := {
  inputs_preserved    := by
    intros ident i₁ i₂ v s₁ s₂ h₁ h₂ h₃
    rw [sigma_rw (flushed_inputs_are_rflushed _ _)] at h₂
    rw [sigma_rw (flushed_inputs_are_rflushed _ _)] at h₃
    obtain ⟨w₁, _, _, _⟩ := h₂
    obtain ⟨w₂, _, _, _⟩ := h₃
    simp at *
    have: φ w₁ w₂ := by
      apply sr.inputs_preserved <;> simpa
    apply sr.internals_preserved <;> assumption
  internals_preserved := by
    intros i₁ i₂ s₁ s₂ h₁ h₂ h₃
    dsimp [flushed] at h₂ h₃
    apply existSR_norules at h₂ <;> subst h₂
    apply existSR_norules at h₃ <;> subst h₃
    exact h₁
  outputs_preserved   := by
    intros ident i₁ i₂ v s₁ s₂ h₁ h₂ h₃
    dsimp [flushed] at h₂ h₃
    apply sr.outputs_preserved <;> assumption
  initial_state_preserves := by
    intros i s h₁ h₂
    dsimp [flushed, isflushed] at *
    apply sr.initial_state_preserves <;> assumption
}

-- TODO: pf mod s is a (weak) simulation relation between any two flushable modules
--       A weak simulation relation allows arbitrary operations after inputing and outputing and in the initial states
end SimulationRelation

section Lemmas

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable (mod: Module Ident S)

lemma m_imp_fm [f: Flushable mod] : ∀ ident s₁ v s₂,
  (mod.inputs.getIO ident).snd s₁ v s₂
  → ∃ s₃, ((flushed mod).inputs.getIO ident).snd s₁ (flushed_preserves_input_over_getIO'.mp v) s₃ :=
by
  intros ident _ _ s₂ _
  obtain ⟨s₃, _⟩ := f.flushable s₂
  use s₃
  have := flushed_inputs_are_rflushed mod ident
  rw [sigma_rw this]
  simp [rflushed]
  use s₂

lemma fm_imp_m: ∀ ident s₁ v s₂,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₃, (mod.inputs.getIO ident).snd s₁ (flushed_preserves_input_over_getIO.mp v) s₃ :=
by
  intros ident _ _ _ h
  have := flushed_inputs_are_rflushed mod ident
  rw [sigma_rw this] at h
  simp [rflushed] at h
  obtain ⟨s₃, _, _⟩ := h
  simp
  use s₃

end Lemmas

section

  variable {Ident S : Type _}
  variable [DecidableEq Ident]

-- TODO: If we build a hierarchy of flushable modules. Should we also define a typeclass
--    for InputPreserversFlushability

class OutputPreservesFlushability (mod: Module Ident S) where
  rule: ∀ ident s₁ v s₂,
    pf mod s₁
  → (mod.outputs.getIO ident).snd s₁ v s₂
  →  pf mod s₂

-- This defintion maybe incomplete because it doesn't enforce that the same token will be outputed
-- TODO: Should we make it reachability preserves outputability?
--       In this case, flushing becomes a special case
class FlushabilityPreservesOutputability (mod: Module Ident S) where
  rule: ∀ ident s₁ s₂,
   outputable mod s₁ ident
   → flushesTo mod s₁ s₂
   → outputable mod s₂ ident

-- TODO: We can also define flushability preserves inputability for symmetry
-- Both of these properties should define wellformness (or be derived from wellformess)
-- of dataflow circuit (only DAGs?)

end

section Refinements

variable (mod: Module Ident S)
variable [DecidableEq Ident]

section FlushedRefinesNonFlushed

private theorem flushed_refinesφ_nonflushed:
  flushed mod ⊑_{Eq} mod := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  subst_vars
  apply Module.comp_refines.mk
  -- input rules
  . intro ident mid_i v h
    simp only [eq_mp_eq_cast, exists_and_left, exists_eq_right']
    rw [sigma_rw (flushed_inputs_are_rflushed _ _)] at h
    dsimp [rflushed] at h
    obtain ⟨s', _, h⟩ := h
    apply flushesTo_implies_reachable at h
    use s'
  -- output rules
  . intro _ mid_i _ _
    dsimp [flushed] at *
    use init_s, mid_i;
    and_intros <;> simpa [existSR_reflexive]
  -- internal rules
  . intro _ mid_i h _
    dsimp [flushed] at h
    contradiction

private theorem refines_init:
  Module.refines_initial (flushed mod) mod Eq :=
by
  unfold Module.refines_initial
  intros s h
  dsimp [flushed, isflushed] at h
  use s
  --obtain ⟨w, _, _⟩ := h
  --use w
  --and_intros
  --. assumption
  --. sorry -- only when mod has flushed initial states.
    -- TODO: Should this be included in the wellformness of a module?

theorem flushed_refines_nonflushed: flushed mod ⊑ mod :=
by
  unfold Module.refines
  have mm: MatchInterface (flushed mod) mod := by infer_instance
  use mm
  use Eq
  and_intros
  . apply flushed_refinesφ_nonflushed
  . apply refines_init

end FlushedRefinesNonFlushed

section NonFlushedRefinesFlushed

variable [qc: QuasiConfluent mod] -- TODO: Can we only use local confluence?
variable [sm: RuleMaySwap mod] -- TODO: Can we derive this property from some sort of confluence?
variable [fl: Flushable mod]
variable [opfm: OutputPreservesFlushability mod] -- TODO: Definition of flushed should guarantee this

theorem nonflushed_refinesφ_flushed:
  mod ⊑_{flushesTo mod} flushed mod :=
by
  unfold Module.refines_φ
  intro init_i init_s h
  apply Module.comp_refines.mk
  . intros ident mid_i v _
    have: ∃ s₄, (mod.inputs.getIO ident).snd init_s v s₄ ∧ existSR mod.internals mid_i s₄ := by
      obtain ⟨_, _⟩ := h
      apply sm.inputs <;> assumption
    obtain ⟨s₄, h₂, _⟩ := this
    obtain h₃ := m_imp_fm mod ident init_s v s₄ h₂
    obtain ⟨s₃, h₃⟩ := h₃
    use s₃, s₃
    and_intros
    . assumption
    . apply existSR_reflexive
    . have := flushed_inputs_are_rflushed mod ident
      rw [sigma_rw this] at h₃
      simp [rflushed] at h₃ <;> clear this
      obtain ⟨s₅, _, _, _⟩ := h₃
      constructor
      . apply existSR_transitive _ _ s₄ _
        . assumption
        . have: ∃ s₆, existSR mod.internals s₄ s₆ ∧ existSR mod.internals s₅ s₆ := by
            apply qc.inputs <;> assumption
          obtain ⟨s₆, _, _⟩ := this
          apply existSR_transitive _ _ s₆ _
          . assumption
          . have: flushesTo mod s₅ s₃ := by
              constructor <;> assumption
            have: flushesTo mod s₆ s₃ := by
              apply newrule <;> assumption
            obtain ⟨_, _⟩ := this
            assumption
      . assumption
  . intros ident mid_i v _
    use init_s
    obtain ⟨_, _⟩ := h
    simp only [exists_and_left]
    and_intros
    . apply existSR_reflexive
    . obtain ⟨s₄, _, _⟩ := sm.outputs ident init_i v mid_i init_s (by assumption) (by assumption)
      use s₄
      dsimp [flushed]
      and_intros
      . assumption
      . constructor
        . assumption
        . apply opfm.rule <;> assumption
  . intros rule mid_i _ _
    use init_s
    and_intros
    . apply existSR_reflexive
    . have: existSR mod.internals init_i mid_i := by
        apply existSR_single_step <;> assumption
      have: ∃ s₄, existSR mod.internals mid_i s₄ ∧ existSR mod.internals init_s s₄ := by
          obtain ⟨_, _⟩ := h
          apply qc.internals <;> assumption
      obtain ⟨s₄, _, _⟩ := this
      have: existSR mod.internals init_i mid_i := by
        apply existSR_single_step <;> assumption
      apply newrule <;> assumption

omit qc sm opfm in
private theorem refines_init':
  Module.refines_initial mod (flushed mod) (flushesTo mod) :=
by
  unfold Module.refines_initial
  intros s h
  have ⟨s', _⟩ := fl.flushable s
  use s
  apply And.intro
  . dsimp [flushed, isflushed] <;> assumption
  . sorry -- TODO: Wellformness should solve this

theorem nonflushed_refines_flushed: mod ⊑ flushed mod :=
by
  unfold Module.refines
  have mm: MatchInterface mod (flushed mod) := by infer_instance
  use mm
  use (flushesTo mod)
  and_intros
  . apply nonflushed_refinesφ_flushed
  . apply refines_init'

end NonFlushedRefinesFlushed

end Refinements

end Graphiti

-- TODO: derive flushability patterns of connect module from outputability patterns of base modules?
