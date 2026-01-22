import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Projects.Flushability.SimulationRelation
import Graphiti.Projects.Flushability.Outputability

namespace Graphiti

variable {Ident S₁ S₂: Type _}
variable (mod₁: Module Ident S₁) (mod₂: Module Ident S₂)
variable (φ: S₁ → S₂ → Prop)
variable [DecidableEq Ident]
variable [MatchInterface mod₁ mod₂]

section EmptyRefinesModule

variable [MatchInterface (Module.empty S₂) mod₁] in
theorem refines₀': @Module.empty Ident S₂ ⊑_{@TTrue S₂ S₁} mod₁ := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  . intros _ _ _ h
    simp[Module.empty, PortMap.getIO] at h
  . intros _ _ _ h
    simp[Module.empty, PortMap.getIO] at h
  . intros _ _ h _
    simp[Module.empty] at h

end EmptyRefinesModule

section SimulationRelation

variable [sr: SimulationRelation φ mod₁ mod₂]
variable [id: Indistinguishable mod₁ mod₂ φ]

theorem refines₀: mod₁ ⊑_{φ} mod₂ := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  . intros ident mid_i v h
    obtain ⟨almost_mid_s, h⟩ := id.inputs ident init_i init_s mid_i v Hφ h
    use almost_mid_s, almost_mid_s
    apply And.intro
    . assumption
    . apply And.intro
      . apply existSR_reflexive
      . apply sr.inputs_preserved <;> assumption
  . intros ident mid_i v h
    use init_s
    rw [exists_and_left]
    and_intros
    . apply existSR_reflexive
    . obtain ⟨mid_s, h⟩ := id.outputs ident init_i init_s mid_i v Hφ h
      use mid_s
      apply And.intro
      . assumption
      . apply sr.outputs_preserved <;> assumption
  . intros rule mid_i h₁ h₂
    use init_s
    apply And.intro
    . apply existSR_reflexive
    . have := existSR_single_step mod₁.internals init_i mid_i rule h₁ h₂
      have := @existSR_reflexive S₂ mod₂.internals init_s
      apply sr.internals_preserved <;> assumption

end SimulationRelation

section WeakSimulationRelation

variable [sr: WeakSimulationRelation φ mod₁ mod₂]

-- TODO: What are the conditions here?
theorem refines₁: mod₁ ⊑_{φ} mod₂ := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  . sorry
  . sorry
  . sorry


end WeakSimulationRelation

end Graphiti
