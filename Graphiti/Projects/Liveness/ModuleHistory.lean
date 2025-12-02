import Graphiti.Core.ModuleLemmas
import Graphiti.Core.Trace

namespace Graphiti.History

variable {Ident : Type _}
variable [DecidableEq Ident]
variable {S : Type _}

def generate_history (m : Module Ident S) : Module Ident (Trace Ident × S) :=
  { init_state s := m.init_state s.2 ∧ s.1 = .nil
    inputs := m.inputs.mapVal (λ k input_rule => ⟨_, λ s i s' =>
          input_rule.snd s.2 i s'.2 ∧ s'.1 = s.1.concat (IOEvent.input k ⟨_, i⟩)
        ⟩)
    outputs :=
      m.outputs.mapVal (λ k output_rule => ⟨_, λ s o s' =>
          output_rule.snd s.2 o s'.2 ∧ s'.1 = s.1.concat (IOEvent.output k ⟨_, o⟩)
        ⟩)
    internals := m.internals.map (λ rule => λ s s' => rule s.2 s'.2 ∧ s.1 = s'.1)
  }

theorem generate_history_correct1 {m : Module Ident S} {t : Trace Ident} :
  ∀ s', @reachable _ _ (Module.state_transition (generate_history m)) t s' → s'.state.1 = t := by sorry

theorem generate_history_correct2 {m : Module Ident S} {s} {t : Trace Ident} :
  @reachable _ _ (Module.state_transition m) t s →
  ∃ s', @reachable _ _ (Module.state_transition (generate_history m)) t s' ∧ s'.state.2 = s.state := by sorry

end Graphiti.History
