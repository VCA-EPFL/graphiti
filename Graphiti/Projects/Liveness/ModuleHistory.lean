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

theorem generate_history_correct1_base {m : Module Ident S} {t : Trace Ident} :
  ∀ s1 s2, @star _ _ (Module.state_transition (generate_history m)) s1 t s2 → s1.module = (generate_history m) → s2.state.1 = s1.state.1 ++ t := by
  intros s1 s2 h_star h_mod
  induction h_star
  case refl s =>
    simp
  case step s1' s2' s3' t1 t2 h_step h_star ih =>
    rcases s1' with ⟨ ⟨ st1hist, st1 ⟩, mod1 ⟩; rcases s2' with ⟨ ⟨ st2hist, st2 ⟩, mod2 ⟩; rcases s3' with ⟨ ⟨ st3hist, st3 ⟩, mod3 ⟩;
    simp at *; subst_vars
    cases h_step --<;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
    case input _ ip a b c d =>
      rw [PortMap.rw_rule_execution (by simp [generate_history]; rfl)] at *

      sorry

      -- intros h_mod

    case output => sorry
    case internal _ r relInt h_step =>
      simp at *
      -- rcases s1' with ⟨ ⟨ st1hist, st1 ⟩, mod1 ⟩; rcases new_s with ⟨ stnew, s1hist ⟩ ; simp at *; subst_vars
      simp [generate_history] at relInt
      rcases relInt with ⟨ r', relInt', h_rel ⟩
      rw [← h_rel] at h_step
      rcases h_step with ⟨ rel12, hist12 ⟩
      simp at hist12
      rw [hist12]
      exact ih

theorem generate_history_correct1_star {m : Module Ident S} {t1 t2 : Trace Ident} :
  ∀ s1 s2,
  @reachable _ _ (Module.state_transition (generate_history m)) t1 s1
  → @star _ _ (Module.state_transition (generate_history m)) s1 t2 s2
  → s1.module = (generate_history m)
  → s1.state.1 = t1
  → s2.state.1 = t1++t2
  := by
    intros s1 s2 h_reach_s1 h_s1_star_s2 h_mod h_hist_s1
    induction h_s1_star_s2
    case refl s3 =>
      simp; exact h_hist_s1
    case step s3 s4 s5 t3 t4 h_step h_star ih =>


      sorry

theorem generate_history_correct1 {m : Module Ident S} {t : Trace Ident} :
  ∀ s', @reachable _ _ (Module.state_transition (generate_history m)) t s' → s'.state.1 = t := by
  intros s_end h_reach
  have h_reach_end := h_reach
  obtain ⟨ s_init, ⟨ h_init, h_mod ⟩, h_star ⟩ := h_reach
  have h_reach_start : @reachable _ _ (Module.state_transition (generate_history m)) [] s_init := by
    unfold reachable
    exists s_init
    apply And.intro
    . unfold StateTransition.init
      apply And.intro
      . assumption
      . assumption
    . apply @star.refl _ _ (Module.state_transition (generate_history m))

  simp [ Module.state_transition] at h_init;
  have ⟨ h_init_state, h_empty_hist ⟩ := h_init

  -- have h_rec := generate_history_correct1_star _ _ h_reach_start h_star h_mod
  -- apply h_rec
  -- exact h_empty_hist

  -- induction h_star
  -- . assumption
  -- case step s1 s2 s3 t1 t2 t3 h_step s_star ih =>
  --   sorry

  have h_rec := generate_history_correct1_base s_init s_end h_star h_mod
  rw [h_empty_hist] at h_rec
  simp at h_rec
  exact h_rec

theorem generate_history_correct2 {m : Module Ident S} {s} {t : Trace Ident} :
  @reachable _ _ (Module.state_transition m) t s →
  ∃ s', @reachable _ _ (Module.state_transition (generate_history m)) t s' ∧ s'.state.2 = s.state := by sorry

end Graphiti.History
