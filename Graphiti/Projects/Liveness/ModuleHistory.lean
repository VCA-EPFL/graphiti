import Graphiti.Core.Graph.ModuleLemmas
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

def match_interface (m : Module Ident S) : MatchInterface m (generate_history m) := by
  rw [MatchInterface_simpler_iff]; intro ident; and_intros
  · dsimp [generate_history]
    rw [Batteries.AssocList.find?_mapVal, Batteries.AssocList.find?_mapVal,Batteries.AssocList.find?_mapVal]
    cases hin : Batteries.AssocList.find? ident m.inputs <;> rfl
  · dsimp [generate_history]
    rw [Batteries.AssocList.find?_mapVal, Batteries.AssocList.find?_mapVal,Batteries.AssocList.find?_mapVal]
    cases hin : Batteries.AssocList.find? ident m.outputs <;> rfl

theorem generate_history_correct1_base {m : Module Ident S} {t : Trace Ident} :
∀ s1 s2, @star _ _ (Module.state_transition (generate_history m)) s1 t s2 → s1.module = (generate_history m) → s2.state.1 = s1.state.1 ++ t := by
  intros s1 s2 h_star h_mod
  induction h_star
  case refl s =>
    simp
  case step s1' s2' s3' t1 t2 h_step h_star ih =>
    rcases s1' with ⟨ ⟨ st1hist, st1 ⟩, mod1 ⟩; rcases s2' with ⟨ ⟨ st2hist, st2 ⟩, mod2 ⟩; rcases s3' with ⟨ ⟨ st3hist, st3 ⟩, mod3 ⟩;
    simp at *; subst_vars
    cases h_step
    case input _ ip a b c d =>
      rw [← List.append_assoc]
      generalize h1 : (Batteries.AssocList.find? ip m.inputs) = og_inputs at *
      have h: st1hist ++ [IOEvent.input ip b] = st2hist := by
        rw [PortMap.rw_rule_execution (by simp [generate_history]; rfl)] at *
        simp [PortMap.getIO] at d
        rw [PortMap.rw_rule_execution (by rw [Batteries.AssocList.find?_mapVal, h1])] at *
        rw [PortMap.rw_rule_execution (by simp [Option.map, Option.getD]; rfl)] at *
        cases h_og : (Batteries.AssocList.find? ip m.inputs) <;> try subst_eqs; rw [PortMap.rw_rule_execution (by rw [h_og])] at *; simp at d
        case some x =>
          have ⟨ _, rell ⟩ := d
          grind
      rw [h]
      simp at *
      assumption

    case output _ ip a b c d =>
      rw [← List.append_assoc]
      generalize h1 : (Batteries.AssocList.find? ip m.outputs) = og_outputs at *
      have h: st1hist ++ [IOEvent.output ip b] = st2hist := by
        rw [PortMap.rw_rule_execution (by simp [generate_history]; rfl)] at *
        simp [PortMap.getIO] at d
        rw [PortMap.rw_rule_execution (by rw [Batteries.AssocList.find?_mapVal, h1])] at *
        rw [PortMap.rw_rule_execution (by simp [Option.map, Option.getD]; rfl)] at *
        cases h_og : (Batteries.AssocList.find? ip m.outputs) <;> try subst_eqs; rw [PortMap.rw_rule_execution (by rw [h_og])] at *; simp at d
        case some x =>
          have ⟨ _, rell ⟩ := d
          grind
      rw [h]
      simp at *
      assumption
    case internal _ r relInt h_step =>
      simp at ih
      simp [generate_history] at relInt
      rcases relInt with ⟨ r', relInt', h_rel ⟩
      rw [← h_rel] at h_step
      rcases h_step with ⟨ rel12, hist12 ⟩
      simp at hist12
      rw [hist12]
      exact ih

theorem generate_history_correct1 {m : Module Ident S} {t : Trace Ident} :
  ∀ s', @reachable _ _ (Module.state_transition (generate_history m)) t s' → s'.state.1 = t := by
  intros s_end h_reach
  have ⟨ s_init, ⟨ h_init, h_mod ⟩, h_star ⟩ := h_reach
  have ⟨ h_init_state, h_empty_hist ⟩ := h_init

  have h_rec := generate_history_correct1_base s_init s_end h_star h_mod
  simp [h_empty_hist] at h_rec
  exact h_rec


theorem generate_history_correct2_star {m : Module Ident S} {s2} {t : Trace Ident} :
  ∀ s1, @star _ _ (Module.state_transition m) s1 t s2
  → s1.module = m
  → ∀(h : Trace Ident) (s1': Module.State Ident (Trace Ident × S)),
  s1'.state = (h, s1.state) ∧ s1'.module = generate_history m
  → ∃(s2': Module.State Ident (Trace Ident × S)),
  @star _ _ (Module.state_transition (generate_history m)) s1' t s2' ∧ s2'.state.2 = s2.state := by
    intros s1 h_star --h_mod1 s1' h_s1 h_mod1'
    induction h_star
    case refl _ s =>
      intros h_mod1 hist s1' h
      have ⟨ h_s1, h_mod ⟩ := h
      exists s1'
      apply And.intro
      . apply @star.refl _ _ (Module.state_transition (generate_history m))
      . grind
    case step _ s_1 s_2 s_3 t1 t2 h_step h_star ih =>
      intros h_mod1 hist1 s1' h
      rcases h with ⟨ h_s1, h_mod1' ⟩
      have h_mod2 : s_2.module = m := by
        have temp := (@Module.step_preserve_mod _ _ _ m s_1 t1 s_2 h_step)
        rw [h_mod1] at temp
        exact temp
      simp [h_mod2] at ih

      specialize ih (hist1 ++ t1) ({state := (hist1 ++ t1, s_2.state), module := (generate_history m)}: Module.State _ _)
      simp at ih
      obtain ⟨ s3', proof ⟩ := ih
      have h_step' : @StateTransition.step _ _ (Module.state_transition (generate_history m)) s1' t1  { state := (hist1 ++ t1, s_2.state), module := s1'.module } := by
        cases h_step
        case input ip s_2 type_i i h_rel h_i =>
          cases hip_avail : s_1.module.inputs.find? ip with
          | none =>
            unfold PortMap.getIO at h_rel; rw [PortMap.rw_rule_execution (by rw [hip_avail])] at h_rel
            contradiction
          | some ipval =>
            unfold PortMap.getIO at h_rel; rw [PortMap.rw_rule_execution (by rw [hip_avail])] at h_rel; dsimp at h_rel
            unfold StateTransition.step
            unfold Module.state_transition
            obtain ⟨s_1_s, s_1_m⟩ := s_1
            obtain ⟨s1'_s, s1'_m⟩ := s1'
            subst_vars
            apply Module.step.input (v := ((match_interface s_1_m).input_types ip).mp type_i)
            unfold PortMap.getIO; rw [PortMap.rw_rule_execution
              (by
                unfold generate_history
                rewrite [Batteries.AssocList.find?_mapVal]
                rewrite [hip_avail]
                dsimp)]
            and_intros
            simp [*]; simp [-Batteries.AssocList.find?_eq]; rw [hip_avail]; rfl
            simp; apply (match_interface s_1_m).input_types ip
        case output ip s_2 type_i i h_rel h_i =>
          cases hip_avail : s_1.module.outputs.find? ip with
          | none =>
            unfold PortMap.getIO at h_rel; rw [PortMap.rw_rule_execution (by rw [hip_avail])] at h_rel
            contradiction
          | some ipval =>
            unfold PortMap.getIO at h_rel; rw [PortMap.rw_rule_execution (by rw [hip_avail])] at h_rel; dsimp at h_rel
            unfold StateTransition.step
            unfold Module.state_transition
            obtain ⟨s_1_s, s_1_m⟩ := s_1
            obtain ⟨s1'_s, s1'_m⟩ := s1'
            subst_vars
            apply Module.step.output (v := ((match_interface s_1_m).output_types ip).mp type_i)
            unfold PortMap.getIO; rw [PortMap.rw_rule_execution
              (by
                unfold generate_history
                rewrite [Batteries.AssocList.find?_mapVal]
                rewrite [hip_avail]
                dsimp)]
            and_intros
            simp [*]; simp [-Batteries.AssocList.find?_eq]; rw [hip_avail]; rfl
            simp; apply (match_interface s_1_m).output_types ip
        case internal r s_2 rel h_rel =>
          simp
          unfold StateTransition.step
          rw (occs := .pos [1]) [generate_history]
          simp [Module.state_transition]
          obtain ⟨s_1_s, s_1_m⟩ := s_1
          obtain ⟨s1'_s, s1'_m⟩ := s1'
          dsimp at *; subst_vars
          constructor; dsimp
          unfold generate_history; dsimp
          apply List.mem_map_of_mem; assumption; grind
      have h_step' : @StateTransition.step _ _ (Module.state_transition (generate_history m)) s1' t1  { state := (hist1 ++ t1, s_2.state), module := generate_history m } := by
        rw [←h_mod1']; assumption
      generalize hs2' : ({ state := (hist1 ++ t1, s_2.state), module := generate_history m } : Module.State _ _) = s2' at *
      have h_end : @star _ _ (Module.state_transition (generate_history m)) s1' (t1 ++ t2) s3' := by
        have ⟨ ha, hb ⟩ := proof
        apply @star.step _ _ (Module.state_transition (generate_history m)) s1' s2' s3' t1 t2
        exact h_step'
        exact ha
      exists s3'
      apply And.intro
      . exact h_end
      . exact proof.right


theorem generate_history_correct2 {m : Module Ident S} {s} {t : Trace Ident} :
  @reachable _ _ (Module.state_transition m) t s →
  ∃ s', @reachable _ _ (Module.state_transition (generate_history m)) t s' ∧ s'.state.2 = s.state := by
  intro h_reach
  have ⟨ s_init, ⟨ h_init, h_mod ⟩, h_star ⟩ := h_reach
  rcases s_init with ⟨ st_init, mod_init ⟩;

  let s'_mod := generate_history m
  let s'_state : (Trace Ident × S) := (t, s.state)
  exists { state := s'_state, module := s'_mod } -- real_s'
  apply And.intro
  case left => -- real_s' is reachable
    unfold reachable
    let st_init' : (Trace Ident × S) := ([], st_init)
    exists { state := st_init', module := s'_mod }
    apply And.intro
    case left => -- init'
      simp [StateTransition.init, Module.state_transition]
      apply And.intro
      case left =>
        simp [generate_history]
        constructor
        . assumption
        . constructor
      . constructor
    case right => -- star to s'
      generalize h1 : ({ state := st_init, module := mod_init } : Module.State _ _) = s_init_full at *
      generalize h2 : ({ state := st_init', module := s'_mod } : Module.State _ _) = s_init'_full at *
      generalize h3 : ({ state := s'_state, module := s'_mod } : Module.State _ _) = s'_full at *
      simp [s'_state, st_init'] at *
      have hh: ∃(s2': Module.State Ident (Trace Ident × S)), @star _ _ (Module.state_transition (generate_history m)) s_init'_full t s2' ∧ s2'.state.2 = s.state := by
        have a : s_init'_full.state.snd = s_init_full.state := by simp [← h2, st_init', ← h1]
        have b := @generate_history_correct2_star _ _ _ m s t s_init_full h_star h_mod -- s_init'_full h_star a h_mod (by simp [← h2, s'_mod])

        specialize b [] s_init'_full
        simp [← h2, ← h1, s'_mod] at b
        rw [h2] at b
        exact b
        /-
        have h_eq : witness = s_init'_full := by -- witness = { state := ([], st_init), module := s'_mod }
          simp [← h2]

          sorry
        -- have c :
        simp [h_eq, a] at proof
        simp [← h2, s'_mod] at proof ⊢
        exact proof
        -/

      obtain ⟨s_witness, h_path, h_state_match⟩ := hh
      have h_eq : s_witness = s'_full := by -- { state := (t, s.state), module := s'_mod } = s_witness

        have h_wit_mod := @Module.steps_preserve_mod _ _ _ s'_mod s_init'_full t s_witness h_path
        have h_wit_hist := @generate_history_correct1_base _ _ _ m t s_init'_full s_witness h_path (by simp [← h2, s'_mod])
        simp [← h2] at h_wit_hist
        simp [← h3]
        cases s_witness
        case mk _ s_wit_stt s_wit_mod =>
          grind

      rw [← h_eq]
      exact h_path

  . constructor

end Graphiti.History
