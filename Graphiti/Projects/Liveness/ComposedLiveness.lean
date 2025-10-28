/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier, Lorenzo Padrini
-/

import Graphiti.Core.ModuleLemmas
import Graphiti.Core.StateTransition
import Graphiti.Projects.Liveness.ComposedModule
import Graphiti.Projects.Liveness.StateTransitionLiveness
import Graphiti.Core.Trace

-- general liveness theorem sketch, as described in "Defining Liveness" paper
-- (∀α: α ∈ S* : (∃β : β ∈ Sω : αβ respects P))
-- theorem liveness (P : Trace → Prop)  :
--   α ∈ (List Trace) → ∃β : β ∈ Sω → P αβ := by
--     sorry


open Graphiti
open Graphiti.Module
open List

/-
The property that our circuit has to follow
-/

def gcompf_P {T} (t: Trace Nat)(f g: T → T) : Prop :=
  ∀ in1, .input 0 ⟨ T, in1 ⟩ ∈ t → .output 0 ⟨ T, g (f (in1)) ⟩ ∈ t

/-
INPUTS: theorems and lemmas managing the input case of the proof
-/

/-
if t1 respects P and t2 respects P then t1++t2 respects P
-/
theorem gcompf_P_concat {T}(f g: T → T):
  ∀ t0 t1, gcompf_P t0 f g ∧ gcompf_P t1 f g → gcompf_P (t0++t1) f g := by
    intros t0 t1 h
    unfold gcompf_P at *
    have ⟨ h1, h2 ⟩ := h
    intros in1 h_in_concat
    -- List.mem_append : a ∈ L₁ ++ L₂ ↔ a ∈ L₁ ∨ a ∈ L₂
    rcases (mem_append.mp h_in_concat) with h_in_t0 | h_in_t1
    case inl =>
      have h_out_t0 : IOEvent.output 0 ⟨T, g (f in1)⟩ ∈ t0 := h1 in1 h_in_t0
      exact mem_append_left t1 h_out_t0
    case inr =>
      have h_out_t1 : IOEvent.output 0 ⟨T, g (f in1)⟩ ∈ t1 := h2 in1 h_in_t1
      exact mem_append_right t0 h_out_t1

/-
If (s_init -[t]*> s_1) (= reachable s_1) and (gcompf_P t) holds, then s_1 = ([], [])
since all inputs in t get closed in t, and t starts from init.
s_init = ([], []), then all inputs in t go in s_init.first, and since P t, we know outputs g(f(inputs)) ∈ t.
for outputs to go in trace, need to flush first list into second with internal rule then use output rule, necessarily
all inputs have to find their outputs in t so none can get stuck inside
-/
theorem reachable_P_implies_empty_state (T : Type) (f g : T → T) (t : Trace ℕ) (s1 : List T × List T) :
@reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s1, (NatModule.gcompf T f g) ⟩
∧ gcompf_P t f g
→ s1 = ([], []) := by
  intros h
  have ⟨ h_reachable, h_p ⟩ := h
  cases h_reachable
  case intro s0 h_reachable =>
    have ⟨ h_init, h_star ⟩ := h_reachable
    dsimp [Module.state_transition] at h_init
    have s0_init_state_empty := h_init.left
    dsimp [NatModule.gcompf] at s0_init_state_empty

    sorry




theorem gcompf_in_P_is_trans {T f g}: ∀ t0 t s s0 e, (∀ x, .input 0 ⟨T, x⟩ ∉ t0)
→ gcompf_P (t ++ t0) f g
→ @star _ _ (state_transition (NatModule.gcompf T f g)) s t0 s0
→ gcompf_P (t ++ [.input 0 ⟨T, e⟩ ] ++ t0 ++ [.output 0 ⟨ T, g (f e) ⟩ ]) f g -- why is t0 in between the in and out? is it useful ?
  := by
    intros t1 t0 s0 s1 e h_noInpInT1 h_concatP h_star
    -- gcompf_P_concat
    simp [gcompf_P, h_noInpInT1] at *
    intro x h_x
    cases h_x
    case inl h =>
      have h1 := h_concatP x h
      cases h1
      case inl h2 =>
        exact Or.inl h2
      case inr h2 =>
        refine or_assoc.mp ?_
        exact Or.intro_left (g (f x) = g (f e)) (h_concatP x h)
    case inr h =>
      rw [h]
      right
      right
      rfl

theorem gcompf_empty_spec {T f g} (st1: List T × List T) (io: T):
@step _ _ _ ⟨(st1.fst ++ [f io], st1.snd), NatModule.gcompf T f g ⟩ []
  { state := (∅, st1.snd ++ (st1.fst.map g) ++ [g (f io)]), module := NatModule.gcompf T f g } := by
  rcases st1 with ⟨a,b ⟩
  simp at *
  constructor <;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  . simp at *
    constructor
  . simp [NatModule.gcompf] at *



theorem gcompf_output_spec {T f g} (st1: List T × List T) (io: T):
@step _ _ _ ⟨(st1.fst, (g (f io)) :: st1.snd), NatModule.gcompf T f g ⟩ [IOEvent.output 0 ⟨T, g (f io)⟩]
  { state := (st1.fst, st1.snd), module := NatModule.gcompf T f g } := by
  rcases st1 with ⟨a,b ⟩
  simp at *
  constructor <;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  . simp at *
    constructor
  . simp [NatModule.gcompf] at *









theorem gcompf_input_star_maps {T f g} (s1 s2 s3: State ℕ (List T × List T)) (t: List (IOEvent ℕ)) (io: T) (h_mod: s1.module = (NatModule.gcompf T f g) ∧ s2.module = (NatModule.gcompf T f g) ∧ s3.module = (NatModule.gcompf T f g)):
@star _ _ (state_transition (NatModule.gcompf T f g)) s1 t s2
→ @step _ _ _ s1 [IOEvent.input 0 ⟨T, io⟩] s3
→ ∃ s4, @star _ _ (state_transition (NatModule.gcompf T f g)) s3 (t ++ [IOEvent.output 0 ⟨T, g (f io)⟩]) s4 :=
by
  intro s1_stars_s2 s1_steps_s3
  induction t using List.concat_induction  with
  | empty =>
    cases s1
    cases s3
    cases s2
    rename_i st1 mod1 st3 mod3 st2 mod2
    simp at *
    cases s1_steps_s3; simp at *; rename_i st1fst st1snd TandIo; rcases TandIo with ⟨Teq,ioeq⟩
    rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
    rcases h_mod with ⟨mod1_eq,s2_mod ⟩
    subst_vars
    simp at *
    exists { state := (st1.fst, st1.snd), module := NatModule.gcompf T f g }
    have emptStep := @gcompf_empty_spec T f g st1 io
    have outStep := @gcompf_output_spec T f g st1 io
    exact @star.step _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ _ _ emptStep (@star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ outStep)
  | step =>
    sorry




theorem gcompf_input_transitive { T f g} (s1 s2 s3 : List T × List T) (t t0: List (IOEvent ℕ)) (io: T): @reachable _ _ (state_transition (NatModule.gcompf T f g)) t  ⟨ s1, (NatModule.gcompf T f g)⟩
→ ( ∀ x, .input 0 ⟨T, x⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s1, (NatModule.gcompf T f g)⟩ t0 ⟨s2, (NatModule.gcompf T f g )⟩
→ gcompf_P (t ++ t0) f g
→ @step _ _ _ ⟨ s1, (NatModule.gcompf T f g)⟩ [IOEvent.input 0 ⟨ T, io⟩]  ⟨s3, (NatModule.gcompf T f g) ⟩
→ ∃ sn tn, gcompf_P (t ++ [IOEvent.input 0 ⟨T, io ⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s3, (NatModule.gcompf T f g) ⟩  tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
    intro s1_reachable ⟨no_input_in_t0, s1_star_s2_with_t0⟩ P_for_t_t0 s1_stars_s3_with_em
    have gcomp_still_valid := @gcompf_in_P_is_trans T f g t0 t ⟨s1, (NatModule.gcompf T f g)⟩ ⟨s2, (NatModule.gcompf T f g)⟩ io no_input_in_t0 P_for_t_t0 s1_star_s2_with_t0
    have new_star_T := @gcompf_input_star_maps T f g ⟨s1, (NatModule.gcompf T f g)⟩ ⟨s2, (NatModule.gcompf T f g)⟩ ⟨s3, (NatModule.gcompf T f g)⟩ t0 io
    simp at new_star_T
    have new_star := new_star_T s1_star_s2_with_t0 s1_stars_s3_with_em
    clear new_star_T
    match new_star with
    | ⟨s4, s1_stars_s4⟩  =>
      exists s4, (t0 ++ [IOEvent.output 0 ⟨T, g (f io)⟩])
      refine ⟨?_, ?_, ?_⟩
      . simp at *
        apply gcomp_still_valid
      . apply s1_stars_s4
      . simp
        apply no_input_in_t0







/-
OUTPUTS: theorems and lemmas managing the output case of the proof
-/

-- the module is deterministic
theorem gcompf_out_P_is_trans {T f g}: ∀ t0 t s s0 e, (∀ x, .input 0 ⟨T, x⟩ ∉ t0)
→ gcompf_P (t ++ t0) f g
→ @star _ _ (state_transition (NatModule.gcompf T f g)) s t0 s0
→ ∃ t0', gcompf_P (t ++ [.output 0 ⟨ T, e ⟩] ++ t0') f g
∧ t0 = ([.output 0 ⟨ T, e ⟩] ++ t0'):= by
  intro t0 t1 s1 s0 e iProp star
  sorry







theorem gcompf_reachness_output { T f g} (s1 s2 s3 : List T × List T) (t t0: List (IOEvent ℕ)) (io: T): @reachable _ _ (state_transition (NatModule.gcompf T f g)) t  ⟨ s1, (NatModule.gcompf T f g)⟩
→ ( ∀ x, .input 0 ⟨T, x⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s1, (NatModule.gcompf T f g)⟩ t0 ⟨s2, (NatModule.gcompf T f g )⟩
→ gcompf_P (t ++ t0) f g
→ @step _ _ _ ⟨ s1, (NatModule.gcompf T f g)⟩ [IOEvent.output 0 ⟨ T, io⟩]  ⟨s3, (NatModule.gcompf T f g) ⟩
→ ∃ sn tn, gcompf_P (t ++ [IOEvent.output 0 ⟨T, io ⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s3, (NatModule.gcompf T f g) ⟩  tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  sorry


/-
EMPTY: theorems to prove the  empty case
-/
theorem gcompf_reachness_empty {T f g} (t t0: List (IOEvent ℕ )) (s1 s2 s3: (List T × List T)): @reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s1, (NatModule.gcompf T f g ) ⟩
→ ( ∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s1, (NatModule.gcompf T f g ) ⟩  t0 ⟨ s2, (NatModule.gcompf T f g ) ⟩
→ gcompf_P (t ++ t0) f g
→ @step _ _ _ ⟨ s1, (NatModule.gcompf T f g ) ⟩  [] ⟨ s3, (NatModule.gcompf T f g ) ⟩
→ ∃ sn tn, gcompf_P (t ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s3, (NatModule.gcompf T f g ) ⟩  tn sn ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  intro s1_reachable ⟨no_input_in_t0, s1_star_s2_with_t0⟩ P_for_t_t0 s1_step_s3
  exists { state := s2, module := NatModule.gcompf T f g }
  exists t0
  apply And.intro
  case left => exact P_for_t_t0
  case right =>
    apply And.intro
    case left =>
      cases s1_star_s2: s1_star_s2_with_t0
      case refl =>
        simp at P_for_t_t0
        have h_s1_empty : s1 = ([], []) := reachable_P_implies_empty_state T f g t s1 (And.intro s1_reachable (P_for_t_t0))
        have s3_reachable : @reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s3, (NatModule.gcompf T f g ) ⟩ :=
          -- S1 reachable and s1_step_s3 so s3 reachable
          sorry
        have h_s3_empty : s3 = ([], []) := reachable_P_implies_empty_state T f g t s3 (And.intro s3_reachable (P_for_t_t0))
        have h_s1_s3 : s1 = s3 := calc
          s1 = ([], []) := h_s1_empty
          _ = s3        := by rw [h_s3_empty]
        rw [← h_s1_s3]
        exact s1_star_s2_with_t0
      case step s4 t1 t2 s1_step_s4_with_t1 s4_star_s2_with_t2 =>
        
        sorry
    case right =>
      trivial



/--
MAIN PROOF: here lies the main proof of the liveness of a circuit
-/

-- diff with liveness: steps for given s1 s2 & ∃s3, s2-[t']*>s3 instead of behavior (t++t')
theorem gcompf_liveness_simp {t : Trace Nat} {T f g}
(h_in: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_out: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(s1 s2: State _ _)
(h_s1: s1.module = (NatModule.gcompf T f g))
(h_s2: s2.module = (NatModule.gcompf T f g))
(h: @StateTransition.init _ _ (state_transition (NatModule.gcompf T f g)) s1 ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s1 t s2):
  ∃ t' s3, gcompf_P (t ++ t') f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s2 t' s3 ∧ (∀ x, .input 0 ⟨T, x⟩ ∉ t'):= by
    have starConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 t).mp h.right
    induction starConv
    . exists []
      simp [gcompf_P]
      exists s1
      exact h.right
    . rename_i s3 s4 l1 l2 step star iH
      have starConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s3 l1).mpr star
      clear star
      simp at h_in h_out
      have h_in_new : (∀ (G : Type) (x : G) (n : InternalPort ℕ), IOEvent.input n ⟨G, x⟩ ∈ l1 → n = 0 ∧ G = T) := by {
        intro G x n exp
        have h_in_up := h_in G x n
        apply h_in_up
        constructor
        assumption
      }
      have h_out_new : (∀ (G : Type) (x : G) (n : InternalPort ℕ), IOEvent.output n ⟨G, x⟩ ∈ l1 → n = 0 ∧ G = T) := by {
        intro G x n exp
        have h_out_up := h_out G x n
        apply h_out_up
        constructor
        assumption
      }
      have keep := steps_preserve_mod (NatModule.gcompf T f g) starConv
      rw [h_s1] at keep
      have iHRes := iH h_in_new h_out_new keep (And.intro h.left starConv)
      clear iH
      cases iHRes
      rename_i tr iH
      cases iH
      rename_i s5 iH
      have keepStep := step
      cases step
      . rename_i IntN s4 s3Fst TT s3Snd TTEq
        cases s3
        rename_i s3 mod3
        subst keep
        have finalResT := @gcompf_input_transitive T f g
        simp [reachable] at finalResT
        cases s5
        rename_i s5 mod5
        cases TT
        rename_i TT inp
        have h_in_assum := h_in TT inp IntN
        simp at h_in_assum
        rcases h_in_assum with ⟨ nEq, TypeEq ⟩
        subst nEq
        subst TypeEq
        have s5_mod_eq := steps_preserve_mod (NatModule.gcompf TT f g) iH.right.left
        subst s5_mod_eq
        have finalRes := finalResT s3.1 s3.2 s5.1 s5.2 s4.1 s4.2 l1 tr inp s1 h.left starConv iH.right.right iH.right.left iH.left keepStep
        cases finalRes
        rename_i s4 finalRes
        cases finalRes
        rename_i tn final
        exists tn
        exists s4
        simp at *
        exact final
      . rename_i IntN s4 s3Fst TT s3Snd TTEq
        cases s3
        rename_i s3 mod3
        subst keep
        have finalResT := @gcompf_reachness_output T f g
        simp [reachable] at finalResT
        cases s5
        rename_i s5 mod5
        cases TT
        rename_i TT inp
        have h_out_assum := h_out TT inp IntN
        simp at h_out_assum
        rcases h_out_assum with ⟨ nEq, TypeEq ⟩
        subst nEq
        subst TypeEq
        have s5_mod_eq := steps_preserve_mod (NatModule.gcompf TT f g) iH.right.left
        subst s5_mod_eq
        have finalRes := finalResT s3.1 s3.2 s5.1 s5.2 s4.1 s4.2 l1 tr inp s1 h.left starConv iH.right.right iH.right.left iH.left keepStep
        cases finalRes
        rename_i s4 finalRes
        cases finalRes
        rename_i tn final
        exists tn
        exists s4
        simp at *
        exact final
      . rename_i RelTT LtLt RelTTInt RelTTState
        have finalRes :=@ gcompf_reachness_empty T f g
        simp [reachable] at finalRes
        cases s3
        rename_i s3 mod3
        cases s5
        rename_i s5 mod5
        have s5_mod_eq := steps_preserve_mod (NatModule.gcompf T f g) iH.right.left
        subst s5_mod_eq
        subst keep
        simp at keepStep
        have finalResT := finalRes l1 tr s3.1 s3.2 s5.1 s5.2 LtLt.1 LtLt.2 s1 h.left starConv iH.right.right iH.right.left iH.left keepStep
        cases finalResT
        rename_i s4 finalRes
        cases finalRes
        rename_i tn final
        exists tn
        exists s4
        simp at *
        exact final




theorem gcompf_liveness2 {t : Trace Nat} {T f g}(h_steps: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t)
(h_input: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_output: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_init_imp_mod: ∀s, @StateTransition.init _ _ (state_transition (NatModule.gcompf T f g)) s  → s.module = (NatModule.gcompf T f g)):
  ∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') ∧ ∀ x, .input 0 ⟨T, x⟩ ∉ t' := by
    simp [behaviour] at h_steps
    match h_steps with
    | ⟨ s1, s1_init_step, s2, s1_star_s2_t ⟩  =>
      have s1_mod_eq := h_init_imp_mod s1 s1_init_step
      have s2_mod_eq := steps_preserve_mod (NatModule.gcompf T f g) s1_star_s2_t
      rw [s1_mod_eq] at s2_mod_eq
      have induct_star_res := gcompf_liveness_simp h_input h_output s1 s2 s1_mod_eq s2_mod_eq (And.intro s1_init_step s1_star_s2_t)
      match induct_star_res with
      | ⟨t2, s3, P_true_tt2, s2_stars_s3_t2, no_inp_in_t2 ⟩ =>
        exists t2
        constructor
        . exact P_true_tt2
        . constructor
          . simp [behaviour]
            have starComb := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 s3 t t2 s1_star_s2_t s2_stars_s3_t2
            exists s1
            constructor
            . exact s1_init_step
            . exists s3
          . exact no_inp_in_t2
