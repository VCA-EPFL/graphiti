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
SPECIFICATIONS: show order between states
-/

theorem gcompf_empty_spec {T f g} (st1: List T × List T) :
@step _ _ _ ⟨(st1.fst, st1.snd), NatModule.gcompf T f g ⟩ []
  { state := (∅, st1.snd ++ (st1.fst.map g)), module := NatModule.gcompf T f g } := by
  rcases st1 with ⟨a,b ⟩
  simp at *
  constructor <;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  . simp at *
    constructor
  . simp [NatModule.gcompf] at *



theorem gcompf_output_spec {T f g} (st1: List T × List T) (io: T):
@step _ _ _ ⟨(st1.fst, (io) :: st1.snd), NatModule.gcompf T f g ⟩ [IOEvent.output 0 ⟨T, io⟩]
  { state := (st1.fst, st1.snd), module := NatModule.gcompf T f g } := by
  rcases st1 with ⟨a,b ⟩
  simp at *
  constructor <;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  . simp at *
    constructor
  . simp [NatModule.gcompf] at *



theorem gcompf_input_spec {T f g} (st1: List T × List T) (io: T):
@step _ _ _ ⟨(st1.fst, st1.snd), NatModule.gcompf T f g ⟩ [IOEvent.input 0 ⟨T, io⟩]
  { state := (st1.fst ++ [f io], st1.snd), module := NatModule.gcompf T f g } := by
  rcases st1 with ⟨a,b ⟩
  simp at *
  constructor <;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  . simp at *
    constructor
  . simp [NatModule.gcompf] at *




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
INPUTS: theorems and lemmas managing the input case of the proof
-/

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


theorem gcompf_steps_holds_ {T f g} (s1 s2: State ℕ (List T × List T)) (t: List (IOEvent ℕ)) (io: T)
(h_input: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_output: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_noinp: ∀ x, IOEvent.input 0 ⟨T, x⟩ ∉ t):
@star _ _ (state_transition (NatModule.gcompf T f g)) s1 t s2
→ (s1.module = (NatModule.gcompf T f g)  ∧ s2.module =  (NatModule.gcompf T f g))
→ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ (s1.state.fst ++ [f io], s1.state.snd), (NatModule.gcompf T f g) ⟩ t ⟨ (∅, s2.state.snd ++ (s2.state.fst.map g) ++ [g (f io)]), (NatModule.gcompf T f g) ⟩
∨ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ (s1.state.fst ++ [f io], s1.state.snd), (NatModule.gcompf T f g) ⟩ t ⟨ (s2.state.fst ++ [f io], s2.state.snd), (NatModule.gcompf T f g) ⟩ := by
  intro st1_stars_st2 s1s2ModEq
  rcases s1s2ModEq with ⟨ s1modeq, s2modeq ⟩
  revert io
  have st1_stars_st2_conv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s2  t).mp st1_stars_st2
  induction st1_stars_st2_conv with
  | refl  =>
    intro io
    have empt_spec := @gcompf_empty_spec T f g (s1.state.fst ++ [f io], s1.state.snd)
    left; simp at *
    exact  @star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ empt_spec
  | step s3 s4 t1 t2 s3_steps_s4 s4_stars_s5_conv iH =>
    have s4_stars_s5 := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s3  t1).mpr s4_stars_s5_conv
    have s4modEq := steps_preserve_mod (NatModule.gcompf T f g) s4_stars_s5
    rcases s1 with ⟨ st1, mod1 ⟩
    rcases s2 with ⟨ st2, mod2 ⟩
    rcases s3 with ⟨ st3, mod3 ⟩
    rcases s4 with ⟨ st4, mod4 ⟩
    subst_vars
    simp at *
    --have keepStep := s3_steps_s4
    cases s3_steps_s4 with
    | input st3fst TpeEq =>
      exfalso
      rename_i n st3Fst Tpe
      rcases Tpe with ⟨ G, el ⟩
      have h_in_eval := h_input G el n
      simp at h_in_eval
      rcases h_in_eval with ⟨ n_is_zero, G_is_T ⟩
      subst_vars
      have h_contr := h_noinp el
      simp at *
    | output st3fst TpeEq =>
      have h_in_new : (∀ (G : Type) (x : G) (n : InternalPort ℕ), IOEvent.input n ⟨G, x⟩ ∈ t1 → n = 0 ∧ G = T) := by {
        intro G x n exp
        have h_in_up := h_input G x n (Or.inl exp)
        assumption

      }
      have h_out_new : (∀ (G : Type) (x : G) (n : InternalPort ℕ), IOEvent.output n ⟨G, x⟩ ∈ t1 → n = 0 ∧ G = T) := by {
        intro G x n exp
        have h_out_up := h_output G x n (Or.inl exp)
        assumption
      }
      intro io
      rename_i n st3Fst Tpe
      rcases Tpe with ⟨ G, el ⟩
      have h_out_eval := h_output G el n
      simp at *
      rcases h_out_eval with ⟨ n_is_zero, G_is_T ⟩
      subst_vars
      simp at *
      rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
      rcases TpeEq with ⟨ left, right ⟩
      rcases st3 with ⟨st3fst_, st3snd ⟩
      simp at *
      rcases st3fst with  ⟨ eq1, eq2 ⟩
      subst_vars
      have iH_ := iH h_in_new h_out_new h_noinp s4_stars_s5 io
      clear iH h_in_new h_out_new
      cases iH_ with
      | inl st3_stars_st5 =>
        left
        cases st3snd with
        | nil => simp at eq2
        | cons head tail =>
          rcases eq2 with ⟨ eq1, eq2 ⟩
          subst_vars
          have fst_step := @star.plus_one _ _ (state_transition (NatModule.gcompf G f g)) _ _ _  (@gcompf_output_spec G f g ([],  st4.snd ++ (map g st4.fst ++ [g (f io)])) head); simp at fst_step st3_stars_st5
          have fin := @star.trans_star _ _ (state_transition (NatModule.gcompf G f g)) { state := (st1.fst ++ [f io], st1.snd), module := NatModule.gcompf G f g }  _ _ _ _   st3_stars_st5 fst_step
          exact fin
      | inr st3_stars_st5 =>
        right
        cases st3snd with
        | nil => simp at eq2
        | cons head tail =>
          rcases eq2 with ⟨ eq1, eq2 ⟩
          subst_vars
          have fst_step := @star.plus_one _ _ (state_transition (NatModule.gcompf G f g)) _ _ _  (@gcompf_output_spec G f g (st4.fst ++ [f io],  st4.snd) head); simp at fst_step st3_stars_st5
          have fin := @star.trans_star _ _ (state_transition (NatModule.gcompf G f g)) { state := (st1.fst ++ [f io], st1.snd), module := NatModule.gcompf G f g }  _ _ _ _   st3_stars_st5 fst_step
          exact fin
    | internal st3fst TpeEq =>
      intro io
      rename_i n
      simp at *
      rcases st3 with ⟨ s31, s32 ⟩
      simp [NatModule.gcompf] at TpeEq st3fst
      subst_vars; simp at *
      have iH_ := iH h_input h_output h_noinp s4_stars_s5 io
      clear iH
      cases iH_ with
      | inl st3_stars_st5 =>
        left
        assumption
      | inr st3_stars_st5 =>
        left
        have fst_step := @star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) _ _ _  (@gcompf_empty_spec T f g (s31 ++ [f io],  s32)); simp at fst_step st3_stars_st5
        have fin := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) { state := (st1.fst ++ [f io], st1.snd), module := NatModule.gcompf T f g }  _ _ _ _   st3_stars_st5 fst_step; simp at fin
        assumption










theorem gcompf_steps_holds {T f g} (s1 s2: State ℕ (List T × List T))(t: List (IOEvent ℕ)) (io: T)
(h_input: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_output: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_noinp: ∀ x, IOEvent.input 0 ⟨T, x⟩ ∉ t):
@star _ _ (state_transition (NatModule.gcompf T f g)) s1 t s2
→ (s1.module = (NatModule.gcompf T f g)  ∧ s2.module =  (NatModule.gcompf T f g))
→ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ (s1.state.fst ++ [f io], s1.state.snd), (NatModule.gcompf T f g) ⟩ t ⟨ (∅, s2.state.snd ++ (s2.state.fst.map g) ++ [g (f io)]), (NatModule.gcompf T f g) ⟩ := by
  intro st1_stars_st2 st1st2Mod
  have lemm_ := @gcompf_steps_holds_ T f g s1 s2 t io h_input h_output h_noinp st1_stars_st2 st1st2Mod
  cases lemm_ <;> try assumption
  rename_i iH
  have moreStep := @gcompf_empty_spec T f g (s2.state.fst ++ [f io], s2.state.snd)
  have moreStar := @star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ moreStep
  have final_star := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ _ _ iH moreStar
  simp at *
  exact final_star



theorem gcompf_input_star_maps {T f g} (s1 s2 s3: State ℕ (List T × List T)) (t: List (IOEvent ℕ)) (io: T) (h_mod: s1.module = (NatModule.gcompf T f g) ∧ s2.module = (NatModule.gcompf T f g) ∧ s3.module = (NatModule.gcompf T f g))
(h_input: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_output: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_noinp: ∀ x, IOEvent.input 0 ⟨T, x⟩ ∉ t):
@star _ _ (state_transition (NatModule.gcompf T f g)) s1 t ⟨(∅, ∅), (NatModule.gcompf T f g)⟩
→ @step _ _ _ s1 [IOEvent.input 0 ⟨T, io⟩] s3
→ @star _ _ (state_transition (NatModule.gcompf T f g)) s3 (t ++ [IOEvent.output 0 ⟨T, g (f io)⟩]) ⟨(∅, ∅), (NatModule.gcompf T f g)⟩  :=
by
  intro s1_stars_s2 s1_steps_s3
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
  have next_v := @gcompf_steps_holds T f g ⟨ st1, (NatModule.gcompf T f g) ⟩ ⟨ (∅, ∅),  (NatModule.gcompf T f g)  ⟩  t io h_input h_output h_noinp s1_stars_s2
  simp at *
  have final_s := @gcompf_output_spec T f g ([], []) (g (f io))
  simp at *
  have repl := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ _ _ next_v (@star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ final_s)
  assumption






theorem gcompf_input_transitive { T f g} (s1 s3 : List T × List T) (t t0: List (IOEvent ℕ)) (io: T)
(h_input: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t0 → (n = 0) ∧ G = T))
(h_output: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t0 → (n = 0) ∧ G = T))
(h_noinp: ∀ x, IOEvent.input 0 ⟨T, x⟩ ∉ t0):
@reachable _ _ (state_transition (NatModule.gcompf T f g)) t  ⟨ s1, (NatModule.gcompf T f g)⟩
→ ( ∀ x, .input 0 ⟨T, x⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s1, (NatModule.gcompf T f g)⟩ t0 ⟨(∅, ∅), (NatModule.gcompf T f g )⟩
→ gcompf_P (t ++ t0) f g
→ @step _ _ _ ⟨ s1, (NatModule.gcompf T f g)⟩ [IOEvent.input 0 ⟨ T, io⟩]  ⟨s3, (NatModule.gcompf T f g) ⟩
→ ∃ tn, gcompf_P (t ++ [IOEvent.input 0 ⟨T, io ⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s3, (NatModule.gcompf T f g) ⟩  tn ⟨(∅, ∅), (NatModule.gcompf T f g )⟩ ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
    intro s1_reachable ⟨no_input_in_t0, s1_star_s2_with_t0⟩ P_for_t_t0 s1_stars_s3_with_em
    have gcomp_still_valid := @gcompf_in_P_is_trans T f g t0 t ⟨s1, (NatModule.gcompf T f g)⟩ ⟨(∅, ∅), (NatModule.gcompf T f g)⟩ io no_input_in_t0 P_for_t_t0 s1_star_s2_with_t0
    have new_star_T := @gcompf_input_star_maps T f g ⟨s1, (NatModule.gcompf T f g)⟩ ⟨(∅, ∅), (NatModule.gcompf T f g)⟩ ⟨s3, (NatModule.gcompf T f g)⟩ t0 io
    simp at new_star_T
    have new_star := new_star_T h_input h_output no_input_in_t0
    clear new_star_T
    match new_star with
    | rhs  =>
      exists (t0 ++ [IOEvent.output 0 ⟨T, g (f io)⟩])
      refine ⟨?_, ?_, ?_⟩
      . simp at *
        apply gcomp_still_valid
      . simp at *
        exact rhs s1_star_s2_with_t0 s1_stars_s3_with_em
      . simp
        apply no_input_in_t0







/-
OUTPUTS: theorems and lemmas managing the output case of the proof
-/

theorem gcompf_output_trace_contains_output {T f g} (st1 st2 st3: State _ _) (io: T) (t : List (IOEvent ℕ)) (h_noinp: ∀ x, IOEvent.input 0 ⟨T, x⟩ ∉ t)
(h_input: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_output: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T))
(h_st1: st1.module = NatModule.gcompf T f g)
(h_st2: st2.module = NatModule.gcompf T f g)
(h_st3: st3 = ⟨ (∅ , ∅ ), (NatModule.gcompf T f g)⟩ ):
@step _ _ _ st1 [IOEvent.output 0 ⟨ T, io⟩]  st2
→ @star _ _ (state_transition (NatModule.gcompf T f g)) st1 t st3
→ ∃ t0, t = [IOEvent.output 0 ⟨ T, io⟩] ++ t0  ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) st2 t0 st3:= by
  intro s1_steps_s2 s1_stars
  revert st2
  induction s1_stars with
  | refl st3 =>
    intro st2 h_st2 s1_steps_s2
    simp at *
    rcases h_st3 with ⟨ eq4, eq5 ⟩
    subst_vars
    cases s1_steps_s2
    try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
    rename_i s1Fst Eq trans
    simp at *
  | step  st4 st5 st6 l1 l2  st4_steps_st5 st5_stars_empty =>
    intro st2 h_st2 s1_steps_s2
    rcases st1 with ⟨ s1, mod1⟩; rcases st2 with ⟨ s2, mod2 ⟩; rcases st3 with ⟨ s3, mod3⟩; rcases st4 with ⟨ s4, mod4⟩; rcases st5 with ⟨ s5, mod5⟩; rcases st6 with ⟨ s6, mod6⟩
    simp at *
    rcases h_st3 with ⟨ eq1, eq2 ⟩
    subst_vars
    cases st4_steps_st5 with
    | input s1Io Eq =>
      rename_i ip s1Fst Tpe iH
      rcases Tpe with ⟨G, x⟩
      subst_vars
      simp at *
      have eqTpe := h_input G x ip
      simp at eqTpe
      rcases eqTpe with ⟨ eq1, eq2⟩
      subst_vars
      have contra := (h_noinp x).left
      simp at contra
    | output s1Io Eq  =>
      rename_i ip s1Fst Tpe iH
      clear iH
      exists l2
      simp at *
      rcases Tpe with ⟨ G, x ⟩
      cases s1_steps_s2
      rename_i s4Fst eq s4Snd; rcases eq; subst_vars
      rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
      have out := h_output G x ip; simp at out; rcases out; subst_vars; simp at *
      rcases s1Io with ⟨ a,b,c ⟩ ; rcases Eq with ⟨ e, f ⟩ ;rcases s2 with ⟨ s21, s22 ⟩; rcases s5 with ⟨ s51, s52 ⟩ ; subst_vars; simp at *
      exact st5_stars_empty



    | internal =>
      rename_i Inp  int trans iH
      simp at *
      have iH_ := iH h_noinp h_input h_output
      simp at *; clear iH
      cases s1_steps_s2
      rename_i s4Fst req s4Snd; rcases req; subst_vars
      cases int with
      | head =>
        rcases s5; simp at trans; subst_vars
        rcases trans; rename_i l1 l2 head tail
        subst_vars
        have empt := @gcompf_empty_spec T f g s2;
        have s := @star.plus_one _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ empt
        have out := @gcompf_output_spec T f g (∅ , (s2.snd ++ map g s2.fst) ) io
        have iH := iH_ ⟨ (∅ , (s2.snd ++ map g s2.fst) ), (NatModule.gcompf T f g) ⟩;
        simp at *; clear iH_
        have iH_ := iH out; rcases iH_ with ⟨ t0, eq, fin_s ⟩ ; clear iH
        have fin := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) _ _ _ _ _ s fin_s
        exists t0
      | tail =>
        simp at *
        rename_i s
        rcases s





















theorem gcompf_output_transitive { T f g} (s1 s2 s3 : List T × List T) (t t0: List (IOEvent ℕ)) (io: T)
(h_input: (∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t0 → (n = 0) ∧ G = T))
(h_output: (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t0 → (n = 0) ∧ G = T))
(h_noinp: ∀ x, IOEvent.input 0 ⟨T, x⟩ ∉ t0)
: @reachable _ _ (state_transition (NatModule.gcompf T f g)) t  ⟨ s1, (NatModule.gcompf T f g)⟩
→ ( ∀ x, .input 0 ⟨T, x⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s1, (NatModule.gcompf T f g)⟩ t0 ⟨(∅, ∅), (NatModule.gcompf T f g )⟩
→ gcompf_P (t ++ t0) f g
→ @step _ _ _ ⟨ s1, (NatModule.gcompf T f g)⟩ [IOEvent.output 0 ⟨ T, io⟩]  ⟨s3, (NatModule.gcompf T f g) ⟩
→ ∃ tn, gcompf_P (t ++ [IOEvent.output 0 ⟨T, io ⟩] ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s3, (NatModule.gcompf T f g) ⟩  tn ⟨(∅, ∅), (NatModule.gcompf T f g )⟩ ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
    intro s1_reachable ⟨no_input_in_t0, s1_star_s2_with_t0⟩ P_for_t_t0 s1_stars_s3_with_em
    have final_res := @gcompf_output_trace_contains_output T f g  ⟨ s1, (NatModule.gcompf T f g)⟩  ⟨ s3, (NatModule.gcompf T f g)⟩  ⟨ (∅, ∅ ), (NatModule.gcompf T f g)⟩ io t0 h_noinp h_input h_output
    simp at final_res
    rcases (final_res s1_stars_s3_with_em s1_star_s2_with_t0) with ⟨l1, toeq, s3_stars_empty⟩
    subst_vars
    exists l1
    simp at *
    constructor
    exact P_for_t_t0
    constructor
    exact s3_stars_empty
    exact h_noinp

/-
EMPTY: theorems to prove the  empty case
-/

lemma gcompf_reachable_states {T} (f g: T → T) (t: List (IOEvent ℕ )) (s1 s2: (List T × List T)):
@reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s1, (NatModule.gcompf T f g ) ⟩
→ @reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s2, (NatModule.gcompf T f g ) ⟩
→ s1.snd ++ s1.fst.map g = s2.snd ++ s2.fst.map g := by
  sorry -- have to prove some kind of preservation
  -- if ppty holds on s1 s2, if you do a step from s1 to s1' with t, and s2-[t]->s2', then this ppty should still hold on s1' s2'
  -- then want to do it on star

-- maybe go to a s_final instead of (∅, ∅) ?
/-
  if two states are the "same" [à un flush près] = have the same "future data", then if they both flush out their "future data" the same way and end up in the empty state
 -/
lemma gcompf_computational_equiv {T} (f g) (s1 s3 : List T × List T) (t : List (IOEvent ℕ)) :
(s1.snd ++ s1.fst.map g = s3.snd ++ s3.fst.map g)
→ (∀ x, IOEvent.input 0 ⟨T, x⟩ ∉ t)
→ (@star _ _ (NatModule.gcompf T f g).state_transition { state := s1, module := (NatModule.gcompf T f g) } t { state := (∅, ∅), module := (NatModule.gcompf T f g) }
  ↔ @star _ _ (NatModule.gcompf T f g).state_transition { state := s3, module := (NatModule.gcompf T f g) } t { state := (∅, ∅), module := (NatModule.gcompf T f g) }) := by
  intros reachable_equiv_states no_input
  induction t -- Proof by induction on the non-input trace t ?
  case nil =>
    sorry
  case cons h t ih =>
    sorry

theorem gcompf_reachness_empty_2 {T f g} (t t0: List (IOEvent ℕ )) (s1 s2 s3: (List T × List T)):
@reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s1, (NatModule.gcompf T f g ) ⟩
→ @reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s2, (NatModule.gcompf T f g ) ⟩
→ (∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s1, (NatModule.gcompf T f g ) ⟩  t0 ⟨ (∅, ∅), (NatModule.gcompf T f g ) ⟩
→ gcompf_P (t ++ t0) f g
→ @step _ _ _ ⟨ s2, (NatModule.gcompf T f g ) ⟩ [] ⟨ s3, (NatModule.gcompf T f g ) ⟩
→ ∃ tn, gcompf_P (t ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s3, (NatModule.gcompf T f g ) ⟩  tn ⟨ (∅, ∅), (NatModule.gcompf T f g ) ⟩ ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  intros reachable_s1 reachable_s2 h_t0 h_P s2_step_s3
  let M := (NatModule.gcompf T f g )
  obtain ⟨ h_t0_input, h_t0_s1star ⟩ := h_t0
  have reachable_s3 : @reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s3, M ⟩ := by
    rcases reachable_s2 with ⟨s0, h_init, h_star_to_empty⟩
    apply Exists.intro s0
    apply And.intro
    case left => assumption
    case right =>
      rw [@star_eq_star_rev _ _ M.state_transition]
      rw [← List.append_nil t]
      apply @star_rev.step _ _ M.state_transition
      . assumption
      . let star_rev_iff_star := @star_eq_star_rev _ _ M.state_transition s0 { state := s2, module := M } t
        apply star_rev_iff_star.mp
        assumption
  cases h_t0: h_t0_s1star
  case refl =>
    have s2_empty : s2 = (∅, ∅) := by
      have h := gcompf_reachable_states f g t (∅, ∅) s2 reachable_s1 reachable_s2
      simp at h
      exact Prod.ext_iff.mpr (id (And.symm h))
    have empty_step_s3: step { state := (∅, ∅), module := NatModule.gcompf T f g } [] { state := s3, module := NatModule.gcompf T f g } := by
      rw [s2_empty] at s2_step_s3
      assumption
    exists []
    simp at *
    apply And.intro
    case left => assumption
    case right =>
      have s3_empty : s3 = (∅, ∅) := by
        have h := gcompf_reachable_states f g t (∅, ∅) s3 reachable_s1 reachable_s3
        simp at h
        exact Prod.ext_iff.mpr (id (And.symm h))
      rw [s3_empty]
      dsimp
      exact h_t0_s1star
  case step s4 t1 t2 s1_step_s4 ih =>
    exists (t1++t2)
    apply And.intro
    case left =>
      assumption
    case right =>
      apply And.intro
      case right =>
        assumption
      case left =>
        have s1_equiv_s3 := gcompf_reachable_states f g t s1 s3 reachable_s1 reachable_s3
        -- big lemma, unsure how to prove :
        have star_equiv := gcompf_computational_equiv f g s1 s3 (t1 ++ t2) s1_equiv_s3 h_t0_input
        apply star_equiv.mp
        exact h_t0_s1star

theorem gcompf_reachness_empty {T f g} (t t0: List (IOEvent ℕ )) (s1 s3: (List T × List T)): @reachable _ _ (state_transition (NatModule.gcompf T f g)) t ⟨ s1, (NatModule.gcompf T f g ) ⟩
→ ( ∀ x, .input 0 ⟨ T, x ⟩ ∉ t0) ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s1, (NatModule.gcompf T f g ) ⟩  t0 ⟨ (∅, ∅), (NatModule.gcompf T f g ) ⟩
→ gcompf_P (t ++ t0) f g
→ @step _ _ _ ⟨ s1, (NatModule.gcompf T f g ) ⟩  [] ⟨ s3, (NatModule.gcompf T f g ) ⟩
→ ∃ tn, gcompf_P (t ++ tn) f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) ⟨ s3, (NatModule.gcompf T f g ) ⟩  tn ⟨ (∅, ∅), (NatModule.gcompf T f g ) ⟩ ∧ ∀ x, .input 0 ⟨T, x ⟩ ∉ tn:= by
  sorry
  /-
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
      assumption
      -/



/-- Still have to define the assumptions of the lemma -/
theorem input_output_single_tpe {T} (t : Trace Nat):
((∀ G x n, IOEvent.input n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T) ∧ (∀ G x n, IOEvent.output n ⟨G, x⟩  ∈ t → (n = 0) ∧ G = T)) := by
  sorry
/--
MAIN PROOF: here lies the main proof of the liveness of a circuit
-/

theorem init_imp_empty {T f g} (s1: State _ _): @StateTransition.init _ _ (state_transition (NatModule.gcompf T f g)) s1 → s1 = ⟨(∅, ∅),  (NatModule.gcompf T f g)⟩:= by
  intro s1Init
  rcases s1Init with ⟨initS, s1Mod⟩
  simp [drunfold] at initS
  rcases s1 with ⟨st1, mod1 ⟩
  simp at *
  exact And.intro initS s1Mod
-- diff with liveness: steps for given s1 s2 & ∃s3, s2-[t']*>s3 instead of behavior (t++t')
theorem gcompf_liveness_simp {t : Trace Nat} {T f g}
(s1 s2: State _ _)
(h_s1: s1.module = (NatModule.gcompf T f g))
(h_s2: s2.module = (NatModule.gcompf T f g))
(h: @StateTransition.init _ _ (state_transition (NatModule.gcompf T f g)) s1 ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s1 t s2):
  ∃ t', gcompf_P (t ++ t') f g ∧ @star _ _ (state_transition (NatModule.gcompf T f g)) s2 t' ⟨(∅, ∅),  (NatModule.gcompf T f g)⟩  ∧ (∀ x, .input 0 ⟨T, x⟩ ∉ t'):= by
    have ⟨h_in, h_out⟩  := @input_output_single_tpe T t
    have starConv := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 t).mp h.right
    induction starConv with
    | refl =>
      exists []
      simp [gcompf_P]
      have s1Eq := @init_imp_empty T f g s1 h.left
      subst_vars
      exact h.right
    | step s3 s4 t1 t2 s3_steps_s4 s1_convstars_s3 iH =>
      have s1_stars_s3  := (@star_eq_star_rev _ _ (state_transition (NatModule.gcompf T f g)) _ _ _).mpr s1_convstars_s3
      clear s1_convstars_s3
      simp at *
      have new_substs := steps_preserve_mod (NatModule.gcompf T f g) s1_stars_s3; rw [h_s1] at new_substs
      have ⟨h_in_, h_out_⟩  := (@input_output_single_tpe T t1)
      have iHRes := iH new_substs h.left s1_stars_s3 h_in_ h_out_
      clear iH new_substs
      rcases iHRes with ⟨tr, comp_l1_tr, s3_stars_empty, tr_is_empty⟩
      have s3_steps_s4_ := s3_steps_s4
      clear h_in_ h_out_
      cases s3_steps_s4 with
      | input =>
        rename_i ip1 st1 s3mod combTpe s3Trans combTpeEq
        rcases s3
        rename_i s3 mod3
        subst h_s2
        have finalResT := @gcompf_input_transitive T f g
        simp [reachable] at finalResT
        rcases combTpe with ⟨TT, inp ⟩
        have h_in_assum := h_in TT inp ip1
        simp at h_in_assum
        rcases h_in_assum with ⟨ nEq, TypeEq ⟩
        subst nEq
        subst TypeEq
        have ⟨h_in_, h_out_⟩  := (@input_output_single_tpe TT tr)
        have finalRes := finalResT s3.1 s3.2 st1.1 st1.2 t1 tr inp h_in_ h_out_ tr_is_empty s1 h.left s1_stars_s3 tr_is_empty s3_stars_empty comp_l1_tr s3_steps_s4_
        cases finalRes
        rename_i tn final
        exists tn
      | output =>
        rename_i ip1 st1 s3mod combTpe s3Trans combTpeEq
        rcases s3
        rename_i s3 mod3
        subst h_s2
        have finalResT := @gcompf_output_transitive T f g
        simp [reachable] at finalResT
        rcases combTpe with ⟨TT, inp ⟩
        have h_out_assum := h_out TT inp ip1
        simp at h_out_assum
        rcases h_out_assum with ⟨ nEq, TypeEq ⟩
        subst nEq
        subst TypeEq
        have ⟨h_in_, h_out_⟩  := (@input_output_single_tpe TT tr)
        have finalRes := finalResT s3.1 s3.2 st1.1 st1.2 t1 tr inp h_in_ h_out_ tr_is_empty s1 h.left s1_stars_s3 tr_is_empty s3_stars_empty comp_l1_tr s3_steps_s4_
        cases finalRes
        rename_i tn final
        exists tn
      | internal =>
        rename_i RI st3 RIInS3 stepS3
        simp at *
        rcases s3 with ⟨st3, mod2⟩
        rename_i st4
        subst h_s2
        have lemm_use := @gcompf_reachness_empty T f g t1 tr st3 st4
        simp [reachable] at lemm_use
        have lemm_use_ := lemm_use s1 h.left s1_stars_s3 tr_is_empty s3_stars_empty comp_l1_tr
        simp at *
        clear lemm_use
        have lemm_use := lemm_use_ s3_steps_s4_
        assumption




theorem gcompf_liveness2 {t : Trace Nat} {T f g}(h_steps: @behaviour _ _ (state_transition (NatModule.gcompf T f g)) t)
(h_init_imp_mod: ∀s, @StateTransition.init _ _ (state_transition (NatModule.gcompf T f g)) s  → s.module = (NatModule.gcompf T f g)):
  ∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompf T f g)) (t ++ t') ∧ ∀ x, .input 0 ⟨T, x⟩ ∉ t' := by
    simp [behaviour] at h_steps
    match h_steps with
    | ⟨ s1, s1_init_step, s2, s1_star_s2_t ⟩  =>
      have s1_mod_eq := h_init_imp_mod s1 s1_init_step
      have s2_mod_eq := steps_preserve_mod (NatModule.gcompf T f g) s1_star_s2_t
      rw [s1_mod_eq] at s2_mod_eq
      have induct_star_res := gcompf_liveness_simp s1 s2 s1_mod_eq s2_mod_eq (And.intro s1_init_step s1_star_s2_t)
      rcases induct_star_res with ⟨i1, i2,i3, i4 ⟩
      exists i1
      constructor
      . exact i2
      . constructor
        . simp [behaviour]
          have starComb := @star.trans_star _ _ (state_transition (NatModule.gcompf T f g)) s1 s2 ⟨(∅, ∅),  (NatModule.gcompf T f g)⟩ t i1 s1_star_s2_t i3
          exists s1
          constructor
          . exact s1_init_step
          . exists ⟨(∅, ∅),  (NatModule.gcompf T f g)⟩
        . exact i4
