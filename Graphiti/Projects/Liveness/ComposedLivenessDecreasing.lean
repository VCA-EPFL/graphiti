/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maï-Linh Cordonnier, Lorenzo Padrini
-/

import Graphiti.Core.ModuleLemmas
import Graphiti.Core.StateTransition
import Graphiti.Projects.Liveness.ComposedModuleHist
import Graphiti.Projects.Liveness.StateTransitionLiveness
import Graphiti.Core.Trace


open Graphiti
open Graphiti.Module


-- COMPUTATION: different functions to compute the weight of the state

-- Calc #inputs - #outputs in history
def count_in_out (history : List (IOEvent Nat)) : Nat :=
  history.foldl (fun acc event =>
    match event with
    | IOEvent.input _ _ => acc + 1
    | IOEvent.output _ _ => acc - 1
  ) 0

def gcompfHistWeight {T} (f g : T -> T) (s : Graphiti.Module.State Nat ((List T) × ((List T) × (Trace Nat)))) : Nat :=
  let s_stt := s.state;
  2 * List.length s_stt.fst + List.length s_stt.snd.fst + count_in_out s_stt.snd.snd


--PROPERTIES: properties that need to be followed at various stages of the proof for the system to be live

def gcompf_P {T} (t: Trace Nat)(f g: T → T) : Prop :=
  ∀ in1, .input 0 ⟨ T, in1 ⟩ ∈ t → .output 0 ⟨ T, g (f (in1)) ⟩ ∈ t

def gcompf_decreasing_P {T} {f g: T → T} (z: Nat) :=
   ∀ (s: Graphiti.Module.State ℕ (List T × List T × Trace Nat)), @gcompfHistWeight _ f g s = z
   → (∃ t, @reachable _ _  (Module.state_transition (NatModule.gcompfHist T f g)) t s)
   → ∃ s' t0, (@gcompfHistWeight _ f g s' = 0) ∧  @star _ _ (Module.state_transition (NatModule.gcompfHist T f g)) s t0 s'

def gcompf_wellfounded_P {T}

-- REACHABILITY: some useful general lemmas on reachability, can be moved to a more spcific file
theorem reachable_inp_module {T} {f g: T → T}
(s: State ℕ (List T × List T × Trace Nat))
(t: Trace ℕ)
(h_reach: @reachable _ _  (state_transition (NatModule.gcompfHist T f g)) t s):
s.module = NatModule.gcompfHist T f g := by
  simp [reachable, StateTransition.init] at h_reach
  rcases h_reach with ⟨s2, s2_inits, s2_stars⟩
  rcases s2_inits with ⟨s2_state, s2_module⟩
  have s_mod := steps_preserve_mod (NatModule.gcompfHist T f g) s2_stars
  rcases s2 with ⟨ s2_state, s2_mod ⟩; simp at s2_module; subst s2_module; simp at s_mod
  exact s_mod

theorem reachable_and_star_imp_reachable {T} {f g: T → T}
(s1 s2: State ℕ (List T × List T × Trace Nat))
(t t0: Trace ℕ)
(h_reach: @reachable _ _  (state_transition (NatModule.gcompfHist T f g)) t s1)
(h_star: @star _ _ (state_transition (NatModule.gcompfHist T f g)) s1 t0 s2):
@reachable _ _  (state_transition (NatModule.gcompfHist T f g)) (t ++ t0) s2 := by
  simp [reachable] at ⊢ h_reach; rcases h_reach with ⟨ s, s_init, s_stars ⟩
  exists s
  constructor; exact s_init
  exact @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ s_stars h_star

-- GCOMPF_LOGIC : some small theorems relating the module to it's internal logic

theorem gcompf_empty_spec {T f g} (st1: List T × List T × Trace ℕ) :
@step _ _ _ ⟨(st1.fst, st1.snd.fst, st1.snd.snd), NatModule.gcompfHist T f g ⟩ []
  { state := (∅, st1.snd.fst ++ (st1.fst.map g), st1.snd.snd), module := NatModule.gcompfHist T f g } := by
  rcases st1 with ⟨a,b ⟩
  simp at *
  constructor <;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  . simp at *
    constructor
  . simp [NatModule.gcompfHist] at *

theorem gcompf_output_spec {T f g} (st1: List T × List T × Trace ℕ) (io: T):
@step _ _ _ ⟨(st1.fst, (io) :: st1.snd.fst, st1.snd.snd), NatModule.gcompfHist T f g ⟩ [IOEvent.output 0 ⟨T, io⟩]
  { state := (st1.fst, st1.snd.fst, IOEvent.output 0 ⟨T, io⟩ :: st1.snd.snd), module := NatModule.gcompfHist T f g } := by
  rcases st1 with ⟨a,b ⟩
  simp at *
  constructor <;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  . simp at *
    constructor <;> exact rfl
  . simp [NatModule.gcompfHist] at *



theorem gcompf_nonzerow_imp_nonempty {T} {f g: T → T}:
  ∀ (s: Graphiti.Module.State ℕ (List T × List T × Trace Nat)), @gcompfHistWeight _ f g s > 0
  → s.state.fst ≠ ∅ ∨ s.state.snd.fst ≠ ∅ := by
  intro s weight_is_positive
  by_contra; rename_i state_nonempty; simp at state_nonempty; rcases state_nonempty with ⟨ s1empty, s2empty ⟩
  simp [gcompfHistWeight, s1empty, s2empty] at weight_is_positive
  sorry




theorem bigger_ind_imp_smaller {T} {f g: T → T} (n: ℕ)(h: ∀ (y : ℕ), WellFoundedRelation.rel y (n + 1) → @gcompf_wf_P T f g  y):
∀ (y : ℕ), WellFoundedRelation.rel y (n) → @gcompf_wf_P T f g y := by
  intro y assum
  apply h
  constructor
  simp; simp [WellFoundedRelation.rel] at assum
  cases assum
  simp; rename_i n sizeofn
  simp at *
  exact Nat.le_of_succ_le sizeofn

theorem gcompf_with_step_decreases {T} {f g :T → T} (s1: List T) (hist: Trace ℕ) (head: T) (tail: List T)  (n: ℕ) (h_in : @gcompfHistWeight T f g { state := (s1, head :: tail, hist), module := NatModule.gcompfHist T f g } = n + 1) :
@gcompfHistWeight T f g { state := ([], tail ++ List.map g s1, IOEvent.output 0 ⟨T, head⟩ :: hist), module := NatModule.gcompfHist T f g } = n:= by
  simp [gcompfHistWeight] at ⊢ h_in
  rw [Nat.add_comm]
  sorry

theorem gcompf_ind_wf {T} {f g: T → T} : ∀ z, @gcompf_wf_P T f g z := by
  intro z
  induction z using WellFounded.induction
  . apply WellFoundedRelation.wf
  . rename_i n iH
    simp [gcompf_wf_P]
    intro s weight_is_n t0 s_is_reachable
    revert s t0
    induction n with
    | zero =>
      intro s weigth_is_zero t0 t0_is_reachable
      exists s
      constructor
      exact weigth_is_zero
      exists []
      apply @star.refl _ _ (state_transition (NatModule.gcompfHist T f g))
    | succ n iHn =>
      have iHn_ := iHn (@bigger_ind_imp_smaller T f g n iH)
      clear iH iHn
      intro s weight_is_nonzero t0 s_is_reachable
      have s_mod := @reachable_inp_module T f g s t0 s_is_reachable;
      rcases s with ⟨ ⟨ s1, s2, hist⟩ , mod ⟩; simp at s_mod; subst s_mod
      have step1 := @gcompf_empty_spec T f g ⟨s1, s2, hist⟩ ; simp at step1
      have nonempty_s := @gcompf_nonzerow_imp_nonempty T f g ⟨ ⟨s1, s2, hist⟩, NatModule.gcompfHist T f g ⟩; simp [weight_is_nonzero] at nonempty_s
      cases nonempty_s with
      | inl s1_nonempty =>
        cases s1 <;> simp at s1_nonempty; try rename_i head tail
        cases s2 with
        | nil => sorry
        | cons => sorry
      | inr s2_nonempty =>
        cases s2 <;> simp at s2_nonempty; try rename_i head tail
        have step2 := @gcompf_output_spec T f g ⟨[],  tail ++ List.map g s1, hist⟩ head ; simp at step2
        have total_step := @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step1) (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step2); clear step1 step2 s2_nonempty; simp at total_step
        have s'_size := @gcompf_with_step_decreases T f g s1 hist head tail n weight_is_nonzero
        have s'_reachable := (@reachable_and_star_imp_reachable T  f g { state := (s1, head :: tail, hist), module := NatModule.gcompfHist T f g } { state := ([], tail ++ List.map g s1, IOEvent.output 0 ⟨T, head⟩ :: hist), module := NatModule.gcompfHist T f g } t0 [IOEvent.output 0 ⟨T, head⟩] s_is_reachable total_step)
        have iHn := iHn_ { state := ([], tail ++ List.map g s1, IOEvent.output 0 ⟨T, head⟩ :: hist), module := NatModule.gcompfHist T f g } s'_size (t0 ++ [IOEvent.output 0 ⟨T, head⟩]) s'_reachable; clear s'_reachable s'_size weight_is_nonzero s_is_reachable
        rcases iHn with ⟨s', s'_is_zero, t0, s_empty_stars_s'⟩
        exists s'
        constructor; exact s'_is_zero
        exists ( [IOEvent.output 0 ⟨T, head⟩] ++ t0)
        exact @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ total_step s_empty_stars_s'


theorem gcompf_wf_P_is_wellfounded :
(WellFounded ())


theorem gcompf_wellness_implies_liveness {T} (f g: T → T) (t : Trace ℕ)
(h_steps: @behaviour _ _ (state_transition (NatModule.gcompfHist T f g)) t) :
∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompfHist T f g)) (t ++ t') := by
  have iH := @gcompf_ind_wf T f g; simp [gcompf_wf_P] at iH
  simp [behaviour] at h_steps
  rcases h_steps with ⟨s1, s1_inits , s2, s1_stars_s2⟩
  have iH_ := iH (@gcompfHistWeight T f g s2) s2; simp [reachable] at iH_;
  clear iH
  have iH := iH_ t s1 s1_inits s1_stars_s2
  rcases iH with ⟨ s3, s3_weights_zero, t0, s2_stars_s3⟩
  exists t0
  constructor
  . simp [gcompf_P]
    intro in1 in1_in_t_or_t0
    have gcom
  . simp [behaviour]
    exists s1
    constructor; exact s1_inits
    exists s3; exact @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ s1_stars_s2 s2_stars_s3
