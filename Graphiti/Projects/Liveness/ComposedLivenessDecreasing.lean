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
  List.length s_stt.fst + List.length s_stt.snd.fst


--PROPERTIES: properties that need to be followed at various stages of the proof for the system to be live

def gcompf_P {T} (t: Trace Nat)(f g: T → T) : Prop :=
  ∀ in1, .input 0 ⟨ T, in1 ⟩ ∈ t → .output 0 ⟨ T, g (f (in1)) ⟩ ∈ t

def gcompf_wf_P {T} (f g: T → T) (z: Nat) :=
   ∀ (s: Graphiti.Module.State ℕ (List T × List T × Trace Nat)), @gcompfHistWeight _ f g s = z
   → (∃ t, @reachable _ _  (Module.state_transition (NatModule.gcompfHist T f g)) t s)
   → ∃ s' t0, (@gcompfHistWeight _ f g s' = 0) ∧  @star _ _ (Module.state_transition (NatModule.gcompfHist T f g)) s t0 s' ∧ ∀ io n, (IOEvent.input io n) ∉ t0



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

theorem gcompf_input_spec {T f g} (st1: List T × List T × Trace ℕ) (io: T):
@step _ _ _ ⟨(st1.fst, st1.snd.fst, st1.snd.snd), NatModule.gcompfHist T f g ⟩ [IOEvent.input 0 ⟨T, io⟩]
  { state := (st1.fst ++ [(f io)], st1.snd.fst , IOEvent.input 0 ⟨T, io⟩ :: st1.snd.snd), module := NatModule.gcompfHist T f g } := by
  rcases st1 with ⟨a,b ⟩
  simp at *
  constructor <;> try rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
  . simp at *
    constructor <;> exact rfl
  . simp [NatModule.gcompfHist] at *

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
  exact Nat.succ_inj'.mp h_in

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
      simp
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
        | nil =>
          sorry
        | cons => sorry
      | inr s2_nonempty =>
        cases s2 <;> simp at s2_nonempty; try rename_i head tail
        have step2 := @gcompf_output_spec T f g ⟨[],  tail ++ List.map g s1, hist⟩ head ; simp at step2
        have total_step := @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step1) (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step2); clear step1 step2 s2_nonempty; simp at total_step
        have s'_size := @gcompf_with_step_decreases T f g s1 hist head tail n weight_is_nonzero
        have s'_reachable := (@reachable_and_star_imp_reachable T  f g { state := (s1, head :: tail, hist), module := NatModule.gcompfHist T f g } { state := ([], tail ++ List.map g s1, IOEvent.output 0 ⟨T, head⟩ :: hist), module := NatModule.gcompfHist T f g } t0 [IOEvent.output 0 ⟨T, head⟩] s_is_reachable total_step)
        have iHn := iHn_ { state := ([], tail ++ List.map g s1, IOEvent.output 0 ⟨T, head⟩ :: hist), module := NatModule.gcompfHist T f g } s'_size (t0 ++ [IOEvent.output 0 ⟨T, head⟩]) s'_reachable; clear s'_reachable s'_size weight_is_nonzero s_is_reachable
        rcases iHn with ⟨s', s'_is_zero, t1, s_empty_stars_s'⟩
        exists s'
        constructor; exact s'_is_zero
        exists ( [IOEvent.output 0 ⟨T, head⟩] ++ t1)
        constructor
        . exact @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ total_step s_empty_stars_s'.left
        . simp; exact s_empty_stars_s'.right


-- DECREASE PROOFS: here we link the fact that the case is zero with the fact that it always decreases

theorem star_and_in_state_imp_out_state {T}
{f g: T → T} {st1 st2 st3: State ℕ (List T × List T × Trace ℕ)} {t: Trace ℕ}
(io: T)
(h_mod: st1.module = NatModule.gcompfHist T f g)
(h_step: @step _ _ _ st1 [IOEvent.input 0 ⟨T, io⟩] st2)
(h_star: @star _ _ (state_transition (NatModule.gcompfHist T f g)) st2 t st3)
(h_empty: gcompfHistWeight f g st3 = 0):
IOEvent.output 0 ⟨T, g ( f io) ⟩ ∈ t := by
  simp [gcompfHistWeight] at h_empty; rcases h_empty with ⟨ eq1, eq2 ⟩
  revert st1 io
  induction h_star with
  | refl st4 =>
    intro st1 io h_mod h_step
    cases h_step <;> simp at *
    rename_i s4 st1Fst st2Fst TpeEq
    rcases TpeEq; rcases s4 with ⟨ s41, s42, s4hist ⟩; rcases st1 with ⟨ ⟨ s11, s12, s1hist ⟩, mod1 ⟩; simp at *; subst_vars
    rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
    simp at *
  | step st4 st5 st6 l1 l2 st4_steps_st5 st5_stars_st6 iH =>
    intro st1 io st1mod st1_steps_st4
    have iH_ := @iH eq1 eq2
    sorry






theorem star_and_in_imp_out {T}
{f g: T → T} {st1 st2: State ℕ (List T × List T × Trace ℕ)} {t: Trace ℕ}
(io: T)
(h_mod: st1.module = NatModule.gcompfHist T f g)
(h_star: @star _ _ (state_transition (NatModule.gcompfHist T f g)) st1 t st2)
(h_empty: gcompfHistWeight f g st2 = 0):
IOEvent.input 0 ⟨T, io ⟩ ∈ t → IOEvent.output 0 ⟨T, g ( f io) ⟩ ∈ t := by
  have keep_empty := h_empty
  simp [gcompfHistWeight, count_in_out] at h_empty
  rcases h_empty with ⟨ eq1 , eq2 ⟩
  intro ioInT
  induction h_star
  . rename_i st3
    simp at *
  . rename_i st3 st4 st5 t1 t2  st3_steps_st4 st4_stars_st5 iH
    have mod := step_preserve_mod (NatModule.gcompfHist T f g) st3_steps_st4; rcases st3 with ⟨ s3, mod3 ⟩; subst h_mod
    have iH_ := iH mod keep_empty eq1 eq2; clear iH
    simp at ioInT;
    cases ioInT with
    | inl io_in_t1 =>
      simp; right
      have keep_step := st3_steps_st4
      rcases st3_steps_st4 <;> simp at *
      rename_i a b c d e p
      rcases io_in_t1 with ⟨ g, h,i ⟩; subst_vars
      have lemm := @star_and_in_state_imp_out_state T f g { state := s3, module := NatModule.gcompfHist T f g } { state := (s3.fst.concat (f c), s3.snd.fst, IOEvent.input 0 ⟨T, c⟩ :: s3.snd.snd), module := NatModule.gcompfHist T f g } st5 t2; simp at lemm keep_step st4_stars_st5
      exact lemm io keep_step st4_stars_st5 keep_empty
    | inr io_in_t2 =>
      have iH := iH_ io_in_t2
      exact List.mem_append_right t1 (iH_ io_in_t2)



-- MAIN PROOF: where the magic happens

theorem gcompf_wellness_implies_liveness {T} (f g: T → T) (t : Trace ℕ)
(h_steps: @behaviour _ _ (state_transition (NatModule.gcompfHist T f g)) t) :
∃ t', gcompf_P (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompfHist T f g)) (t ++ t') := by
  have iH := @gcompf_ind_wf T f g; simp [gcompf_wf_P] at iH
  simp [behaviour] at h_steps
  rcases h_steps with ⟨s1, s1_inits , s2, s1_stars_s2⟩
  have iH_ := iH (@gcompfHistWeight T f g s2) s2; simp [reachable] at iH_;
  clear iH
  have iH := iH_ t s1 s1_inits s1_stars_s2
  rcases iH with ⟨ s3, s3_weights_zero, t0, s2_stars_s3, input_notin_t0⟩
  exists t0
  have s1_stars_s3 := @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ s1_stars_s2 s2_stars_s3
  constructor
  . simp [gcompf_P]
    intro in1 in1_in_t_or_t0
    have s1_module :=  s1_inits
    rcases s1_module with ⟨ temp, s1_mod ⟩; clear temp
    have io_val := star_and_in_imp_out in1 s1_mod s1_stars_s3 s3_weights_zero
    simp at io_val
    exact io_val in1_in_t_or_t0
  . simp [behaviour]
    exists s1
    constructor; exact s1_inits
    exists s3
