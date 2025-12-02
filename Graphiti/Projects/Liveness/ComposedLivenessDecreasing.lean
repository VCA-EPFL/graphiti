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

-- Calc #inputs in history
def count_in (history : List (IOEvent Nat))  : Nat :=
  match history with
  | [] => 0
  | x :: xs =>
    match x with
    | IOEvent.input _ _ => 1 + count_in xs
    | IOEvent.output _ _ => count_in xs
-- Calc #outputs in history
def count_out (history : List (IOEvent Nat)) : Nat :=
  match history with
  | [] => 0
  | x :: xs =>
    match x with
    | IOEvent.input _ _ => count_out xs
    | IOEvent.output _ _ => 1 + count_out xs

-- Calc #inputs - #outputs in history USE LIST OF PARTITION
def count_in_out (history : List (IOEvent Nat))  : Nat :=
  count_in history  - count_out history

def gcompfHistWeight {T} (f g : T -> T) (s : State Nat ((List T) × ((List T) × (Trace Nat)))) : Nat :=
  let s_stt := s.state;
  List.length s_stt.fst + List.length s_stt.snd.fst


--PROPERTIES: properties that need to be followed at various stages of the proof for the system to be live

def gcompf_P {T} (t: Trace Nat)(f g: T → T) : Prop :=
  ∀ in1, .input 0 ⟨ T, in1 ⟩ ∈ t → .output 0 ⟨ T, g (f (in1)) ⟩ ∈ t

def gcompf_P_simp {T} (t: Trace Nat)(f g: T → T) : Prop :=
  count_in t = count_out t

def gcompf_wf_P {T} (f g: T → T) (z: Nat) :=
   ∀ (s: Graphiti.Module.State ℕ (List T × List T × Trace Nat)), @gcompfHistWeight _ f g s = z
   → (∃ t, @reachable _ _  (state_transition (NatModule.gcompfHist T f g)) t s)
   → ∃ s' t0, (@gcompfHistWeight _ f g s' = 0) ∧  @star _ _ (state_transition (NatModule.gcompfHist T f g)) s t0 s' ∧ ∀ io n, (IOEvent.input io n) ∉ t0



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


theorem reachable_and_star_imp_reachable {T} (f g: T → T)
{s1 s2: State ℕ (List T × List T × Trace Nat)}
{t t0: Trace ℕ}
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

theorem gcompf_with_empt_step_remains {T} {f g :T → T}  (hist: Trace ℕ) (head: T) (tail1 tail2: List T)  (n: ℕ) (h_in : @gcompfHistWeight T f g { state := (head :: tail1, tail2, hist), module := NatModule.gcompfHist T f g } = n) :
@gcompfHistWeight T f g { state := ([],  tail2 ++ g head :: (List.map g tail1), hist), module := NatModule.gcompfHist T f g } = n:= by
  simp [gcompfHistWeight] at ⊢ h_in
  rw [←h_in]
  exact Nat.add_comm tail2.length (tail1.length + 1)

theorem gcompf_with_out_step_decreases {T}  {s1: List T} {hist: Trace ℕ} {head: T} {tail: List T}  {n: ℕ} (f g :T → T) (h_in : @gcompfHistWeight T f g { state := (s1, head :: tail, hist), module := NatModule.gcompfHist T f g } = n + 1) :
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
          have step2 := @gcompf_output_spec T f g ⟨[], List.map g tail, hist  ⟩ (g head)
          have full_step := @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step1) (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step2); clear step1 step2; simp at full_step
          have weight1 := @gcompf_with_empt_step_remains T f g hist head tail [] (n+1) weight_is_nonzero
          have weight2 := gcompf_with_out_step_decreases f g weight1; clear weight1; simp at weight2
          have news_reachable := reachable_and_star_imp_reachable f g s_is_reachable full_step; simp at news_reachable
          have iH := iHn_ { state := ([], (List.map g tail).append [] ++ List.map g [],IOEvent.output 0 ⟨T, g head⟩ :: hist), module := NatModule.gcompfHist T f g }; simp at iH
          have iH_ := iH weight2 ( t0 ++ [IOEvent.output 0 ⟨ T, g head ⟩]); clear iHn_; simp at *
          have iH__ := iH_ news_reachable; clear iH iH_
          repeat rcases iH__; rename_i s1 prop
          repeat rcases prop;
          rename_i s1_is_zero prop
          exists s1
          constructor
          exact s1_is_zero
          cases prop; rename_i x prop
          exists [IOEvent.output 0 ⟨ T, g head ⟩] ++ x
          constructor
          exact @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ full_step prop.left
          simp; exact prop.right
        | cons h t =>
          have step2 := @gcompf_output_spec T f g ⟨[], t ++ List.map g (head :: tail), hist  ⟩ h
          have full_step := @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step1) (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step2); clear step1 step2; simp at full_step
          have weight1 := @gcompf_with_empt_step_remains T f g hist head tail (h:: t) (n+1) weight_is_nonzero
          have weight2 := gcompf_with_out_step_decreases f g weight1; clear weight1 weight_is_nonzero; simp at weight2
          have news_reachable := reachable_and_star_imp_reachable f g s_is_reachable full_step; simp at news_reachable
          have iH := iHn_ { state := ([], t ++ g head :: List.map g tail, IOEvent.output 0 ⟨T, h⟩ :: hist),module := NatModule.gcompfHist T f g } ; simp at iH
          have iH_ := iH weight2 ( t0 ++ [IOEvent.output 0 ⟨ T, h ⟩]); clear iHn_; simp at *
          have iH__ := iH_ news_reachable; clear iH
          repeat rcases iH__; rename_i s1 prop
          repeat rcases prop;
          rename_i s1_is_zero prop
          exists s1
          constructor
          exact s1_is_zero
          cases prop; rename_i x prop
          exists [IOEvent.output 0 ⟨ T, h ⟩] ++ x
          constructor
          exact @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ full_step prop.left
          simp; exact prop.right

      | inr s2_nonempty =>
        cases s2 <;> simp at s2_nonempty; try rename_i head tail
        have step2 := @gcompf_output_spec T f g ⟨[],  tail ++ List.map g s1, hist⟩ head ; simp at step2
        have total_step := @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step1) (@star.plus_one _ _ (state_transition (NatModule.gcompfHist T f g))  _ _ _ step2); clear step1 step2 s2_nonempty; simp at total_step
        have s'_size := gcompf_with_out_step_decreases f g weight_is_nonzero
        have s'_reachable := (@reachable_and_star_imp_reachable T  f g { state := (s1, head :: tail, hist), module := NatModule.gcompfHist T f g } { state := ([], tail ++ List.map g s1, IOEvent.output 0 ⟨T, head⟩ :: hist), module := NatModule.gcompfHist T f g } t0 [IOEvent.output 0 ⟨T, head⟩] s_is_reachable total_step)
        have iHn := iHn_ { state := ([], tail ++ List.map g s1, IOEvent.output 0 ⟨T, head⟩ :: hist), module := NatModule.gcompfHist T f g } s'_size (t0 ++ [IOEvent.output 0 ⟨T, head⟩]) s'_reachable; clear s'_reachable s'_size weight_is_nonzero s_is_reachable
        rcases iHn with ⟨s', s'_is_zero, t1, s_empty_stars_s'⟩
        exists s'
        constructor; exact s'_is_zero
        exists ( [IOEvent.output 0 ⟨T, head⟩] ++ t1)
        constructor
        . exact @star.trans_star _ _ (state_transition (NatModule.gcompfHist T f g)) _ _ _ _ _ total_step s_empty_stars_s'.left
        . simp; exact s_empty_stars_s'.right







theorem lemma_step {T}
(f g: T → T)
{n z: ℕ}
{t: Trace ℕ}
{s1 s2: State ℕ ((List T) × ((List T) × (Trace Nat)))}
(reach: @StateTransition.step _ _ (state_transition (NatModule.gcompfHist T f g)) s1 t s2 )
(h_zero_: gcompfHistWeight f g s1 = z )
(h_zero: gcompfHistWeight f g s2 = n )
(m_eq: s1.module = (NatModule.gcompfHist T f g))
(assum: count_in s1.state.2.2 = z + count_out s1.state.2.2 )
: count_in s2.state.2.2 = n + count_out s2.state.2.2  := by
  cases reach with
  | input trans TpeEq =>
    rename_i ip st s1fst Tpe
    rcases s1 with ⟨ ⟨ st11, st12, st1hist ⟩, mod1 ⟩; rcases st with ⟨ s1, s2, s1hist ⟩ ; simp at *; subst_vars
    rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
    split at trans
    . subst_vars
      simp at *
      rcases trans with ⟨a, b, c⟩; subst_vars
      simp [count_in, count_out, gcompfHistWeight] at *
      rw [assum]
      ac_rfl
    . rename_i prop
      exfalso
      simp at *
      sorry
  | output trans TpeEq =>
    rename_i ip st s1fst Tpe
    rcases s1 with ⟨ ⟨ st11, st12, st1hist ⟩, mod1 ⟩; rcases st with ⟨ s1, s2, s1hist ⟩ ; simp at *; subst_vars
    rw [PortMap.rw_rule_execution (by simp [drunfold]; rfl)] at *
    split at trans
    . subst_vars
      simp at *
      rcases trans with ⟨a, b, c⟩; cases st12 <;> try (simp at b; rcases b )
      simp at b
      subst_vars
      simp [count_in, count_out, gcompfHistWeight] at *
      rw [assum]
      ac_rfl
    . rename_i prop
      exfalso
      simp at *
      sorry
  | internal trans TpeEq =>
    rename_i ip st
    rcases s1 with ⟨ ⟨ st11, st12, st1hist ⟩, mod1 ⟩; rcases st with ⟨ s1, s2, s1hist ⟩ ; simp at *; subst_vars
    simp [count_in, count_out, gcompfHistWeight] at *
    cases trans
    . rcases TpeEq with ⟨ a, b, c ⟩ ; simp
      rw [assum]
      ac_rfl
    . rename_i c
      cases c













theorem gcompf_weight_of_s1_imp_weight_of_s2 {T}
(f g: T → T)
{n z: ℕ}
{t: Trace ℕ}
{s1 s2: State ℕ ((List T) × ((List T) × (Trace Nat)))}
{m: _}
(reach: @star _ _  m s1 t s2 )
(h_zero: gcompfHistWeight f g s2 = n )
(h_zero_: gcompfHistWeight f g s1 = z )
(m_eq: m = (state_transition (NatModule.gcompfHist T f g)))
(mod: s1.module = NatModule.gcompfHist T f g )
(assum: count_in s1.state.2.2 = z + count_out s1.state.2.2 )
: count_in s2.state.2.2 = n + count_out s2.state.2.2  := by
  revert h_zero h_zero_ assum m_eq z n mod
  induction reach with
  | refl s3 =>
    intro s3_is_n s2_is_n
    grind
  | step  s3 s4 s5 t1 t2 s3_steps_s4 s4_stars_s5 iH =>
    intro n z s5_n s3_z m_trans mod count_eq
    have iH_ := @iH n (@gcompfHistWeight T f g s4) s5_n; clear iH; simp at iH_
    have iH := iH_ m_trans ; clear iH
    subst m_trans
    have s4mod := @step_preserve_mod ℕ _ _ _  s3 t1 s4 s3_steps_s4
    have lemm := @lemma_step T f g (gcompfHistWeight f g s4) z t1 s3 s4 s3_steps_s4 s3_z; simp at lemm
    rcases s3 with ⟨ s3s, mod3 ⟩; rcases s4 with ⟨ s4s, mod4 ⟩
    simp at mod4 mod; subst_vars; simp at *
    apply iH_; clear iH_;
    apply lemm
    exact count_eq

theorem gcompf_weight_eq_num_of_vals {T}
(f g: T → T)
{n: ℕ}
{t: Trace ℕ}
{s: State ℕ ((List T) × ((List T) × (Trace Nat)))}
(h_zero: gcompfHistWeight f g s = n )
(reach: @reachable _ _  (state_transition (NatModule.gcompfHist T f g)) t s )
: count_in s.state.snd.snd = n + count_out s.state.snd.snd  := by
  simp [reachable] at reach
  rcases reach with ⟨ s1, s1_inits, s1_stars_s ⟩
  have cc := @gcompf_weight_of_s1_imp_weight_of_s2 T f g n (@gcompfHistWeight T f g s1)  t s1 s (state_transition (NatModule.gcompfHist T f g)) s1_stars_s h_zero
  simp at cc
  simp [gcompfHistWeight] at cc
  rcases s1_inits with ⟨ s1_init_state, s1_mod ⟩
  rcases s1 with ⟨⟨ s11, s12, s1hist ⟩, mod ⟩
  simp [drunfold] at s1_init_state; rcases s1_init_state with ⟨ s1empty, s2empty, histempty ⟩
  simp at s1_mod
  subst_vars
  simp [count_in, count_out] at cc;
  rw [cc]







theorem gcompf_eq_sum {T}
(f g: T → T)
{t: Trace ℕ}
{s: State ℕ ((List T) × ((List T) × (Trace Nat)))}
(h_zero: gcompfHistWeight f g s = 0 )
(reach: @reachable _ _  (state_transition (NatModule.gcompfHist T f g)) t s )
: count_in t = count_out t  := by
  have num_with_zero := gcompf_weight_eq_num_of_vals f g h_zero reach
  simp at num_with_zero
  sorry

-- MAIN PROOF: where the magic happens

theorem gcompf_wellness_implies_liveness {T} (f g: T → T) (t : Trace ℕ)
(h_steps: @behaviour _ _ (state_transition (NatModule.gcompfHist T f g)) t) :
∃ t', gcompf_P_simp (t ++ t') (f) (g) ∧ @behaviour _ _ (state_transition (NatModule.gcompfHist T f g)) (t ++ t') := by
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
  . have sum := @gcompf_eq_sum T f g
    simp [reachable] at sum
    have sum_ := sum s3_weights_zero _ s1_inits s1_stars_s3
    simp [gcompf_P_simp]
    exact sum_
  . simp [behaviour]
    exists s1
    constructor; exact s1_inits
    exists s3
