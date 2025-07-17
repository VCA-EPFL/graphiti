/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.StateTransition
import Mathlib.Tactic

namespace Graphiti

inductive Method where
  | enq (n : Nat)
  | unenq (n : Nat)
  | deq (n : Nat)
  | undeq (n : Nat)
  | unlock

structure ImpState where
  lock : Bool
  queue : Queue
  deriving Inhabited, Repr

inductive imp_step : ImpState → List Method → ImpState → Prop where
  | enq : ∀ s n,
    s.lock = false →
    imp_step s [Method.enq n] { s with queue := s.queue ++ [n] }
  | unenq : ∀ s n rst,
    s.lock = false →
    s.queue = rst ++ [n] →
    imp_step s [Method.unenq n] { s with queue := rst }
  | deq : ∀ s n rst,
    s.queue = n :: rst →
    imp_step s [Method.deq n] { s with queue := rst }
  | undeq : ∀ s n,
    imp_step s [Method.undeq n] { s with queue := n :: s.queue }
  | unlock : ∀ s,
    s.lock = true →
    imp_step s [Method.unlock] { s with lock := false }
  | lock : ∀ s,
    imp_step s [] { s with lock := true }
  | unlock_natural : ∀ s,
    s.queue = [] →
    imp_step s [] { s with lock := false }

instance ImpStateTransition : StateTransition Method ImpState where
  init := default
  step := imp_step

structure SpecState where
  queue : Queue
  deriving Inhabited, Repr

inductive spec_step : SpecState → List Method → SpecState → Prop where
  | enq : ∀ s n,
    spec_step s [Method.enq n] { s with queue := s.queue ++ [n] }
  | unenq : ∀ s n rst,
    s.queue = rst ++ [n] →
    spec_step s [Method.unenq n] { s with queue := rst }
  | deq : ∀ s n rst,
    s.queue = n :: rst →
    spec_step s [Method.deq n] { s with queue := rst }
  | undeq : ∀ s n,
    spec_step s [Method.undeq n] { s with queue := n :: s.queue }
  | unlock : ∀ s,
    spec_step s [Method.unlock] s

instance SpecStateTransition : StateTransition Method SpecState where
  init := default
  step := spec_step

infix:60 " ≺ " => @indistinguishable Method

inductive Method₂ where
  | enq (n : Nat)
  | deq (n : Nat)

inductive imp_step₂ : ImpState → List Method₂ → ImpState → Prop where
  | enq : ∀ s n,
    s.lock = false →
    imp_step₂ s [Method₂.enq n] { s with queue := s.queue ++ [n] }
  | deq : ∀ s n rst,
    s.queue = n :: rst →
    imp_step₂ s [Method₂.deq n] { s with queue := rst }
  | lock : ∀ s,
    imp_step₂ s [] { s with lock := true }
  | unlock_natural : ∀ s,
    s.queue = [] →
    imp_step₂ s [] { s with lock := false }

instance ImpStateTransition₂ : StateTransition Method₂ ImpState where
  init := default
  step := imp_step₂

inductive spec_step₂ : SpecState → List Method₂ → SpecState → Prop where
  | enq : ∀ s n,
    spec_step₂ s [Method₂.enq n] { s with queue := s.queue ++ [n] }
  | deq : ∀ s n rst,
    s.queue = n :: rst →
    spec_step₂ s [Method₂.deq n] { s with queue := rst }

instance SpecStateTransition₂ : StateTransition Method₂ SpecState where
  init := default
  step := spec_step₂

infix:60 " ≺₂ " => @indistinguishable Method₂

/--
Implementation of have with holes, which uses let first to create the definition
and then assigns it using `have` to remove the body, followed by clearing the
hypothesis.
-/
syntax (name := haveByLet) "have_hole " haveDecl : tactic

macro_rules
  | `(tactic| have_hole $id:haveId $bs* : $type := $proof) =>
    `(tactic| (let h $bs* : $type := $proof; have $id:haveId := h; clear h))

theorem spec_single_signal (s1 s2 : SpecState) (e1 : List Method)
  : s1 -[ e1 ]-> s2 → ∃ (e2 : Method), e1 = [e2] := by
  intro H; have H₂ := H; cases H <;> tauto

inductive match_methods : Method → Method₂ → Prop where
  | enq : ∀ n, match_methods (Method.enq n) (Method₂.enq n)
  | deq : ∀ n, match_methods (Method.deq n) (Method₂.deq n)

theorem spec_steps (s s' : SpecState) (e : List Method) (e' : List Method₂)
  : s -[ e ]-> s' → List.Forall₂ match_methods e e' → s -[ e' ]-> s' := by
  intro HF; have Heq := spec_single_signal _ _ _ HF; rcases Heq with ⟨ m, Heq ⟩; subst e
  intro HM; cases HM; rename_i m₂ l₂ Hm HF'; cases HF'; cases Hm <;> (cases HF; constructor; try assumption)

theorem spec_star_steps (s s' : SpecState) (e : List Method) (e' : List Method₂)
  : s -[ e ]*> s' → List.Forall₂ match_methods e e' → s -[ e' ]*> s' := by
  intro H; induction H generalizing e' with
  | refl s2 =>
    intro HF; cases HF; constructor
  | step s1 s2 s3 e1 e2 Hs1 _ IH =>
    intro HF; have Hs1' := Hs1; apply spec_single_signal at Hs1; rcases Hs1 with ⟨ e1', Hs1 ⟩; subst e1
    cases HF; rename_i m ml Hm HF; dsimp at *
    apply IH at HF
    have : m :: ml = [m] ++ ml := by dsimp
    rw [this]; constructor
    apply spec_steps; assumption
    repeat' first | assumption | constructor

theorem indis_less_methods (i : ImpState) (s : SpecState) :
  i ≺ s → i ≺₂ s := by
  unfold indistinguishable; intro H
  intro e i' Histep
  have Histep' := Histep
  cases Histep with
  | enq n a =>
    have_hole H₂ : i -[[Method.enq n]]-> _ := by tauto
    apply H at H₂
    rcases H₂ with ⟨ s', Hsstep ⟩
    exists s'; apply spec_star_steps <;> tauto
  | deq n rst a =>
    have_hole H₂ : i -[[Method.deq n]]-> _ := by
      constructor; assumption
    apply H at H₂
    rcases H₂ with ⟨ s', Hsstep ⟩
    exists s'; apply spec_star_steps <;> tauto
  | lock | unlock_natural _ => tauto

/--
We define phi with a few necessary extensions.  For example, we use
quantification for the `enq` case, so that we can handle any inputs and still
commute.  In addition to that, we have indistinguishability inside of the φ.
This is because it makes it easier to prove the `enq` case, because one knows
one just has indistinguishability.
-/
inductive φ : ImpState → SpecState → Prop where
  | base :
    φ ⟨false, []⟩ ⟨[]⟩
  | enq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.enq n] i' →
    spec_step s [Method.enq n] s' →
    φ i s
  | unenq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.unenq n] i' →
    spec_step s [Method.unenq n] s' →
    φ i s
  | deq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.deq n] i' →
    spec_step s [Method.deq n] s' →
    φ i s
  | undeq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.undeq n] i' →
    spec_step s [Method.undeq n] s' →
    φ i s
  | unlock : ∀ i i' s s',
    i ≺ s →
    φ i' s' →
    imp_step i [Method.unlock] i' →
    spec_step s [Method.unlock] s' →
    φ i s
  | internal : ∀ i i' s,
    i ≺ s →
    φ i' s →
    imp_step i [] i' →
    φ i s

inductive φ₂ : ImpState → SpecState → Prop where
  | base :
    φ₂ ⟨false, []⟩ ⟨[]⟩
  | enq : ∀ i i' s s' n,
    φ₂ i' s' →
    imp_step i [Method.enq n] i' →
    spec_step s [Method.enq n] s' →
    φ₂ i s
  | unenq : ∀ i i' s s' n,
    φ₂ i' s' →
    imp_step i [Method.unenq n] i' →
    spec_step s [Method.unenq n] s' →
    φ₂ i s
  | deq : ∀ i i' s s' n,
    φ₂ i' s' →
    imp_step i [Method.deq n] i' →
    spec_step s [Method.deq n] s' →
    φ₂ i s
  | undeq : ∀ i i' s s' n,
    φ₂ i' s' →
    imp_step i [Method.undeq n] i' →
    spec_step s [Method.undeq n] s' →
    φ₂ i s
  | unlock : ∀ i i' s s',
    φ₂ i' s' →
    imp_step i [Method.unlock] i' →
    spec_step s [Method.unlock] s' →
    φ₂ i s
  | internal : ∀ i i' s,
    φ₂ i' s →
    imp_step i [] i' →
    φ₂ i s

macro "solve_indistinguishable" t:tactic : tactic =>
  `(tactic| (unfold indistinguishable; intros _ _ a; have Hindimpstep := a; cases a
             <;> (try ((repeat' first | (apply star.refl; done) | apply star.plus_one | constructor | $t:tactic) <;> done))))

theorem φ₂_equal_queues i s : φ₂ i s → i.queue = s.queue := by
  intro H; induction H with
  | base => simp
  | enq i i' s s' n Hphi Histep Hsstep iH
  | unenq i i' s s' n Hphi Histep Hsstep iH
  | deq i i' s s' n Hphi Histep Hsstep iH
  | undeq i i' s s' n Hphi Histep Hsstep iH
  | unlock i i' s s' Hphi Histep Hsstep iH =>
    cases Histep; cases Hsstep; simp [*] at *; assumption
  | internal i i' s Hphi Histep iH =>
    cases Histep <;> (simp [*] at *; assumption)

theorem φ₂_indist i s :
  φ₂ i s → i ≺ s := by
  intro Hphi; 
  have Heq := φ₂_equal_queues _ _ Hphi
  solve_indistinguishable fail
  case unenq n rst Hl Hq _Hstep =>
    constructor; apply star.plus_one; constructor
    rw [←Heq]; assumption
  case deq n rst a _Hstep =>
    constructor; apply star.plus_one; constructor
    rw [←Heq]; assumption

theorem empty_indistinguishable :
  (default : ImpState) ≺ (default : SpecState) := by
  unfold indistinguishable; intros e i' Himp
  cases Himp with
  | enq n a | undeq n | unlock => constructor; apply star.plus_one; constructor
  | deq n rst a | unenq n rst _ a => reduce at a; simp at a
  | lock | unlock_natural => constructor; apply star.refl

theorem φ_indistinguishable i s :
  φ i s → i ≺ s := by
  intros H; cases H with
  | base => apply empty_indistinguishable
  | _ => assumption

theorem invert_single_spec_step (s1 s2 : SpecState) (e : Method):
  s1 -[[e]]*> s2 → s1 -[[e]]-> s2 := by
  generalize Hthis : [e] = e'; intros Hs
  cases Hs with
  | refl => simp at Hthis
  | step s1' s2' s3' e1 e2 Hstep Hstar =>
    have Hthis' : e1 = [e] ∧ e2 = [] := by
      cases Hstep <;> (simp at *; tauto)
    cases Hthis'; subst e1; subst e2
    generalize Hother : [] = e' at Hstar
    cases Hstar with
   | step s1'' s2'' s3'' e1' e2' Hstep' Hstar' =>
      symm at Hother; rw [List.append_eq_nil] at Hother; cases Hother
      subst e1'; subst e2'; cases Hstep'
   | refl => assumption

open Lean Elab Meta Tactic

/--
Tactic to specialize all the hypotheses in the context that contain an binding
of that term in the first position.
-/
syntax (name := specializeAll) "specializeAll " term : tactic

@[tactic specializeAll] def specializeAllTactic : Tactic -- Syntax -> TacticM Unit
  | `(tactic| specializeAll $t:term) => withMainContext do
    let t ← elabTerm t none
    let termType ← inferType t
    let lctx ← getLCtx
    lctx.forM fun decl : LocalDecl => do
      -- First we check if the current hypothesis contains a binding of the same
      -- type as the input term in the first position.
      if (← forallTelescopeReducing decl.type fun vars _ => do
        if h : vars.size > 0 then
          isDefEq (← inferType vars[0]) termType
        else
          return false)
        -- We don't want to instantiate arrow types (only dependent types).
        && decl.type.arrow?.isNone
      then
        let e ← mkAppM' decl.toExpr #[t]
        -- We create a new assertion in the current goal and also infer the type
        -- of `e` again.  Instead we could generate the correct type as well.
        let mvarId ← (← getMainGoal).assert decl.userName (← inferType e).headBeta e
        let (_, mvarId) ← mvarId.intro1P
        let mvarId ← mvarId.tryClear decl.fvarId
        replaceMainGoal [mvarId]
      else
        return ()
  | _ => throwUnsupportedSyntax

def kAbstractMatches (expr t : Expr) : MetaM Bool := do
  try
    -- `==` does not work here because sometimes the term can be reduced I
    -- believe, in which case they won't 100% match.
    let abstr ← withAssignableSyntheticOpaque <| kabstract expr t
    not <$> (withAssignableSyntheticOpaque <| isDefEq abstr expr)
  -- isDefEq will error with unbound bvars, which is expected and means
  -- that the abstraction worked.
  catch _e =>
    return true

def findIndHyp : TacticM (FVarId × FVarId) := do
    -- First: Figure out which hypothesis is the top step and which is the
    -- inductive hypothesis.  This will be made with the assumption that the
    -- inductive hypothesis will contain the implementation step, implying a
    -- series of specification steps and the phi.
    let lctx ← getLCtx

    -- log m!"{repr (∃ s', s -[ e ]*> s' ∧ φ i' s')}"

    let mut ret := none

    for decl in lctx do
      -- Otherwise the theorem itself shows up in the declarations.
      if decl.isImplementationDetail then continue

      trace[debug] m!"(DECL) {decl.userName}: {decl.type}"

      -- This will match different step functions, which can then be used to
      -- find the inductive hypothesis.
      let (x, ind_hyp') ← withNewMCtxDepth do
        let (_, _, expr) ← forallMetaTelescopeReducing decl.type
        let t ← elabTermWithHoles (← `(imp_step ?a ?b ?c)) none `createInductivePhi
        let s ← elabTerm (← `(imp_step ?c ?d ?e)) none
        -- trace[debug] m!"T':: {t.fst}"
        -- trace[debug] m!"(DECL2): {expr}"
        -- trace[debug] m!"(DECL3): {repr expr}"
        trace[debug] m!"(MAGIC): {(← withAssignableSyntheticOpaque <| kabstract expr t.fst)}"
        if ← kAbstractMatches expr t.fst then
          let mut declId := false
          let mut ind_hyp : Array FVarId := #[]
          for decl' in lctx do
            if decl'.isImplementationDetail then continue

            -- Using `forallMetaTelescopeReducing` here is necessary because
            -- otherwise a new context is created that is not a `subPrefixOf`
            -- the previous context.  This means that meta variables cannot be
            -- instantiated in that context.
            let (lst, _, expr') ← forallMetaTelescopeReducing decl'.type
            match ← whnf expr' with
            | .app (.app (.const ``Exists _) _) _ =>

              trace[debug] m!"(LIST): {← sequence <| List.map (inferType ·) (lst.toList)}"
              for hyp in lst do
                trace[debug] m!"(MAGIC2): {(← withAssignableSyntheticOpaque <| kabstract (← inferType hyp) s)}"
                if ← kAbstractMatches (← inferType hyp) s then
                  declId := true
                  ind_hyp := ind_hyp.push decl'.fvarId
                trace[debug] m!"TYPE: {(← inferType hyp)} ::: {s}"
                trace[debug] m!"DECLUSERNAME: {decl'.userName}: {← inferType hyp}"
            | _ => pure ()
          return (declId, ind_hyp)
        else return (false, #[])
      if h : x ∧ ind_hyp'.size > 0 then
        ret := some (decl.fvarId, ind_hyp'[0])

    let some someret := ret
        | throwError "Could not find hypothesis"
    return someret

def findCurrentEvent : TacticM Expr := do
  let (.app (.app (.const ``Exists _) _) goalType) := (← getMainTarget).consumeMData
    | throwError "Not the right goal type"
  withNewMCtxDepth <| lambdaTelescope goalType fun _ars newGoalType => do
    let (t, ars) ← elabTermWithHoles (← `(@star SpecState Method _ ?a ?b ?c)) none `findCurrentEvent
    if ← kAbstractMatches newGoalType t then
      instantiateMVars (Expr.mvar ars[1]!)
    else throwError "Could not find event type in goal"

/--
Creates
-/
syntax (name := createInductivePhi) "create_ind_phi" : tactic

@[tactic createInductivePhi] def createInductivePhiTactic : Tactic
  | `(tactic| create_ind_phi) => withMainContext do
    let lctx ← getLCtx
    let (imp, ind) ← findIndHyp
    trace[debug] m!"Found : {(lctx.get! imp).userName} and {(lctx.get! ind).userName}"
    let e ← findCurrentEvent
    trace[debug] m!"FOUND: {e}"
    liftMetaTactic fun mvarId => do
      let ind_decl := lctx.get! ind
      let (ars, _, t) ← forallMetaTelescopeReducing ind_decl.type
      for x in ars do
        if ← isDefEq (← inferType x) (← inferType e) then
          x.mvarId!.assign e
      let e_t ← mkAppM' ind_decl.toExpr ars
      let mvarIdNew ← mvarId.assert ind_decl.userName t e_t
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      let mvarIdNew ← mvarIdNew.tryClear ind
      -- log m!"LOG: {repr ((← (sequence <| (mvarIdNew :: (ars.map (·.mvarId!)).toList.reverse).map (·.getKind))))}"
      let newMVars := (ars.map (·.mvarId!)).toList.reverse
      return mvarIdNew :: newMVars
  | _ => throwUnsupportedSyntax

theorem enough :
  ∀ i s, φ i s →
    ∀ e i', imp_step i e i' →
      ∃ s', star s e s' ∧ φ i' s' := by stop
  intro i s h;
  induction h with
  | base =>
    intro e i' Himp
    cases Himp with
    | enq n a =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ.unenq
        · solve_indistinguishable (simp [*] at *)
        · apply φ.base
        · constructor; simp; rfl
        · constructor; simp
    | unenq n rst a b => simp at b
    | deq n rst a => simp at a
    | undeq n =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ.deq
        · solve_indistinguishable (simp [*] at *)
        · apply φ.base
        · constructor; simp; rfl
        · constructor; simp
    | lock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ.unlock
        · solve_indistinguishable (simp [*] at *)
        · apply φ.base
        · constructor
        · constructor
    | unlock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.plus_one; constructor
      · apply φ.base
    | unlock_natural a =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ.base
  | enq i i_ne s s_ne n Hindist Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ.unenq
      · solve_indistinguishable fail
        · sorry
        · sorry
      · apply φ.enq <;> assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | unenq n' rst Hl Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft; subst iright
      apply φ.enq
      · solve_indistinguishable fail
        · sorry
        · sorry
      · apply φ.enq <;> assumption
      · generalize Hi : ({ lock := false, queue := rst } : ImpState) = i''; 
        have : false = i''.lock := by subst i''; rfl
        rw [this]
        have : rst = i''.queue := by subst i''; rfl
        rw [this]
        constructor; symm; assumption
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
  | _ => sorry

-- theorem l_empty (l : List Nat) : [] = l → True := by
--   generalize H : ([] : List Nat) = l' at *

theorem empty_spec (s s' : SpecState) :
  s -[ ([] : List Method) ]*> s' → s = s' := by
  intro H; generalize Hempty : ([] : List Method) = l at H
  induction H; rfl
  rename_i s1 s2 s3 e1 e2 Hs1 Hs2 He
  rw [List.nil_eq_append] at Hempty
  cases Hempty; subst e1; subst e2
  cases Hs1

theorem enough₂ :
  ∀ i s, φ₂ i s →
    ∀ e i', imp_step i e i' →
      ∃ s', star s e s' ∧ φ₂ i' s' := by
  intro i s h;
  induction h with
  | base =>
    intro e i' Himp
    cases Himp with
    | enq n a =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ₂.unenq
        · apply φ₂.base
        · constructor; simp; rfl
        · constructor; simp
    | unenq n rst a b => simp at b
    | deq n rst a => simp at a
    | undeq n =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ₂.deq
        · apply φ₂.base
        · constructor; simp; rfl
        · constructor; simp
    | lock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ₂.unlock
        · apply φ₂.base
        · constructor; simp
        · constructor
    | unlock => tauto
      -- simp; exists ⟨[]⟩; and_intros
      -- · apply star.plus_one; constructor
      -- · apply φ₂.base
    | unlock_natural a =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ₂.base
  | enq i i_ne s s_ne n Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    have Hphi_base : φ₂ i s := by
      apply φ₂.enq <;> assumption
    have Hindist := φ₂_indist _ _ Hphi_base
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ₂.unenq
      · assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | unenq n' rst Hl Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft; subst iright
      apply φ₂.enq
      · assumption
      · generalize Hi : ({ lock := false, queue := rst } : ImpState) = i''; 
        have : false = i''.lock := by subst i''; rfl
        rw [this]
        have : rst = i''.queue := by subst i''; rfl
        rw [this]
        constructor; symm; assumption
      · apply invert_single_spec_step at HspecDown; cases HspecDown; rename_i rst' a; rcases s with ⟨ s ⟩; simp at *; rw [a]; constructor
    | deq n' rst a =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
      apply φ₂.undeq
      · assumption
      · constructor
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i Ha; simp at Ha; rw [Ha]; constructor
    | undeq n' =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply φ₂.deq
      · assumption
      · constructor; simp; rfl
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i q; constructor; simp
    | unlock a =>
      cases HimpRight; rw [a] at *; tauto
    | lock =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft
      · apply φ₂.unlock
        · assumption
        · constructor; simp
        · constructor
      · assumption
    | unlock_natural Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft <;> try assumption
      apply φ₂.internal
      · assumption
      · constructor
  | deq i i_ne s s_ne n Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    have Hphi_base : φ₂ i s := by
      apply φ₂.deq <;> assumption
    have Hindist := φ₂_indist _ _ Hphi_base
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ₂.unenq
      · assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | unenq n' rst Hl Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft; subst iright
      apply φ₂.enq
      · assumption
      · generalize Hi : ({ lock := false, queue := rst } : ImpState) = i''; 
        have : false = i''.lock := by subst i''; rfl
        rw [this]
        have : rst = i''.queue := by subst i''; rfl
        rw [this]
        constructor; symm; assumption
      · apply invert_single_spec_step at HspecDown; cases HspecDown; rename_i rst' a; rcases s with ⟨ s ⟩; simp at *; rw [a]; constructor
    | deq n' rst a =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
      apply φ₂.undeq
      · assumption
      · constructor
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i Ha; simp at Ha; rw [Ha]; constructor
    | undeq n' =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply φ₂.deq
      · assumption
      · constructor; simp; rfl
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i q; constructor; simp
    | unlock a =>
      apply invert_single_spec_step at HspecDown; cases HspecDown
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft
      apply φ₂.internal
      · assumption
      · constructor
    | lock =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft
      · apply φ₂.unlock
        · assumption
        · constructor; simp
        · constructor
      · assumption
    | unlock_natural Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft <;> try assumption
      apply φ₂.internal
      · assumption
      · constructor
  | unenq i i_ne s s_ne n Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    have Hphi_base : φ₂ i s := by
      apply φ₂.unenq <;> assumption
    have Hindist := φ₂_indist _ _ Hphi_base
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ₂.unenq
      · assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | unenq n' rst Hl Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft; subst iright
      apply φ₂.enq
      · assumption
      · generalize Hi : ({ lock := false, queue := rst } : ImpState) = i''; 
        have : false = i''.lock := by subst i''; rfl
        rw [this]
        have : rst = i''.queue := by subst i''; rfl
        rw [this]
        constructor; symm; assumption
      · apply invert_single_spec_step at HspecDown; cases HspecDown; rename_i rst' a; rcases s with ⟨ s ⟩; simp at *; rw [a]; constructor
    | deq n' rst a =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
      apply φ₂.undeq
      · assumption
      · constructor
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i Ha; simp at Ha; rw [Ha]; constructor
    | undeq n' =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply φ₂.deq
      · assumption
      · constructor; simp; rfl
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i q; constructor; simp
    | unlock a =>
      apply invert_single_spec_step at HspecDown; cases HspecDown
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft
      apply φ₂.internal
      · assumption
      · constructor
    | lock =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft
      · apply φ₂.unlock
        · assumption
        · constructor; simp
        · constructor
      · assumption
    | unlock_natural Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft <;> try assumption
      apply φ₂.internal
      · assumption
      · constructor
  | undeq i i_ne s s_ne n Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    have Hphi_base : φ₂ i s := by
      apply φ₂.undeq <;> assumption
    have Hindist := φ₂_indist _ _ Hphi_base
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ₂.unenq
      · assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | unenq n' rst Hl Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft; subst iright
      apply φ₂.enq
      · assumption
      · generalize Hi : ({ lock := false, queue := rst } : ImpState) = i''; 
        have : false = i''.lock := by subst i''; rfl
        rw [this]
        have : rst = i''.queue := by subst i''; rfl
        rw [this]
        constructor; symm; assumption
      · apply invert_single_spec_step at HspecDown; cases HspecDown; rename_i rst' a; rcases s with ⟨ s ⟩; simp at *; rw [a]; constructor
    | deq n' rst a =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
      apply φ₂.undeq
      · assumption
      · constructor
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i Ha; simp at Ha; rw [Ha]; constructor
    | undeq n' =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply φ₂.deq
      · assumption
      · constructor; simp; rfl
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i q; constructor; simp
    | unlock a =>
      apply invert_single_spec_step at HspecDown; cases HspecDown
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft
      apply φ₂.internal
      · assumption
      · constructor
    | lock =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft
      · apply φ₂.unlock
        · assumption
        · constructor; simp
        · constructor
      · assumption
    | unlock_natural Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft <;> try assumption
      apply φ₂.internal
      · assumption
      · constructor
  | unlock i i_ne s s_ne Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    have Hphi_base : φ₂ i s := by
      apply φ₂.unlock <;> assumption
    have Hindist := φ₂_indist _ _ Hphi_base
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ₂.unenq
      · assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | unenq n' rst Hl Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft; subst iright
      apply φ₂.enq
      · assumption
      · generalize Hi : ({ lock := false, queue := rst } : ImpState) = i''; 
        have : false = i''.lock := by subst i''; rfl
        rw [this]
        have : rst = i''.queue := by subst i''; rfl
        rw [this]
        constructor; symm; assumption
      · apply invert_single_spec_step at HspecDown; cases HspecDown; rename_i rst' a; rcases s with ⟨ s ⟩; simp at *; rw [a]; constructor
    | deq n' rst a =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
      apply φ₂.undeq
      · assumption
      · constructor
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i Ha; simp at Ha; rw [Ha]; constructor
    | undeq n' =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply φ₂.deq
      · assumption
      · constructor; simp; rfl
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i q; constructor; simp
    | unlock a =>
      apply invert_single_spec_step at HspecDown; cases HspecDown
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft
      apply φ₂.internal
      · assumption
      · constructor
    | lock =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft
      · apply φ₂.unlock
        · assumption
        · constructor; simp
        · constructor
      · assumption
    | unlock_natural Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft <;> try assumption
      apply φ₂.internal
      · assumption
      · constructor
  | internal i i_ne s Hphi HimpRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    have Hphi_base : φ₂ i s := by
      apply φ₂.internal <;> assumption
    have Hindist := φ₂_indist _ _ Hphi_base
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ₂.unenq
      · assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | unenq n' rst Hl Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft; subst iright
      apply φ₂.enq
      · assumption
      · generalize Hi : ({ lock := false, queue := rst } : ImpState) = i''; 
        have : false = i''.lock := by subst i''; rfl
        rw [this]
        have : rst = i''.queue := by subst i''; rfl
        rw [this]
        constructor; symm; assumption
      · apply invert_single_spec_step at HspecDown; cases HspecDown; rename_i rst' a; rcases s with ⟨ s ⟩; simp at *; rw [a]; constructor
    | deq n' rst a =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
      apply φ₂.undeq
      · assumption
      · constructor
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i Ha; simp at Ha; rw [Ha]; constructor
    | undeq n' =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply φ₂.deq
      · assumption
      · constructor; simp; rfl
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i q; constructor; simp
    | unlock a =>
      apply invert_single_spec_step at HspecDown; cases HspecDown
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft
      apply φ₂.internal
      · assumption
      · constructor
    | lock =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft
      · apply φ₂.unlock
        · assumption
        · constructor; simp
        · constructor
      · assumption
    | unlock_natural Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft <;> try assumption
      apply φ₂.internal
      · assumption
      · constructor

theorem φ₂_empty : φ₂ default default := by constructor

theorem enough₂_star (i i': ImpState) (s : SpecState) (e : List Method):
  φ₂ i s → star i e i' →
  ∃ s', star s e s' ∧ φ₂ i' s' := by
  intro Hphi Hstar; induction Hstar generalizing s with
  | refl => exists s; and_intros; constructor; assumption
  | step s1 s2 s3 e1 e2 Hs1 Hs2 iH =>
    apply enough₂ at Hs1 <;> try assumption
    rcases Hs1 with ⟨ a, b, c ⟩
    apply iH at c
    rcases c with ⟨ c, d, e ⟩
    exists c; and_intros; apply star.trans_star <;> assumption
    assumption

-- theorem refinement (i : ImpState) (e : List Method₂) :
--   default -[ e ]*> i →
--   ∃ s : SpecState, default -[ e ]*> s ∧ i ≺₂ s := by
--   intro H
--   have H' := enough₂_star _ _ _ _ φ₂_empty H

end Graphiti
