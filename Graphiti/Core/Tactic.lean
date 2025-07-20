/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Qq

import Batteries

namespace Graphiti

open Batteries (AssocList)

open Lean Meta Elab Tactic

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

-- elab "precompute " t:term : tactic => Tactic.withMainContext do
--   let expr ← Term.elabTerm t none
--   Term.synthesizeSyntheticMVarsUsingDefault
--   let expr ← Lean.instantiateMVars expr
--   let expr ←
--     -- withTransparency .all <|
--       reallyReduce (skipArgs := false) (skipTypes := false) expr
--   (← Tactic.getMainGoal).assign expr

/--
Opaque definition used to lift any type into a `Prop`, so that it can be used as
the goal in `TacticM` mode.
-/
opaque Opaque {A : Sort _} (_ : A) : Prop := False

open Qq in
/--
Run a tactic on an expression which must be a `Prop`.  The expression is set to
be the current goal, then the tactic is executed.  The modified goal is then
returned as the new expression.
-/
def evalTacticOnExprNoWrap (tac : Syntax) (e : Q(Prop)) : TacticM Q(Prop) := do
  let s ← saveState
  let l ← mkFreshExprMVar e
  setGoals [l.mvarId!]
  evalTactic tac
  let new_e ← getMainTarget
  restoreState s
  return new_e

open Qq in
/--
Run a tactic on an expression of any type.  This wraps the expression using
`Opaque`, which transforms it into a `Prop` so that it can be set to the current
goal.
-/
def evalTacticOnExpr (tac : Syntax) (e : Expr) : TacticM Expr := do
  let e' ← mkAppOptM ``Opaque #[(← inferType e), e]
  match ← evalTacticOnExprNoWrap tac e' with
  | ~q(Opaque $e) => return e
  | _ => throwError "Not in correct form"

elab "precomputeTac " t:term " by " tac:tacticSeq : tactic => Tactic.withMainContext do
  let expr ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsUsingDefault
  let expr ← Lean.instantiateMVars expr
  let exprType ← inferType expr
  let opaqueExpr ← mkAppOptM ``Opaque #[exprType, expr]
  let m ← mkFreshExprMVar opaqueExpr
  let (l :: s) ← evalTacticAt tac m.mvarId!
    | logError "No mvar returned"
  let r := (← l.getDecl).type.getArg!' 1
  (← getMainGoal).assign r

def generateMVarEq (expr : Expr) : TermElabM (MVarId × Expr) := do
  let exprType ← inferType expr
  let lhs ← Lean.Meta.mkFreshExprMVar (userName := `reduced) (kind := .natural) exprType
  return (lhs.mvarId!, ← mkEq lhs expr)

elab "precomputeTacEq " t:term " by " tac:tacticSeq : tactic => Tactic.withMainContext do
  let expr ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsUsingDefault
  let expr ← Lean.instantiateMVars expr
  let (m', eq) ← generateMVarEq expr
  let target ← getMainTarget
  unless ← isDefEq target eq do logWarning m!"Goal not an equality {target}"
  evalTactic tac
  -- evalTactic (← `(tactic| rfl))

elab "rfl_assign" : tactic => do Tactic.withMainContext <| withAssignableSyntheticOpaque <| evalTactic (← `(tactic| rfl))

def r := by
  precomputeTacEq 3 by
    rewrite [show Eq.{1} 3 (2 + 1) by trivial]
    rfl

  -- let m ← mkFreshExprMVar opaqueExpr
  -- let [l] ← evalTacticAt tac m.mvarId!
  --   | throwError "No mvar returned or goals outstanding"
  -- return (← l.getDecl).type

theorem rw_opaque {f : Type _ → Type _} {s s' : Σ T, f T} (heq : s = s') : @Opaque (f s.fst) s.snd ↔ @Opaque (f s'.fst) s'.snd := by
  subst s; rfl

/--
Creates a have which allows metavar holes in it.
-/
syntax (name := haveByLet) "have_hole " letConfig letDecl : tactic
macro_rules
  | `(tactic| have_hole $id:ident $bs* : $type := $proof) =>
    `(tactic| (let h $bs* : $type := $proof; have $id:ident := h; clear h))

theorem ite_destruct {motive : Prop} (a : Bool) :
  (a = true → motive) →
  (a = false → motive) →
  motive := by cases a <;> solve_by_elim

/--
Given an (optional) hypothesis name `h`, an AssocList `ct`, an identifier which is used to index into the AssocList `i`
and a proof that if `i` is not contained in `ct` one has a contradiction, we can introduce the hypothesis that `i` is
contained in `ct` into the context.

This is explicitly written in a verbose `elab` style to show this off, there is probably a shorter `macro`
implementation.  You could probably also implement this as a theorem itself.
-/
elab "case_transition " h:ident " : " ct:term ", " i:term ", " ht:term : tactic => Tactic.withMainContext do
  let containsExpr ← elabTerm (← `(Batteries.AssocList.contains $i $ct)) (.some (.const ``Bool []))
  let htExpr ← elabTerm ht (← elabTerm (← `(¬Batteries.AssocList.contains $i $ct → False)) .none)
  liftMetaTactic fun mvar => do
    let mvarType ← inferType (mkMVar mvar)
    let e ← mkAppOptM ``ite_destruct #[mvarType, containsExpr]
    let [m1, m2] ← mvar.apply e
      | throwError "unexpected: too many mvars in application"
    let (hcontains', m1) ← m1.intro h.getId
    -- Prove m2
    let (hcontains, m2) ← m2.intro1
    let [m2] ← m2.apply (mkConst ``False.elim [← mkFreshLevelMVar])
      | throwError "too many mvars in False.elim application"
    m2.assign (mkApp htExpr (.fvar hcontains))
    return [m1]

macro "case_transition " ct:term ", " i:term ", " ht:term : tactic =>
  `(tactic| case_transition hcase_trans : $ct:term, $i:term, $ht:term)

-- example : ∀ (a : Batteries.AssocList Nat Nat) (n : Nat) (p : a.contains n = false → False), True := by
--   intro a n p
--   case_transition H : a, n, ‹_›
--   simp at H
--   sorry

-- TODO: Currently needs the lhs of the refinement to be passed as parameter `t`, however, it could be deduced from the
-- goal.

-- TODO: Currently it bypasses hygiene using `mkIdent`, reivaluate if it should stay like that.  As it is a top-level
-- tactic, this may be fine.

-- TODO: Currently only modules with one input and one output are handled.  It should not be difficult to extend, I just
-- need an example to test on.  Essentially, this will come down to repeatidly casing on `a ∨ b ∨ c ∨ ... ∨ d` and
-- naming each case appropriately (ideally after the `ident`).

-- TODO: Currently, nothing is done for the internal rules.  Here a fin-cases would be appropriate.

-- TODO: Currently `v` is not simplified, this may also be nice to try.
macro "prove_refines_φ " t:term : tactic =>
  `(tactic|
    (intro $(mkIdent `i) $(mkIdent `s) $(mkIdent `H); constructor)
      <;> [intro $(mkIdent `ident) $(mkIdent `mid_i) $(mkIdent `v) $(mkIdent `Hrule);
           intro $(mkIdent `ident) $(mkIdent `mid_i) $(mkIdent `v) $(mkIdent `Hrule); skip]
      <;> [case_transition Hcontains : $(mkIdent `Module.inputs) $t, $(mkIdent `ident),
             (fun x => $(mkIdent `PortMap.getIO_not_contained_false') x $(mkIdent `Hrule));
           case_transition Hcontains : $(mkIdent `Module.outputs) $t, $(mkIdent `ident),
             (fun x => $(mkIdent `PortMap.getIO_not_contained_false') x $(mkIdent `Hrule));
           skip]
      <;> [simp at Hcontains; simp at Hcontains; skip]
      <;> [subst $(mkIdent `ident); subst $(mkIdent `ident); skip]
      <;> [rw [$(mkIdent `PortMap.rw_rule_execution):ident] at $(mkIdent `Hrule):ident;
           rw [$(mkIdent `PortMap.rw_rule_execution):ident] at $(mkIdent `Hrule):ident; skip]
      <;> [simp -failIfUnchanged at $(mkIdent `Hrule):ident; simp -failIfUnchanged at $(mkIdent `Hrule):ident; skip]
   )

end Graphiti
