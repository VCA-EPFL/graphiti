import Lean

open Lean
open Leanses
open Lean Elab Meta Tactic

namespace matchGoal


/--
Tactic to specialize all the hypotheses in the context that contain a binding
of that term.
-/
syntax (name := specializeAll) "specializeAll " term : tactic

-- We use a structure storage to save the state of our bounded vars
structure Storage where
  bef : Array Expr
  aft : Array Expr

-- We use these auxiliary methods to create and set the content of our storage
def globalStorageRef : IO (IO.Ref Storage) :=
  IO.mkRef { bef := #[], aft := #[]}

def setStorage (ref : IO.Ref Storage) (vars : Array Expr) (index : Array Expr): IO Unit := do
  ref.set { bef := vars, aft := index}

@[tactic specializeAll] def specializeAllTactic : Tactic -- Syntax -> TacticM Unit
  | `(tactic| specializeAll $t:term) => withMainContext do
    let ref <- globalStorageRef
    let t ← elabTerm t none
    let termType ← inferType t
    let lctx ← getLCtx
    lctx.forM fun decl : LocalDecl => do
      if decl.isImplementationDetail then return ()
      if (← forallTelescopeReducing decl.type fun vars _ => do
        if vars.size > 0 then
          -- we identify which variable needs to be specialized and save
          -- all other bounded variables
          let mut bef : Array Expr := #[]
          let mut aft : Array Expr := #[]
          for i in [0:vars.size] do
            let varType ← inferType vars[i]!
            if (← isDefEq varType termType) then
              for j in [i+1:vars.size] do
                aft := aft.push vars[j]!
              setStorage ref bef aft
              return true
            else
              bef := bef.push vars[i]!
        return false
      )
        -- We don't want to instantiate arrow types (only dependent types).
        && decl.type.arrow?.isNone
      then
        let var <- ref.get
        -- We unbind the bvars before the var to be specialized, apply it, then
        -- bind it again with mkLambdaFvars
        let e ← forallBoundedTelescope decl.type var.bef.size fun fvars _ => do
          let y <- mkAppM' (mkAppN decl.toExpr fvars) #[t]
          mkLambdaFVars fvars y
        -- We create a new assertion in the current goal and also infer the type
        -- of `e` again.  Instead we could generate the correct type as well.
        let mvarId ← (← getMainGoal).assert decl.userName (← inferType e).headBeta e
        let (_, mvarId) ← mvarId.intro1P
        let mvarId ← mvarId.tryClear decl.fvarId
        replaceMainGoal [mvarId]
      else
        return ()
  | _ => throwUnsupportedSyntax

------------------- TESTS -----------------------

theorem sp_a : (∀ a b c : Bool, a /\ b /\ c) -> false := by
  intros
  specializeAll false
  sorry

theorem sp_b : (∀ a : Nat, ∀ b c : Bool, (a = 1) /\ b /\ c) -> false := by
  intros
  specializeAll true
  sorry

theorem sp_c : (∀ a b : Nat, ∀ c : Bool, (a = 1) /\ (b = 2) /\ c) -> false := by
  intros
  specializeAll false
  sorry
------------------- END -----------------------


/--
Tactic to match a hypothesis in the context with its pattern before applying
a given tactic to the goal.
-/

syntax (name := matchGoal) "matchGoal" sepBy1("("sepBy1(ident " : " term, ",") ")" "("term")" "("tactic")", "|") : tactic

@[tactic matchGoal]
def matchGoalTactic : Tactic
  | `(tactic| matchGoal $[($[$ids:ident : $patts:term],*) ($goal:term) ($tac:tactic)]|*) => withMainContext do
      -- we zip all our args together to have a clause tuple with hypothesis patterns, goal pattern, and tactics to try
      let clauses := (List.zip (List.zip (List.zip ids.toList patts.toList) goal.toList) tac.toList).map (λ (((ids, patts), goal), tac) => (ids, patts, goal, tac))
      -- we iterate over each clause to match its patterns and apply its tactics if applicable
      for (ids, patts, goal, tac) in clauses do
        -- we save state in case no pattern is found and an exception is thrown
        let original <- saveState
        -- we catch any terminating error for the currently inspected clause
        try{
          -- we use an hashset to store previously matched patterns
          let fk <- IO.mkRef (HashSet.empty : HashSet FVarId)

          let fvarIds <- (ids.zip patts).mapM fun (id, patt) => do
            -- we try to find our matching hypothesis without modifying the state of our goal
            let fvarId ← withoutModifyingState do
              -- we create a new metavar context depth to try different assignments and try to match them to our hypothesis
              let fvarId? ← (← getLCtx).findDeclRevM? fun localDecl => withNewMCtxDepth do
                -- we elab our term
                let hypPatt ← elabTerm patt none
                -- we check if we previously matched that hypothesis
                let fkarr <- fk.get
                if fkarr.contains localDecl.fvarId then
                  return none
                -- we try to assign its metavars with our localdecl
                if (← withAssignableSyntheticOpaque <| isDefEq hypPatt localDecl.type) then
                  return some localDecl.fvarId
                else
                  return none
              -- at the end of our iteration, we throw an error if no matching type or return the id of the fvar matched
              match fvarId? with
              | none => throwError "failed to match hyps to patt {indentExpr (<- elabTerm patt none)}"
              | some fvarId =>
                fk.modify fun f => f.insert fvarId
                return fvarId
            return (id, fvarId)

          -- we get the old username for renaming purposes
          let names <- fvarIds.mapM fun (id, fvar) => do
            -- we rename the matched pattern if needed (it is not a single metavar)
            replaceMainGoal [← (← getMainGoal).rename fvar id.getId]
            return (id, fvar, fvar.getUserName)

          -- we pattern match on the current goal to see if we can apply the tactics (similar to above)
          let patt <- withoutModifyingState do
              withNewMCtxDepth do
              let goalPatt ← elabTerm goal none
              let goalType <- (<- getMainGoal).getType
              if (← withAssignableSyntheticOpaque <| isDefEq goalPatt goalType) then
                return some (<- getMainGoal)
              return none
          match patt with
          | none => throwError "failed to match pattern to curr goal {indentExpr (<- elabTerm goal none)}"
          | some _ =>
            -- if the goal pattern matched the current goal, we try to eval the tactic
            evalTactic tac
            -- if no exception is thrown and a goal still exists we rename the variables and return
            if(<- getUnsolvedGoals).isEmpty then return
            (← getLCtx).findDeclRevM? fun localDecl => do
              let bgg? <- names.mapM fun (_, _, name) => do
                if ((<- name) == (<- localDecl.fvarId.getUserName)) then
                  for goal in (<- getUnsolvedGoals).reverse do
                    let i <- goal.rename localDecl.fvarId (<- name)
                    appendGoals [i]
                  return some localDecl.fvarId
                else
                  return none
              match bgg? with
              | _ => pure (none : Option FVarId)
          return
        }
        -- if we have a terminating error, we restore state and move to next clause
        catch _ =>
          restoreState original
      -- if no clause evaluation succeeded, we throw an error
      throwError "No pattern found or tactic failed"
      | _ => throwUnsupportedSyntax


-------- TESTS ------------

example α :
  False → α := by
  intros; matchGoal(h : False) (_) (cases h)

example α :
  False → α := by
  intros; matchGoal(h : True, v : _) (_) (cases h) | (h : False) (_) (cases h)


example :
  True := by
  intros; matchGoal (h : ?a) (True) (constructor)

example:
  True ∧ True := by
  repeat matchGoal (h : _) (?a ∧ ?b) (constructor) | (h : _) (_) (constructor)

-- not in the right order to show that it doesn't matter, no failure
example (b: Bool) (v : b) :
  True -> False ∨ b := by
  repeat matchGoal (h : _) (?a ∨ ?b) (right) | (h :_) (_ -> _) (intros) | (k : _ = true)(_)(exact k)

example (a b c d: Bool) (j: c = false)(k : a = true)(g : b = true):
  (a ∧ b) ∨ (c ∧ d) := by
  repeat matchGoal (l : _ = true, v: _ = true) (_ ∧ _) (apply And.intro v l) | (r : _) (_ ∨_) (constructor)

-- we add the middle pattern to show if tactic fails it doesn't stop exec
example a b c d :
  a ∧ b -> c ∨ d -> a ∧ b := by
  repeat matchGoal (h: _) (_ -> _) (intros) | (h: _ ∨ _) (_) (exact h) | (h: _ ∧ _) (_) (exact h)

theorem sp_a_m : (∀ a b c : Bool, a /\ b /\ c) -> false := by
  intros
  matchGoal(h : ∀ _ : Bool, _)(_)(specialize h false)
  sorry

theorem sp_b_m : (∀ a : Nat, ∀ b c : Bool, (a = 1) ∧ b /\ c) -> (z : Bool) -> True := by
  intros
  matchGoal(h : ∀ _ (_ : ?b) _, _, q : ?b)(_)(replace h := fun a c => h a q c)

  trivial

theorem sp_c_m : (∀ a b : Nat, ∀ c : Bool, (a = 1) /\ (b = 2) /\ c) -> false := by
  intros
  matchGoal (h : ∀ _ _ (_ : Bool), _, z : _) (_) (replace h := fun a b => h a b false)
  sorry

------------------- END -----------------------

theorem s : ∀ (y : True) (h : False) (z : True), False := by
  matchGoal (h : ?f) (?f) (apply h)
