/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import LeanSearchClient.Syntax
public import Mathlib.Tactic.DefEqTransformations
public import Mathlib.Tactic.GeneralizeProofs
public import Mathlib.Tactic.Recall
public import Mathlib.Tactic.StacksAttribute

@[expose] public meta section

open Lean Expr Meta Elab Tactic

partial def reallyReduce (e : Expr) (explicitOnly skipTypes skipProofs skipArgs useElabWhnf := true) : MetaM Expr :=
  let rec visit (e : Expr) : MonadCacheT Expr Expr MetaM Expr :=
    checkCache e fun _ => Core.withIncRecDepth do
      if (← (pure skipTypes <&&> isType e)) then
        return e
      else if (← (pure skipProofs <&&> isProof e)) then
        return e
      else
        let e ← if useElabWhnf then
                   whnf e
                 else ofExceptKernelException <| Kernel.whnf (← getEnv) (← getLCtx) e
        match e with
        | Expr.app .. =>
          let f     ← visit e.getAppFn
          let nargs := e.getAppNumArgs
          let finfo ← getFunInfoNArgs f nargs
          let mut args  := e.getAppArgs
          for i in [:args.size] do
            if i < finfo.paramInfo.size then
              let info := finfo.paramInfo[i]!
              if !explicitOnly || info.isExplicit then
                args ← args.modifyM i visit
            else
              args ← args.modifyM i visit
          if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isRawNatLit then
            return mkRawNatLit (args[0]!.rawNatLit?.get! + 1)
          else
            return mkAppN f args
        | Expr.lam ..        => lambdaTelescope e fun xs b => do
          if skipArgs then mkLambdaFVars xs (← visit b)
          else
            let ctx ← getLCtx
            let ctx' ← xs.foldlM (fun ctx' e => do
              let e' ← visit (ctx'.getFVar! e).type
              return ctx'.modifyLocalDecl e.fvarId! fun l => l.setType e') ctx
            withLCtx ctx' #[] do mkLambdaFVars xs (← visit b)
        | Expr.forallE ..    => forallTelescope e fun xs b => do
          if skipArgs then mkForallFVars xs (← visit b)
          else
            let ctx ← getLCtx
            let ctx' ← xs.foldlM (fun ctx' e => do
              let e' ← visit (ctx'.getFVar! e).type
              return ctx'.modifyLocalDecl e.fvarId! fun l => l.setType e') ctx
            withLCtx ctx' #[] do mkForallFVars xs (← visit b)
        | Expr.proj n i s .. => return mkProj n i (← visit s)
        | _                  => return e
  visit e |>.run

def reallyReduceAll (e : Expr) : MetaM Expr :=
  reallyReduce e false false false

syntax (name := reallyReduceCmd) "#reallyReduce " term : command

open Elab.Command in
@[command_elab reallyReduceCmd] def elabReallyReduce : CommandElab
  | `(#reallyReduce%$tk $term) => go tk term
  | _ => throwUnsupportedSyntax
where
  go (tk : Syntax) (term : Syntax) : CommandElabM Unit :=
    withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      -- TODO: add options or notation for setting the following parameters
      withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
        let e ← withTransparency (mode := TransparencyMode.all) <| reallyReduce e false false true false true
        logInfoAt tk e

-- #reduce (proofs := true) (types := true) 1 + 1 = 2 → True
-- #reallyReduce 1 + 1 = 2 → True

/--
This is `Lean.MVarId.changeLocalDecl` but makes sure to preserve local variable order.
-/
def _root_.Lean.MVarId.changeLocalDecl'' (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
    (checkDefEq := true) : MetaM MVarId := do
  mvarId.checkNotAssigned `changeLocalDecl
  let lctx := (← mvarId.getDecl).lctx
  let some decl := lctx.find? fvarId | throwTacticEx `changeLocalDecl mvarId m!"\
    local variable {Expr.fvar fvarId} is not present in local context{mvarId}"
  let toRevert := lctx.foldl (init := #[]) fun arr decl' =>
    if decl.index ≤ decl'.index then arr.push decl'.fvarId else arr
  let (_, mvarId) ← mvarId.withReverted toRevert fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map .some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId

/-- For the main goal, use `m` to transform the types of locations specified by `loc?`.
If `loc?` is none, then transforms the type of target. `m` is provided with an expression
with instantiated metavariables as well as, if the location is a local hypothesis, the fvar.

`m` *must* transform expressions to defeq expressions.
If `checkDefEq = true` (the default) then `runDefEqTactic` will throw an error
if the resulting expression is not definitionally equal to the original expression. -/
def runDefEqTactic (m : Option FVarId → Expr → MetaM Expr)
    (loc? : Option (TSyntax ``Parser.Tactic.location))
    (tacticName : String)
    (checkDefEq : Bool := true) :
    TacticM Unit := withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
    (atLocal := fun h => liftMetaTactic1 fun mvarId => do
      let ty ← h.getType
      let ty' ← m h (← instantiateMVars ty)
      if Expr.equal ty ty' then
        return mvarId
      else
        mvarId.changeLocalDecl' (checkDefEq := checkDefEq) h ty')
    (atTarget := liftMetaTactic1 fun mvarId => do
      let ty ← instantiateMVars (← mvarId.getType)
      mvarId.change (checkDefEq := checkDefEq) (← m none ty))
    (failed := fun _ => throwError "{tacticName} failed")

elab "rreduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ e => withTransparency (mode := TransparencyMode.all) <| reallyReduce e (skipTypes := false) (skipProofs := false) (skipArgs := false)) loc? "rreduce"

elab "rreduce_not_all" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ e => reallyReduce e (skipTypes := false) (skipProofs := false) (skipArgs := false)) loc? "rreduce"

elab "ker_rreduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ e => withTransparency (mode := TransparencyMode.all) <| reallyReduce e (skipTypes := false) (skipProofs := false) (skipArgs := false) (useElabWhnf := false)) loc? "ker_rreduce"

elab "ker_rreduce_not_all" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ e => reallyReduce e (skipTypes := false) (skipProofs := false) (skipArgs := false) (useElabWhnf := false)) loc? "ker_rreduce"
