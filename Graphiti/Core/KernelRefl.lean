/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean

public meta section

namespace Graphiti

open Lean Meta

private def useKernel (lhs rhs : Expr) : MetaM Bool := do
  if lhs.hasMVar || rhs.hasMVar then
    return false
  else
    return (← getTransparency) matches TransparencyMode.default | TransparencyMode.all

/--
Close given goal using `Eq.refl`, using Kernel isDefEq even with free variables.
-/
def _root_.Lean.MVarId.ker_refl (mvarId : MVarId) : MetaM Unit := do
  mvarId.withContext do
    mvarId.checkNotAssigned `refl
    let targetType ← mvarId.getType'
    unless targetType.isAppOfArity ``Eq 3 do
      throwTacticEx `rfl mvarId m!"equality expected{indentExpr targetType}"
    let lhs ← instantiateMVars targetType.appFn!.appArg!
    let rhs ← instantiateMVars targetType.appArg!
    let lctx ← getLCtx
    let quantifiedTargetType ← mkForallFVars (usedOnly := true) lctx.getFVars targetType
    let instQuantifiedTargetType ← instantiateMVars quantifiedTargetType
    let newContext ← withLCtx {} {} <| forallTelescope instQuantifiedTargetType λ _ _ => getLCtx
    let success ← if (← useKernel lhs rhs) && !instQuantifiedTargetType.hasMVar then
      ofExceptKernelException (Kernel.isDefEq (← getEnv) newContext lhs rhs)
    else
      isDefEq lhs rhs
    unless success do
      throwTacticEx `rfl mvarId m!"equality lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
    let us := targetType.getAppFn.constLevels!
    let α := targetType.appFn!.appFn!.appArg!
    mvarId.assign (mkApp2 (mkConst ``Eq.refl  us) α lhs)

elab "ker_refl" : tactic =>
  Elab.Tactic.liftMetaTactic fun mvarId => do mvarId.ker_refl; pure []

end Graphiti
