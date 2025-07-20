/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Lean
import Qq

open Lean Meta Elab Tactic

elab "assert " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assertExt n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.introNP 2
      return [mvarIdNew]

-- TODO
-- elab "forget " h:ident : tactic => withMainContext do
--   let ctx ← Lean.MonadLCtx.getLCtx
--   -- let tmp ← ctx.get! h.getId
--   liftMetaTactic fun mvarId => do
--     mvarId.assertExt
--     mvarId.define
--     return mvarId
