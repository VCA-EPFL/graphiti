/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.RewriterLemmas
import Graphiti.Core.Rewrites.LoopRewriteCorrect

open Batteries (AssocList)

namespace Graphiti

noncomputable def LoopRewrite_Environment
    {b : Bool}
    {ε_global : FinEnv String (String × Nat)}
    {g g' : ExprHigh String (String × Nat)}
    {e_g : ExprLow String (String × Nat)}
    {st _st' : RewriteState}
    {elems : List String}
    {types : Vector Nat LoopRewrite.rewrite.params}
    (h_wf : ∀ (s : String), ε_global.toEnv.well_formed s)
    (h1 : ε_global.max_typeD <= st.fresh_type)
    (h2 : LoopRewrite.rewrite.pattern g = Except.ok (elems, types))
    (h3 : g.lower = some e_g)
    (h4 : ExprLow.well_formed ε_global.toEnv e_g = true)
    (h5 : ExprLow.well_typed ε_global.toEnv e_g)
    (h6 : Rewrite.run' g LoopRewrite.rewrite b st = EStateM.Result.ok g' _st'):
    Environment LoopRewrite.lhsLower where
  ε := ε_global
  types := types
  max_type := st.fresh_type
  h_wf := ⟨h_wf, h1⟩
  h_wt :=
    run'_implies_wt_lhs h2 h3 h4 h5 h6 (by rfl) (by apply LoopRewrite.lhsLower_locally_wf)

theorem run'_refines_applied {b} {ε_global : FinEnv String (String × Nat)}
    {g g' : ExprHigh String (String × Nat)}
    {e_g : ExprLow String (String × Nat)}
    {st _st'}
    {elems types}
    (h_wf : ∀ s, Env.well_formed ε_global.toEnv s)
    (h1 : ε_global.max_typeD <= st.fresh_type)
    (h2 : LoopRewrite.rewrite.pattern g = .ok (elems, types))
    (h3 : g.lower = some e_g)
    (h4 : e_g.well_formed ε_global.toEnv)
    (h5 : e_g.well_typed ε_global.toEnv)
    (h6 : Rewrite.run' g LoopRewrite.rewrite b st = .ok g' _st') :
    [Ge| g', (ε_global ++ ((@LoopRewrite.verified_rewrite (LoopRewrite_Environment h_wf h1 h2 h3 h4 h5 h6)).ε_ext)).toEnv ] ⊑ [Ge| g, ε_global.toEnv ] :=
  run'_refines h2 h3 h4 h5 h6

#print axioms run'_refines_applied
