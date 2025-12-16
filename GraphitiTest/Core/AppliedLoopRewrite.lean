/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.RewriterLemmas
import Graphiti.Core.Rewrites.LoopImplementationProof

open Batteries (AssocList)

namespace Graphiti

set_option maxHeartbeats 0

noncomputable def LoopRewrite_Environment
    {b : Bool}
    {ε_global : FinEnv String (String × Nat)}
    {g g' : ExprHigh String (String × Nat)}
    {e_g : ExprLow String (String × Nat)}
    {st _st' : RewriteState}
    {elems : List String}
    {types : Vector Nat LoopRewrite.rewrite.params}
    (h_wf : ε_global.toEnv.well_formed)
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
  h_lhs_wt := run'_implies_wt_lhs h2 h3 h4 h5 h6 (by rfl) LoopRewrite.lhsLower_locally_wf
  h_lhs_wf := run'_implies_wf_lhs h2 h3 h4 h5 h6 (by rfl) LoopRewrite.lhsLower_locally_wf

/--
This is the top-level theorem that applies the loop rewrite to a graph and concludes that this new graph refines the
original graph.

It assumes a few well-formedness criteria on the environment, as this rewrite holds for any environment.

The assumptions are documented below.

- h_wf: states that the environment is well formed, and for each module in the graph it assigns the correct semantics to
  it.
- h1: states that the fresh type used by the rewrite to generate new types is greater than any existing type in the
  environment.
- h2: states that the rewrite pattern matched a subgraph.  If it did not match a subgraph, then the rewrite would not
  be applicable.
- h3: states that the graph can be lowered to an inductive version of the graph.  If this were not possible, the
  rewrite would again not apply.
- h4: states that the graph is well formed with respect to the environment, meaning each port mapping for each module
  instantiation in the graph has the right number of ports, and no duplicate port definitions.
- h5: states that the graph is well typed with respect to the environment, meaning if two ports are connected to each
  other, they must have the same type.
- h6: states that applying the rewrite returned a new graph `g'`.

Finally, the conclusion of the theorem states that this new rewritten graph `g'` refines (⊑) `g`.  Given the environment
`ε_global`, to correctly interpret the graph `g'`, we have to add the loop rewrite environment
`LoopRewrite.verified_rewrite.ε_ext` to it.
-/
theorem run'_refines_applied {b} {ε_global : FinEnv String (String × Nat)}
    {g g' : ExprHigh String (String × Nat)}
    {e_g : ExprLow String (String × Nat)}
    {st _st'}
    {elems types}
    (h_wf : ε_global.toEnv.well_formed)
    (h1 : ε_global.max_typeD <= st.fresh_type)
    (h2 : LoopRewrite.rewrite.pattern g = .ok (elems, types))
    (h3 : g.lower = some e_g)
    (h4 : e_g.well_formed ε_global.toEnv)
    (h5 : e_g.well_typed ε_global.toEnv)
    (h6 : Rewrite.run' g LoopRewrite.rewrite b st = .ok g' _st') :
    [Ge| g', (ε_global ++ ((@LoopRewrite.verified_rewrite (LoopRewrite_Environment h_wf h1 h2 h3 h4 h5 h6)).ε_ext)).toEnv ] ⊑ [Ge| g, ε_global.toEnv ] :=
  run'_refines h2 h3 h4 h5 h6

#print axioms run'_refines_applied

end Graphiti
