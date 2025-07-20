/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

open Batteries (AssocList)

namespace Graphiti.PureJoinLeft

open StringModule

variable (T₁ T₂ T₃ : Type)
variable (f : T₁ → T₂)
variable (S₁ S₂ S₃ : String)

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure".isPrefixOf typ do return none

       let (.some join) := followOutput g inst "out1" | return none
       unless "join".isPrefixOf join.typ ∧ join.inputPort = "in1" do return none

       let (.some t1) := typ.splitOn |>.get? 1 | return none
       let (.some t2) := typ.splitOn |>.get? 2 | return none
       let (.some t3) := join.typ.splitOn |>.get? 2 | return none

       return some ([inst, join.inst], [t1, t2, t3])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def nameMap (g : ExprHigh String) : RewriteResult (AssocList String (Option String)) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure".isPrefixOf typ do return none

       let (.some join) := followOutput g inst "out1" | return none
       unless "join".isPrefixOf join.typ ∧ join.inputPort = "in1" do return none

       let (.some t1) := typ.splitOn |>.get? 1 | return none
       let (.some t2) := typ.splitOn |>.get? 2 | return none
       let (.some t3) := join.typ.splitOn |>.get? 2 | return none

       return .some [(join.inst, (.some "join")), (inst, (.some "pure"))].toAssocList
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    o_out [type = "io"];

    pure [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure {S₁} {S₂}")];
    join [typeImp = $(⟨_, join T₂ T₃⟩), type = $(s!"join {S₂} {S₃}")];

    i_0 -> pure [to="in1"];
    i_1 -> join [to="in2"];

    pure -> join [from="out1", to="in1"];

    join -> o_out [from="out1"];
  ]

def lhs_extract := (lhs Unit Unit Unit (λ _ => default) S₁ S₂ S₃).fst.extract ["pure", "join"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁ S₂ S₃).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁ S₂ S₃).fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    o_out [type = "io"];

    join [typeImp = $(⟨_, join T₁ T₃⟩), type = $(s!"join {S₁} {S₃}")];
    pure [typeImp = $(⟨_, StringModule.pure λ (x : T₁ × T₃) => (f x.1, x.2)⟩), type = $(s!"pure ({S₁}×{S₃}) ({S₂}×{S₃})")];

    i_0 -> join [to="in1"];
    i_1 -> join [to="in2"];

    join -> pure [from="out1", to="in1"];

    pure -> o_out [from="out1"];
  ]

def rhs_extract := (rhs Unit Unit Unit (λ _ => default) S₁ S₂ S₃).fst.extract ["pure", "join"] |>.get rfl

def rhsLower := (rhs_extract S₁ S₂ S₃).fst.lower.get rfl

def findRhs mod := (rhs_extract "" "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂, S₃] => .some ⟨lhsLower S₁ S₂ S₃, rhsLower S₁ S₂ S₃⟩ | _ => failure,
    name := "pure-join-left",
    transformedNodes := [findRhs "pure" |>.get rfl, findRhs "join" |>.get rfl]
  }

end Graphiti.PureJoinLeft
