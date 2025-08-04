/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.ForkJoin

open StringModule

variable (T₁ T₂ : Type)
variable (S₁ S₂ : String)

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "join".isPrefixOf typ do return none

       let (.some p) := followOutput g inst "out1" | return none
       unless "fork".isPrefixOf p.typ do return none

       let (.some jt1) := typ.splitOn |>.get? 1 | return none
       let (.some jt2) := typ.splitOn |>.get? 2 | return none

       -- -- TODO: prevent forks being moved away from branch/mux
       -- let (.some mux) := followOutput g p.inst "out1" | return none
       -- unless "mux".isPrefixOf mux.typ || "branch".isPrefixOf mux.typ do return none

       return some ([inst, p.inst], [jt1, jt2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    join [typeImp = $(⟨_, join T₁ T₂⟩), type = $(s!"join {S₁} {S₂}")];
    fork [typeImp = $(⟨_, fork (T₁ × T₂) 2⟩), type = $(s!"fork ({S₁}×{S₂}) 2")];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];
    join -> fork [from="out1",to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
  ]

def lhs_extract := (lhs Unit Unit S₁ S₂).fst.extract ["join", "fork"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁ S₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁ S₂).fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    fork1 [typeImp = $(⟨_, fork T₁ 2⟩), type = $(s!"fork {S₁} 2")];
    fork2 [typeImp = $(⟨_, fork T₂ 2⟩), type = $(s!"fork {S₂} 2")];
    join1 [typeImp = $(⟨_, join T₁ T₂⟩), type = $(s!"join {S₁} {S₂}")];
    join2 [typeImp = $(⟨_, join T₁ T₂⟩), type = $(s!"join {S₁} {S₂}")];

    i1 -> fork1 [to="in1"];
    i2 -> fork2 [to="in1"];
    fork1 -> join1 [from="out1",to="in1"];
    fork2 -> join1 [from="out1",to="in2"];
    fork1 -> join2 [from="out2",to="in1"];
    fork2 -> join2 [from="out2",to="in2"];
    join1 -> o1 [from="out1"];
    join2 -> o2 [from="out1"];
  ]

def rhs_extract := (rhs Unit Unit S₁ S₂).fst.extract ["fork1", "fork2", "join1", "join2"] |>.get rfl

def rhsLower := (rhs_extract S₁ S₂).fst.lower.get rfl

def findRhs mod := (rhs_extract "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂] => .some ⟨lhsLower S₁ S₂, rhsLower S₁ S₂⟩ | _ => failure,
    name := "fork-join"
    transformedNodes := [.none, .none]
    addedNodes := [ findRhs "fork1" |>.get rfl, findRhs "fork2" |>.get rfl
                  , findRhs "join1" |>.get rfl, findRhs "join2" |>.get rfl]
  }

end Graphiti.ForkJoin
