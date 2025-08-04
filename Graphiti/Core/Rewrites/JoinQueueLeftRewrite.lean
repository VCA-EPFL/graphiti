/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.JoinQueueLeftRewrite

open StringModule

variable (T T' : Type)
variable (S S' : String)

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "queue".isPrefixOf typ do return none

       let (.some join) := followOutput g inst "out1" | return none
       unless "join".isPrefixOf join.typ ∧ join.inputPort = "in1" do return none

       let (.some t1) := join.typ.splitOn |>.get? 1 | return none
       let (.some t2) := join.typ.splitOn |>.get? 2 | return none

       return some ([inst, join.inst], [t1, t2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    q [typeImp = $(⟨_, queue T⟩), type = $(s!"queue {S}")];
    join [typeImp = $(⟨_, join T T'⟩), type = $(s!"join {S} {S'}")];

    i_1 -> q [to = "in1"];
    i_2 -> join [to = "in2"];
    join -> o_out [from="out1"];

    q -> join [from="out1", to="in1"];
  ]

def lhs_extract := (lhs Unit Unit S S').fst.extract ["q", "join"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S S').snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S S').fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join [typeImp = $(⟨_, join T T'⟩), type = $(s!"join {S} {S'}")];

    i_1 -> join [to = "in1"];
    i_2 -> join [to = "in2"];
    join -> o_out [from="out1"];
  ]

def rhsLower := (rhs Unit Unit S S').fst.lower.get rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S, S'] => .some ⟨lhsLower S S', rhsLower S S'⟩ | _ => failure
    name := "join-queue-left"
  }

end Graphiti.JoinQueueLeftRewrite
