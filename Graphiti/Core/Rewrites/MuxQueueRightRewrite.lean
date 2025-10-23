/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.MuxQueueRightRewrite

open StringModule

variable (T : Type)
variable (S : String)

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "queue".isPrefixOf typ do return none

       let (.some mux) := followOutput g inst "out1" | return none
       unless "mux".isPrefixOf mux.typ ∧ mux.inputPort = "in3" do return none

       let (.some t1) := typ.splitOn[1]? | return none

       return some ([inst, mux.inst], [t1])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_1 [type = "io"];
    i_2 [type = "io"];
    i_3 [type = "io"];
    o_out [type = "io"];

    q [typeImp = $(⟨_, queue T⟩), type = $(s!"queue {S}")];
    mux [typeImp = $(⟨_, mux T⟩), type = $(s!"mux {S}")];

    i_2 -> mux [to="in2"];
    i_1 -> mux [to="in1"];
    i_3 -> q [to = "in1"];
    mux -> o_out [from="out1"];

    q -> mux [from="out1", to="in3"];
  ]

def lhs_extract := (lhs Unit S).fst.extract ["q", "mux"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S).fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_1 [type = "io"];
    i_2 [type = "io"];
    i_3 [type = "io"];
    o_out [type = "io"];

    mux [typeImp = $(⟨_, mux T⟩), type = $(s!"mux {S}")];

    i_2 -> mux [to="in2"];
    i_1 -> mux [to="in1"];
    i_3 -> mux [to = "in3"];
    mux -> o_out [from="out1"];
  ]

def rhsLower := (rhs Unit S).fst.lower.get rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S] => .some ⟨lhsLower S, rhsLower S⟩ | _ => failure
    name := "mux-queue-right"
  }

end Graphiti.MuxQueueRightRewrite
