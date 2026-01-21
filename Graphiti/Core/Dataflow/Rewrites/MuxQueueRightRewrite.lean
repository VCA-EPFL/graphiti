/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.MuxQueueRightRewrite

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "queue" == typ.1 do return none

       let (.some mux) := followOutput g inst "out1" | return none
       unless "mux" == mux.typ.1 ∧ mux.inputPort = "in3" do return none

       return some ([inst, mux.inst], #v[typ.2, mux.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i_1 [type = "io"];
    i_2 [type = "io"];
    i_3 [type = "io"];
    o_out [type = "io"];

    q [type = "queue", arg = $(T[0])];
    mux [type = "mux", arg = $(T[1])];

    i_2 -> mux [to="in2"];
    i_1 -> mux [to="in1"];
    i_3 -> q [to = "in1"];
    mux -> o_out [from="out1"];

    q -> mux [from="out1", to="in3"];
  ]

def lhs_extract := (lhs T).extract ["q", "mux"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_1 [type = "io"];
    i_2 [type = "io"];
    i_3 [type = "io"];
    o_out [type = "io"];

    mux [type = "mux", arg = $(M+1)];

    i_2 -> mux [to="in2"];
    i_1 -> mux [to="in1"];
    i_3 -> mux [to = "in3"];
    mux -> o_out [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["mux"] |>.get rfl

def rhsLower := (rhs_extract M).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l m => ⟨lhsLower l, rhsLower m⟩
    name := "mux-queue-right"
    transformedNodes := [.none, findRhs "mux"]
    addedNodes := []
    fresh_types := 1
  }

end Graphiti.MuxQueueRightRewrite
