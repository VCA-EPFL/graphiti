/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Rewriter
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Dataflow.Component

@[expose] public section

namespace Graphiti.JoinQueueRightRewrite

open StringModule

variable (types : Vector Nat 2)
variable (m : Nat)

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "queue" == typ.1 do return none

       let (.some join) := followOutput g inst "out1" | return none
       unless "join" == join.typ.1 ∧ join.inputPort = "in2" do return none

       return some ([inst, join.inst], #v[typ.2, join.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    q [type = "queue", arg = $(types[0])];
    join [type = "join", arg = $(types[1])];

    i_2 -> q [to = "in1"];
    i_1 -> join [to = "in1"];
    join -> o_out [from="out1"];

    q -> join [from="out1", to="in2"];
  ]

def lhs_extract := (lhs types).extract ["q", "join"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract types).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract types).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join [type = "join", arg = $(m+1)];

    i_1 -> join [to = "in1"];
    i_2 -> join [to = "in2"];
    join -> o_out [from="out1"];
  ]

def rhs_extract := (rhs m).extract ["join"] |>.get rfl

def rhsLower := (rhs_extract m).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ f n => ⟨lhsLower f, rhsLower n⟩
    transformedNodes := [.none, findRhs "join"]
    addedNodes := []
    name := "join-queue-right"
    fresh_types := 1
  }

end Graphiti.JoinQueueRightRewrite
