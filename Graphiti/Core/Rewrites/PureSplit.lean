/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.PureJoinRight

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure" == typ.1 do return none

       let (.some join) := followOutput g inst "out1" | return none
       unless "join" == join.typ.1 ∧ join.inputPort = "in2" do return none

       return some ([inst, join.inst], #v[typ.2, join.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    o_out [type = "io"];

    pure [type = "pure", arg = $(T[0])];
    join [type = "join", arg = $(T[1])];

    i_0 -> join [to="in1"];
    i_1 -> pure [to="in1"];

    pure -> join [from="out1", to="in2"];

    join -> o_out [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["pure", "join"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    o_out [type = "io"];

    join [type = "join", arg = $(M+1)];
    pure [type = "pure", arg = $(M+2)];

    i_0 -> join [to="in1"];
    i_1 -> join [to="in2"];

    join -> pure [from="out1", to="in1"];

    pure -> o_out [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["pure", "join"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    transformedNodes := [findRhs "pure" |>.get rfl, findRhs "join" |>.get rfl]
    name := "pure-join-right"
    fresh_types := 2
  }

end Graphiti.PureJoinRight
