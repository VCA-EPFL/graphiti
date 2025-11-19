/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.ForkPure

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure" == typ.1 do return none

       let (.some p) := followOutput g inst "out1" | return none
       unless "fork" == p.typ.1 do return none

       return some ([inst, p.inst], #v[typ.2, p.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    pure [type = "pure", arg = $(T[0])];
    fork [type = "fork", arg = $(T[1])];

    i -> pure [to="in1"];
    pure -> fork [from="out1",to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
  ]

def lhs_extract := (lhs T).extract ["pure", "fork"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    fork [type = "fork", arg = $(M+1)];
    pure1 [type = "pure", arg = $(M+2)];
    pure2 [type = "pure", arg = $(M+3)];

    i -> fork [to="in1"];
    fork -> pure1 [from="out1",to="in1"];
    fork -> pure2 [from="out2",to="in1"];
    pure1 -> o1 [from="out1"];
    pure2 -> o2 [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["fork", "pure1", "pure2"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "fork-pure"
    transformedNodes := [.none, findRhs "fork" |>.get rfl]
    addedNodes := [findRhs "pure1" |>.get rfl, findRhs "pure2" |>.get rfl]
    fresh_types := 3
  }

end Graphiti.ForkPure
