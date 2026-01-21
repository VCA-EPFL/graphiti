/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.SplitSinkRight

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "split" == typ.1 do return none

       let (.some sink) := followOutput g inst "out2" | return none
       unless "sink" == sink.typ.1 do return none

       return some ([inst, sink.inst], #v[typ.2, sink.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    split [type = "split", arg = $(T[0])];
    sink [type = "sink", arg = $(T[1])];

    i -> split [to="in1"];
    split -> o [from="out1"];

    split -> sink [from="out2", to="in1"];
  ]

def lhs_extract := (lhs T).extract ["split", "sink"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    pure [type = "pure", arg = $(M+1)];

    i -> pure [to="in1"];
    pure -> o [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["pure"] |>.get rfl

def rhsLower := (rhs_extract M).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "split-sink-right"
    transformedNodes := [.none, .none]
    addedNodes := [findRhs "pure" |>.get rfl]
    fresh_types := 1
  }

end Graphiti.SplitSinkRight
