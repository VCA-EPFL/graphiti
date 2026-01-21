/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.PureSplitRight

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "split" == typ.1 do return none

       let (.some p) := followOutput g inst "out2" | return none
       unless "pure" == p.typ.1 do return none

       return some ([inst, p.inst], #v[typ.2, p.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    split [type = "split", arg = $(T[0])];
    pure [type = "pure", arg = $(T[1])];

    i -> split [to="in1"];
    split -> o1 [from="out1"];
    pure -> o2 [from="out1"];

    split -> pure [from="out2", to="in1"];
  ]

def lhs_extract := (lhs T).extract ["split", "pure"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    split [type = "split", arg = $(M+1)];
    pure [type = "pure", arg = $(M+2)];

    i -> pure [to="in1"];
    pure -> split [from="out1", to="in1"];
    split -> o1 [from="out1"];
    split -> o2 [from="out2"];
  ]

def rhs_extract := (rhs M).extract ["split", "pure"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "pure-split-right"
    transformedNodes := [findRhs "split" |>.get rfl, findRhs "pure" |>.get rfl]
    fresh_types := 2
  }

end Graphiti.PureSplitRight
