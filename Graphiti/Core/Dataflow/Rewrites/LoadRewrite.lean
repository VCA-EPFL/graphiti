/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.LoadRewrite

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless typ.1 == "load" do return none

       let (.some mc) := followOutput g inst "out2" | return none
       unless "mc" == mc.typ.1 do return none

       let (.some load) := followOutput g mc.inst "out1" | return none
       unless load.inst = inst do return none

       return some ([inst, mc.inst], #v[typ.2, mc.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    load [type = "load", arg = $(T[0])];
    mc [type = "mc", arg = $(T[1])];

    i_in -> load [to = "in2"];
    load -> o_out [from = "out1"];

    load -> mc [from = "out2", to = "in1"];
    mc -> load [from = "out1", to = "in1"];
  ]

def lhs_extract := (lhs T).extract ["load", "mc"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    pure [type = "pure", arg = $(M+1)];

    i_in -> pure [to = "in1"];
    pure -> o_out [from = "out1"];
  ]

def rhs_extract := (rhs M).extract ["pure"] |>.get rfl

def rhsLower := (rhs_extract M).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "load-rewrite"
    transformedNodes := [.none, .none]
    addedNodes := [findRhs "pure" |>.get rfl]
    fresh_types := 1
  }

end Graphiti.LoadRewrite
