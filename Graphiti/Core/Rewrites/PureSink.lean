/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.PureSink

open StringModule

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure" == typ.1 do return none

       let (.some sink) := followOutput g inst "out1" | return none
       unless "sink" == sink.typ.1 do return none

       return some ([inst, sink.inst], #v[typ.2, sink.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

variable (types : Vector Nat 2)

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];

    pure [typeImp = $(⟨_, pure f⟩), type = "pure", arg = $(types[0])];
    sink [typeImp = $(⟨_, sink T' 1⟩), type = "sink", arg = $(types[1])];

    i -> pure [to="in1"];
    pure -> sink [from="out1", to="in1"];
  ]

def lhs_extract := (lhs types).extract ["pure", "sink"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract types).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract types).fst.lower.get rfl

variable (max_type : Nat)

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];

    sink [type = "sink", arg = $(max_type+1)];

    i -> sink [to="in1"];
  ]

def rhs_extract := (rhs max_type).extract ["sink"] |>.get rfl

def rhsLower := (rhs_extract max_type).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { params := 2
    abstractions := [],
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "pure-sink"
    transformedNodes := [.none, findRhs "sink" |>.get rfl]
  }

end Graphiti.PureSink
