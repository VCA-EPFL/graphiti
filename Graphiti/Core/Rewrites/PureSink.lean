/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.PureSink

open StringModule

variable (T T' : Type)
variable (f : T → T')
variable [Inhabited T']
variable (S S' : String)

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure".isPrefixOf typ do return none

       let (.some sink) := followOutput g inst "out1" | return none
       unless "sink".isPrefixOf sink.typ do return none

       let (.some t1) := typ.splitOn[1]? | return none
       let (.some t2) := sink.typ.splitOn[1]? | return none
       let (.some t3) := typ.splitOn[2]? | return none

       unless t2 = t3 do return none

       return some ([inst, sink.inst], [t1, t2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];

    pure [typeImp = $(⟨_, pure f⟩), type = $(s!"pure {S} {S'}")];
    sink [typeImp = $(⟨_, sink T' 1⟩), type = $(s!"sink {S'} 1")];

    i -> pure [to="in1"];
    pure -> sink [from="out1", to="in1"];
  ]

def lhs_extract := (lhs Unit Unit (λ _ => default) S S').fst.extract ["pure", "sink"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S S').snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S S').fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];

    sink [typeImp = $(⟨_, sink (T × T') 1⟩), type = $(s!"sink ({S} × {S'}) 1")];

    i -> sink [to="in1"];
  ]

def rhs_extract := (rhs Unit Unit S S').fst.extract ["sink"] |>.get rfl

def rhsLower := (rhs_extract S S').fst.lower.get rfl

def findRhs mod := (rhs_extract "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S, S'] => .some ⟨lhsLower S S', rhsLower S S'⟩ | _ => failure
    name := "pure-sink"
    transformedNodes := [.none, findRhs "sink" |>.get rfl]
  }

end Graphiti.PureSink
