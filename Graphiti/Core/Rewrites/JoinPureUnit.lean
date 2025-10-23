/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.JoinPureUnit

open StringModule

variable (T₁ T₂ : Type)
variable (f : T₁ × Unit → T₂)
variable (S₁ S₂ : String)

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "join".isPrefixOf typ do return none

       let (.some p) := followOutput g inst "out1" | return none
       unless "pure".isPrefixOf p.typ do return none

       let (.some t1) := p.typ.splitOn[2]? | return none
       let (.some jt1) := typ.splitOn[1]? | return none
       let (.some jt2) := typ.splitOn[2]? | return none

       unless jt2 = "Unit" do return none

       return some ([inst, p.inst], [jt1, t1])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    join [typeImp = $(⟨_, join T₁ Unit⟩), type = $(s!"join {S₁} Unit")];
    pure [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure ({S₁}×Unit) {S₂}")];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];
    join -> pure [from="out1",to="in1"];
    pure -> o [from="out1"];
  ]

def lhs_extract := (lhs Unit Unit (λ _ => default) S₁ S₂).fst.extract ["join", "pure"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁ S₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁ S₂).fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    pure [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure {S₁} {S₂}")];
    sink [typeImp = $(⟨_, sink Unit 1⟩), type = $("sink Unit 1")];

    i1 -> pure [to="in1"];
    i2 -> sink [to="in1"];
    pure -> o [from="out1"];
  ]

def rhsLower := (rhs Unit Unit (λ _ => default) S₁ S₂).fst.lower.get rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂] => .some ⟨lhsLower S₁ S₂, rhsLower S₁ S₂⟩ | _ => failure,
    name := "join-pure-unit"
  }

end Graphiti.JoinPureUnit
