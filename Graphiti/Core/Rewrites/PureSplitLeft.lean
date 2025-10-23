/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.PureSplitLeft

open StringModule

variable (T₁ T₂ T₃ : Type)
variable (f : T₂ → T₃)
variable (S₁ S₂ S₃ : String)

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "split".isPrefixOf typ do return none

       let (.some p) := followOutput g inst "out1" | return none
       unless "pure".isPrefixOf p.typ do return none

       let (.some t2) := p.typ.splitOn[1]? | return none
       let (.some t3) := p.typ.splitOn[2]? | return none
       let (.some t1) := typ.splitOn[2]? | return none

       return some ([inst, p.inst], [t1, t2, t3])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    split [typeImp = $(⟨_, split T₂ T₁⟩), type = $(s!"split {S₂} {S₁}")];
    pure [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure {S₂} {S₃}")];

    i -> split [to="in1"];
    pure -> o1 [from="out1"];
    split -> o2 [from="out2"];

    split -> pure [from="out1", to="in1"];
  ]

def lhs_extract := (lhs Unit Unit Unit (λ _ => default) S₁ S₂ S₃).fst.extract ["split", "pure"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁ S₂ S₃).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁ S₂ S₃).fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    split [typeImp = $(⟨_, split T₃ T₁⟩), type = $(s!"split {S₃} {S₁}")];
    pure [typeImp = $(⟨_, StringModule.pure λ (x : T₂×T₁) => (f x.1, x.2)⟩), type = $(s!"pure ({S₂}×{S₁}) ({S₃}×{S₁})")];

    i -> pure [to="in1"];
    pure -> split [from="out1", to="in1"];
    split -> o1 [from="out1"];
    split -> o2 [from="out2"];
  ]

def rhsLower := (rhs Unit Unit Unit (λ _ => default) S₁ S₂ S₃).fst.lower.get rfl

def findRhs mod := (rhs Unit Unit Unit (λ _ => default) "" "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂, S₃] => .some ⟨lhsLower S₁ S₂ S₃, rhsLower S₁ S₂ S₃⟩ | _ => failure,
    name := "pure-split-left"
    transformedNodes := [findRhs "split" |>.get rfl, findRhs "pure" |>.get rfl]
  }

end Graphiti.PureSplitLeft
