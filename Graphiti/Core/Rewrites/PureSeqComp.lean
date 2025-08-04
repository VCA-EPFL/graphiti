/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.PureSeqComp

open StringModule

variable (T₁ T₂ T₃ : Type)
variable (f : T₁ → T₂) (g : T₂ → T₃)
variable (S₁ S₂ S₃ : String)

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure".isPrefixOf typ do return none

       let (.some join) := followOutput g inst "out1" | return none
       unless "pure".isPrefixOf join.typ do return none

       let (.some t1) := typ.splitOn |>.get? 1 | return none
       let (.some t2) := typ.splitOn |>.get? 2 | return none
       let (.some t2') := join.typ.splitOn |>.get? 1 | return none
       let (.some t3) := join.typ.splitOn |>.get? 2 | return none

       unless t2 = t2' do return none

       return some ([inst, join.inst], [t1, t2, t3])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    o_out [type = "io"];

    puref [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure {S₁} {S₂}")];
    pureg [typeImp = $(⟨_, StringModule.pure g⟩), type = $(s!"pure {S₂} {S₃}")];

    i_0 -> puref [to="in1"];

    puref -> pureg [from="out1", to="in1"];

    pureg -> o_out [from="out1"];
  ]

def lhs_extract := (lhs Unit Unit Unit (λ _ => default) (λ _ => default) S₁ S₂ S₃).fst.extract ["puref", "pureg"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁ S₂ S₃).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁ S₂ S₃).fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    o_out [type = "io"];

    pure [typeImp = $(⟨_, StringModule.pure (g ∘ f)⟩), type = $(s!"pure {S₁} {S₃}")];

    i_0 -> pure [to="in1"];
    pure -> o_out [from="out1"];
  ]

def rhsLower := (rhs Unit Unit Unit (λ _ => default) (λ _ => default) S₁ S₃).fst.lower.get rfl

def findRhs mod := (rhs Unit Unit Unit (λ _ => default) (λ _ => default) "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂, S₃] => .some ⟨lhsLower S₁ S₂ S₃, rhsLower S₁ S₃⟩ | _ => failure,
    name := "pure-seq-comp"
    transformedNodes := [.none, .none]
    addedNodes := [findRhs "pure" |>.get rfl]
  }

end Graphiti.PureSeqComp
