/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

open Batteries (AssocList)

namespace Graphiti.JoinComm

open StringModule

def identMatcher (s : String) (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let n ← ofOption (.error s!"{decl_name%}: could not find '{s}'") <| g.modules.find? s
  unless "join".isPrefixOf n.2 do throw (.error s!"{decl_name%}: type of '{s}' is '{n.2}' instead of 'join'")

  let (.some t1) := n.2.splitOn |>.get? 1 | throw (.error s!"{decl_name%}: type incorrect1")
  let (.some t2) := n.2.splitOn |>.get? 2 | throw (.error s!"{decl_name%}: type incorrect2")

  return ([s], [t1, t2])

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) :=
  throw (.error s!"{decl_name%}: matcher not implemented")

def identRenaming (s : String) (g : ExprHigh String String) : RewriteResult (AssocList String (Option String)) := do
  return (.cons s "joinN" .nil)

def lhs (T₁ T₂ : Type) (S₁ S₂ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    o_out [type = "io"];

    join [typeImp = $(⟨_, join T₁ T₂⟩), type = $(s!"join {S₁} {S₂}")];

    i_0 -> join [to = "in1"];
    i_1 -> join [to = "in2"];

    join -> o_out [from = "out1"];
  ]

def lhs_extract S₁ S₂ := (lhs Unit Unit S₁ S₂).fst.extract ["join"] |>.get rfl

theorem double_check_empty_snd S₁ S₂ : (lhs_extract S₁ S₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower S₁ S₂ := (lhs_extract S₁ S₂).fst.lower.get rfl

def rhs (T₁ T₂ : Type) (S₁ S₂ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    o_out [type = "io"];

    joinN [typeImp = $(⟨_, join T₂ T₁⟩), type = $(s!"join {S₂} {S₁}")];
    pure [typeImp = $(⟨_, @StringModule.pure (T₂ × T₁) (T₁ × T₂) (λ (a, b) => (b, a))⟩),
          type = $(s!"pure ({S₂}×{S₁}) ({S₁}×{S₂})")];

    i_0 -> joinN [to = "in2"];
    i_1 -> joinN [to = "in1"];

    joinN -> pure [from="out1", to="in1"];

    pure -> o_out [from = "out1"];
  ]

def rhs_extract S₁ S₂ := (rhs Unit Unit S₁ S₂).fst.extract ["joinN", "pure"] |>.get rfl

def rhsLower S₁ S₂ := (rhs_extract S₁ S₂).fst.lower.get rfl

def findRhs mod := (rhs_extract "" "").fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂] => pure ⟨lhsLower S₁ S₂, rhsLower S₁ S₂⟩ | _ => failure,
    name := "join-comm"
    transformedNodes := [findRhs "joinN" |>.get rfl]
    addedNodes := [findRhs "pure" |>.get rfl]
  }

def targetedRewrite (s : String) : Rewrite String String :=
  { rewrite with pattern := identMatcher s }

end Graphiti.JoinComm
