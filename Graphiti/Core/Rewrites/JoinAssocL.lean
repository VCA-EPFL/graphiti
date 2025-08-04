/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

open Batteries (AssocList)

namespace Graphiti.JoinAssocL

open StringModule

def identMatcher (s : String) (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let n ← ofOption (.error s!"{decl_name%}: could not find '{s}'") <| g.modules.find? s
  unless "join".isPrefixOf n.2 do throw (.error s!"{decl_name%}: type of '{s}' is '{n.2}' instead of 'join'")
  let next ← ofOption (.error s!"{decl_name%}: could not find next node") <| followInput g s "in2"
  unless "join".isPrefixOf next.typ do throw (.error s!"{decl_name%}: type of '{next.inst}' is '{next.typ}' instead of 'join'")

  let (.some t1) := n.2.splitOn |>.get? 1 | throw (.error s!"{decl_name%}: type incorrect3")
  let (.some t2) := next.typ.splitOn |>.get? 1 | throw (.error s!"{decl_name%}: type incorrect1")
  let (.some t3) := next.typ.splitOn |>.get? 2 | throw (.error s!"{decl_name%}: type incorrect2")

  return ([s, next.inst], [t1, t2, t3])

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) :=
  throw (.error s!"{decl_name%}: matcher not implemented")

def identRenaming (s : String) (g : ExprHigh String String) : RewriteResult (AssocList String (Option String)) := do
  let next ← ofOption (.error s!"{decl_name%}: could not find next node") <| followInput g s "in2"
  return [(next.inst, (.some "join1")), (s, (.some "join2"))].toAssocList

def lhs (T₁ T₂ T₃ : Type) (S₁ S₂ S₃ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join1 [typeImp = $(⟨_, join T₂ T₃⟩), type = $(s!"join {S₂} {S₃}")];
    join2 [typeImp = $(⟨_, join T₁ (T₂ × T₃)⟩), type = $(s!"join {S₁} ({S₂}×{S₃})")];

    i_0 -> join2 [to = "in1"];
    i_1 -> join1 [to = "in1"];
    i_2 -> join1 [to = "in2"];

    join1 -> join2 [from = "out1", to = "in2"];

    join2 -> o_out [from = "out1"];
  ]

def lhs_extract S₁ S₂ S₃ := (lhs Unit Unit Unit S₁ S₂ S₃).fst.extract ["join2", "join1"] |>.get rfl

theorem double_check_empty_snd S₁ S₂ S₃ : (lhs_extract S₁ S₂ S₃).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower S₁ S₂ S₃ := (lhs_extract S₁ S₂ S₃).fst.lower.get rfl

def rhs (T₁ T₂ T₃ : Type) (S₁ S₂ S₃ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join2 [typeImp = $(⟨_, join T₁ T₂⟩), type = $(s!"join {S₁} {S₂}")];
    join1 [typeImp = $(⟨_, join (T₁ × T₂) T₃⟩), type = $(s!"join ({S₁}×{S₂}) {S₃}")];
    pure [typeImp = $(⟨_, StringModule.pure (λ (((a, b), c) : (T₁ × T₂) × T₃) => (a, (b, c)))⟩),
          type = $(s!"pure (({S₁}×{S₂})×{S₃}) ({S₁}×({S₂}×{S₃}))")];

    i_0 -> join2 [to = "in1"];
    i_1 -> join2 [to = "in2"];
    i_2 -> join1 [to = "in2"];

    join2 -> join1 [from = "out1", to = "in1"];
    join1 -> pure [from = "out1", to = "in1"];

    pure -> o_out [from = "out1"];
  ]

def rhs_extract S₁ S₂ S₃ := (rhs Unit Unit Unit S₁ S₂ S₃).fst.extract ["join2", "join1", "pure"] |>.get rfl

def rhsLower S₁ S₂ S₃ := (rhs_extract S₁ S₂ S₃).fst.lower.get rfl

def findRhs mod := (rhs_extract "" "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂, S₃] => pure ⟨lhsLower S₁ S₂ S₃, rhsLower S₁ S₂ S₃⟩ | _ => failure,
    name := "join-assoc-left"
    transformedNodes := [findRhs "join2" |>.get rfl, findRhs "join1" |>.get rfl],
    addedNodes := [findRhs "pure" |>.get rfl]
  }

def targetedRewrite (s : String) : Rewrite String String :=
  { rewrite with pattern := identMatcher s }

end Graphiti.JoinAssocL
