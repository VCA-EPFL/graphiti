/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

open Batteries (AssocList)

namespace Graphiti.JoinSplitElim

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def identMatcher (s : String) : Pattern String (String × Nat) 2 := fun g => do
  let n ← ofOption (.error s!"{decl_name%}: could not find '{s}'") <| g.modules.find? s
  unless "join".isPrefixOf n.2 do throw (.error s!"{decl_name%}: type of '{s}' is '{n.2}' instead of 'join'")
  let next1 ← ofOption (.error s!"{decl_name%}: could not find next node") <| followInput g s "in1"
  unless "split".isPrefixOf next1.typ do
    throw (.error s!"{decl_name%}: type of '{next1.inst}' is '{next1.typ}' instead of 'split'")
  unless next1.inputPort = "out1" do throw (.error s!"{decl_name%}: output port of split is incorrect")
  let next2 ← ofOption (.error s!"{decl_name%}: could not find next node") <| followInput g s "in2"
  unless "split".isPrefixOf next2.typ do
    throw (.error s!"{decl_name%}: type of '{next2.inst}' is '{next2.typ}' instead of 'split'")
  unless next2.inputPort = "out2" do throw (.error s!"{decl_name%}: output port of split is incorrect")

  let (.some t1) := n.2.splitOn[1]? | throw (.error s!"{decl_name%}: type incorrect1")
  let (.some t2) := n.2.splitOn[2]? | throw (.error s!"{decl_name%}: type incorrect2")
  let (.some t1') := next1.typ.splitOn[1]? | throw (.error s!"{decl_name%}: type incorrect1")
  let (.some t2') := next1.typ.splitOn[2]? | throw (.error s!"{decl_name%}: type incorrect2")

  unless t1 = t1' ∧ t2 = t2' do
    throw (.error s!"{decl_name%}: types '{t1} ≠ {t1'}' or '{t2} ≠ {t2'}' do not match")
  unless next1.inst = next2.inst do
    throw (.error s!"{decl_name%}: join instances do not match: {next1.inst} ≠ {next2.inst}")

  return ([s, next1.inst], [t1, t2])

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) :=
  throw (.error s!"{decl_name%}: matcher not implemented")

def identRenaming (s : String) (g : ExprHigh String String) : RewriteResult (AssocList String (Option String)) :=
  pure .nil

def lhs (T₁ T₂ : Type) (S₁ S₂ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    o_out [type = "io"];

    split [typeImp = $(⟨_, split T₁ T₂⟩), type = $(s!"split {S₁} {S₂}")];
    join [typeImp = $(⟨_, join T₁ T₂⟩), type = $(s!"join {S₁} {S₂}")];

    i_0 -> split [to = "in1"];

    split -> join [from="out1", to="in1"];
    split -> join [from="out2", to="in2"];

    join -> o_out [from = "out1"];
  ]

def lhs_extract S₁ S₂ := (lhs Unit Unit S₁ S₂).fst.extract ["join", "split"] |>.get rfl

theorem double_check_empty_snd S₁ S₂ : (lhs_extract S₁ S₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower S₁ S₂ := (lhs_extract S₁ S₂).fst.lower.get rfl

def rhs (T₁ T₂ : Type) (S₁ S₂ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    o_out [type = "io"];

    pure [typeImp = $(⟨_, @StringModule.pure (T₁ × T₂) (T₁ × T₂) (λ a => a)⟩),
          type = $(s!"pure ({S₁}×{S₂}) ({S₁}×{S₂})")];

    i_0 -> pure [to = "in1"];
    pure -> o_out [from = "out1"];
  ]

def rhsLower S₁ S₂ := (rhs Unit Unit S₁ S₂).fst.lower.get rfl

def findRhs mod := (rhs Unit Unit "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂] => pure ⟨lhsLower S₁ S₂, rhsLower S₁ S₂⟩ | _ => failure,
    name := "join-split-elim"
    transformedNodes := [.none, .none]
    addedNodes := [findRhs "pure" |>.get rfl]
  }

def targetedRewrite (s : String) : Rewrite String String :=
  { rewrite with pattern := identMatcher s }

end Graphiti.JoinSplitElim
