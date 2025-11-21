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
  let n ← ofOption' (.error s!"{decl_name%}: could not find '{s}'") <| g.modules.find? s
  unless "join" == n.2.1 do throw (.error s!"{decl_name%}: type of '{s}' is '{n.2}' instead of 'join'")
  let next1 ← ofOption' (.error s!"{decl_name%}: could not find next node") <| followInput g s "in1"
  unless "split" == next1.typ.1 do
    throw (.error s!"{decl_name%}: type of '{next1.inst}' is '{next1.typ}' instead of 'split'")
  unless next1.inputPort == "out1" do throw (.error s!"{decl_name%}: output port of split is incorrect")
  let next2 ← ofOption' (.error s!"{decl_name%}: could not find next node") <| followInput g s "in2"
  unless "split" == next2.typ.1 do
    throw (.error s!"{decl_name%}: type of '{next2.inst}' is '{next2.typ}' instead of 'split'")
  unless next2.inputPort == "out2" do throw (.error s!"{decl_name%}: output port of split is incorrect")

  return ([s, next1.inst], #v[n.2.2, next1.typ.2])

def matcher : Pattern String (String × Nat) 2 := fun g => do
  throw (.error s!"{decl_name%}: matcher not implemented")

def identRenaming (s : String) (g : ExprHigh String (String × Nat)) : RewriteResult (AssocList String (Option String)) :=
  pure .nil

def lhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    o_out [type = "io"];

    split [type = "split", arg = $(T[0])];
    join [type = "join", arg = $(T[1])];

    i_0 -> split [to = "in1"];

    split -> join [from="out1", to="in1"];
    split -> join [from="out2", to="in2"];

    join -> o_out [from = "out1"];
  ]

def lhs_extract := (lhs T).extract ["split", "join"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    o_out [type = "io"];

    pure [type = "pure", arg = $(M+1)];

    i_0 -> pure [to = "in1"];
    pure -> o_out [from = "out1"];
  ]

def rhs_extract := (rhs M).extract ["pure"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "join-split-elim"
    transformedNodes := [.none, .none]
    addedNodes := [findRhs "pure" |>.get rfl]
    fresh_types := 1
  }

def targetedRewrite (s : String) := { rewrite with pattern := identMatcher s }

end Graphiti.JoinSplitElim
