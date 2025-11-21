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

variable (T : Vector Nat 2)
variable (M : Nat)

def identMatcher (s : String) : Pattern String (String × Nat) 2 := fun g => do
  let n ← ofOption' (.error s!"{decl_name%}: could not find '{s}'") <| g.modules.find? s
  unless "join" == n.2.1 do throw (.error s!"{decl_name%}: type of '{s}' is '{n.2}' instead of 'join'")
  let next ← ofOption' (.error s!"{decl_name%}: could not find next node") <| followInput g s "in2"
  unless "join" == next.typ.1 do throw (.error s!"{decl_name%}: type of '{next.inst}' is '{next.typ}' instead of 'join'")

  return ([s, next.inst], #v[n.2.2, next.typ.2])

def matcher : Pattern String (String × Nat) 2 := fun g => do
  throw (.error s!"{decl_name%}: matcher not implemented")

def identRenaming (s : String) (g : ExprHigh String String) : RewriteResultSL (AssocList String (Option String)) := do
  let next ← ofOption' (.error s!"{decl_name%}: could not find next node") <| followInput g s "in2"
  return [(next.inst, (.some "join1")), (s, (.some "join2"))].toAssocList

def lhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join1 [type = "join", arg = $(T[0])];
    join2 [type = "join", arg = $(T[1])];

    i_0 -> join2 [to = "in1"];
    i_1 -> join1 [to = "in1"];
    i_2 -> join1 [to = "in2"];

    join1 -> join2 [from = "out1", to = "in2"];

    join2 -> o_out [from = "out1"];
  ]

def lhs_extract := (lhs T).extract ["join1", "join2"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join2 [type = "split", arg = $(M+1)];
    join1 [type = "split", arg = $(M+2)];
    pure [type = "pure", arg = $(M+3)];

    i_0 -> join2 [to = "in1"];
    i_1 -> join2 [to = "in2"];
    i_2 -> join1 [to = "in2"];

    join2 -> join1 [from = "out1", to = "in1"];
    join1 -> pure [from = "out1", to = "in1"];

    pure -> o_out [from = "out1"];
  ]

def rhs_extract := (rhs M).extract ["join2", "join1", "pure"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "join-assoc-left"
    transformedNodes := [findRhs "join2" |>.get rfl, findRhs "join1" |>.get rfl],
    addedNodes := [findRhs "pure" |>.get rfl]
    fresh_types := 3
  }

def targetedRewrite (s : String) :=
  { rewrite with pattern := identMatcher s }

end Graphiti.JoinAssocL
