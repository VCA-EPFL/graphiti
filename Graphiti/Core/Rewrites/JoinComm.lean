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

variable (T : Vector Nat 1)
variable (M : Nat)

def identMatcher (s : String) : Pattern String (String × Nat) 1 := fun g => do
  let n ← ofOption' (.error s!"{decl_name%}: could not find '{s}'") <| g.modules.find? s
  unless "join" == n.2.1 do throw (.error s!"{decl_name%}: type of '{s}' is '{n.2}' instead of 'join'")
  return ([s], #v[n.2.2])

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: matcher not implemented")

def identRenaming (s : String) (g : ExprHigh String String) : RewriteResult (AssocList String (Option String)) := do
  return (.cons s "joinN" .nil)

def lhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    o_out [type = "io"];

    join [type = "join", arg = $(T[0])];

    i_0 -> join [to = "in1"];
    i_1 -> join [to = "in2"];

    join -> o_out [from = "out1"];
  ]

def lhs_extract := (lhs T).extract ["join"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    o_out [type = "io"];

    joinN [type = "join", arg = $(M+1)];
    pure [type = "pure", arg = $(M+2)];

    i_0 -> joinN [to = "in2"];
    i_1 -> joinN [to = "in1"];

    joinN -> pure [from="out1", to="in1"];

    pure -> o_out [from = "out1"];
  ]

def rhs_extract := (rhs M).extract ["joinN", "pure"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := []
    params := 1
    pattern := matcher
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "join-comm"
    transformedNodes := [findRhs "joinN" |>.get rfl]
    addedNodes := [findRhs "pure" |>.get rfl]
    fresh_types := 2
  }

def targetedRewrite s := { rewrite with pattern := identMatcher s }

end Graphiti.JoinComm
