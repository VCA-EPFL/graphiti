/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Rewriter
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Dataflow.Component

@[expose] public section

open Batteries (AssocList)

namespace Graphiti.JoinAssocR

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def identMatcher (join2 : String) : Pattern String (String × Nat) 2 := fun g => do
  let join2_typ ← ofOption' (.error s!"{decl_name%}: could not find '{join2}'") <| g.modules.find? join2
  unless "join" == join2_typ.2.1 do throw (.error s!"{decl_name%}: type of '{join2}' is '{join2_typ.2}' instead of 'join'")
  let join1 ← ofOption' (.error s!"{decl_name%}: could not find next node") <| followInput g join2 "in1"
  unless "join" == join1.typ.1 do throw (.error s!"{decl_name%}: type of '{join1.inst}' is '{join1.typ}' instead of 'join' 2")

  return ([join1.inst, join2], #v[join1.typ.2, join2_typ.2.2])

def matcher : Pattern String (String × Nat) 2 := fun g => do
  throw (.error s!"{decl_name%}: matcher not implemented")

def identRenaming (s : String) (g : ExprHigh String String) : RewriteResultSL (AssocList String (Option String)) := do
  let next ← ofOption' (.error s!"{decl_name%}: could not find next node") <| followInput g s "in1"
  return [(next.inst, (.some "join1")), (s, (.some "join2"))].toAssocList

def lhs : ExprHigh String (String × Nat) := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join1 [type = "join", arg = $(T[0])];
    join2 [type = "join", arg = $(T[1])];

    i_0 -> join1 [to = "in1"];
    i_1 -> join1 [to = "in2"];
    i_2 -> join2 [to = "in2"];

    join1 -> join2 [from = "out1", to = "in1"];

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

    join2 [type = "join", arg = $(M+1)];
    join1 [type = "join", arg = $(M+2)];
    pure [type = "pure", arg = $(M+3)];

    i_1 -> join2 [to = "in1"];
    i_2 -> join2 [to = "in2"];
    i_0 -> join1 [to = "in1"];

    join2 -> join1 [from = "out1", to = "in2"];
    join1 -> pure [from = "out1", to = "in1"];

    pure -> o_out [from = "out1"];
  ]

def rhs_extract := (rhs M).extract ["join1", "join2", "pure"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "join-assoc-right"
    transformedNodes := [findRhs "join1" |>.get rfl, findRhs "join2" |>.get rfl],
    addedNodes := [findRhs "pure" |>.get rfl]
    fresh_types := 3
  }

def targetedRewrite (s : String) :=
  { rewrite with pattern := identMatcher s }

end Graphiti.JoinAssocR
