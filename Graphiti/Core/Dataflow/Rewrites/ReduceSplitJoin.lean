/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayatallah Elakhras
-/

module

public import Graphiti.Core.Rewriter
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Dataflow.Component

@[expose] public section

namespace Graphiti.ReduceSplitJoin

open StringModule

def extractFirstWordAfterJoin (s : String) : String :=
  match s.drop 5 |>.copy |>.splitOn " " with
  | []      => ""
  | x :: _  => x

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s

      unless "split" == typ.1 do return none
      let (.some join_nn) := followOutput g inst "out1" | return none
      let (.some join_nn') := followOutput g inst "out2" | return none

      unless "join" == join_nn.typ.1 && "join" == join_nn'.typ.1 do return none
      unless join_nn.inst = join_nn'.inst do return none
      unless join_nn.inputPort = "in1" && join_nn'.inputPort = "in2" do return none

      return some ([join_nn.inst, inst], #v[join_nn.typ, typ])
    ) none | throw .done
  return list

def lhs (T : Vector Nat 2) : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    split [type = "split", arg = $(T[1])];
    join [type = "join", arg = $(T[0])];

    i -> split [to="in1"];
    split -> join [from="out1", to="in1"];
    split -> join [from="out2", to="in2"];
    join -> o [from="out1"];
  ]

def lhs_extract T := (lhs T).extract ["join", "split"] |>.get rfl

-- #eval IO.print ((lhs Unit Unit "T" "T'").fst)

theorem double_check_empty_snd T : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T := lhs_extract T |>.fst.lower.get rfl

def rhs (M : Nat) : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    queue [type = "queue", arg = $(M+1)];

    i -> queue [to="in1"];
    queue -> o [from="out1"];
  ]

def rhs_extract M := (rhs M).extract ["queue"] |>.get rfl

def rhsLower M := (rhs_extract M).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

-- #eval IO.print ((rhs Unit Unit "T" "T'").fst)

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 2
    pattern := matcher,
    rewrite := λ l m => ⟨lhsLower (l.map (·.2)), rhsLower m.2⟩
    transformedNodes := [.none, .none]
    addedNodes := [findRhs "queue" |>.get rfl]
    name := .some "reduce-split-join"
    fresh_types := fun x => (x.1, x.2+1)
  }

end Graphiti.ReduceSplitJoin
