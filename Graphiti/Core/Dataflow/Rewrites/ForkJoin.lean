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

namespace Graphiti.ForkJoin

open StringModule

variable (T : Vector Nat 2)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "join" == typ.1 do return none

       let (.some p) := followOutput g inst "out1" | return none
       unless "fork2" == p.typ.1 do return none

       return some ([inst, p.inst], #v[typ, p.typ])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    join [type = "join", arg = $(T[0])];
    fork [type = "fork2", arg = $(T[1])];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];
    join -> fork [from="out1",to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
  ]

def lhs_extract := (lhs T).extract ["join", "fork"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    fork1 [type = "fork2", arg = $(M+1)];
    fork2 [type = "fork2", arg = $(M+2)];
    join1 [type = "join", arg = $(M+3)];
    join2 [type = "join", arg = $(M+4)];

    i1 -> fork1 [to="in1"];
    i2 -> fork2 [to="in1"];
    fork1 -> join1 [from="out1",to="in1"];
    fork2 -> join1 [from="out1",to="in2"];
    fork1 -> join2 [from="out2",to="in1"];
    fork2 -> join2 [from="out2",to="in2"];
    join1 -> o1 [from="out1"];
    join2 -> o2 [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["fork1", "fork2", "join1", "join2"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := 2
  pattern := matcher
  rewrite := λ l n => ⟨lhsLower (l.map (·.2)), rhsLower n.2⟩
  name := "fork-join"
  transformedNodes := [.none, .none]
  addedNodes := [ findRhs "fork1" |>.get rfl, findRhs "fork2" |>.get rfl
                , findRhs "join1" |>.get rfl, findRhs "join2" |>.get rfl]
  fresh_types := fun x => (x.1, x.2+4)


end Graphiti.ForkJoin
