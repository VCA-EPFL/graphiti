/-
Copyright (c) 2024, 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayatallah Elakhras, Yann Herklotz
-/

module

public import Graphiti.Core.Rewriter
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Dataflow.Component

@[expose] public section

namespace Graphiti.Fork9Rewrite

open StringModule

def matcher : Pattern String (String × Nat) 1 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s

      unless "fork9" == typ.1 do return none

      return some ([inst], #v[typ.2])
    ) none | throw .done
  return list

def lhs (types : Vector Nat 1) : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];
    o3 [type = "io"];
    o4 [type = "io"];
    o5 [type = "io"];
    o6 [type = "io"];
    o7 [type = "io"];
    o8 [type = "io"];
    o9 [type = "io"];

    fork [type = "fork9", arg = $(types[0])];

    i -> fork [to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
    fork -> o3 [from="out3"];
    fork -> o4 [from="out4"];
    fork -> o5 [from="out5"];
    fork -> o6 [from="out6"];
    fork -> o7 [from="out7"];
    fork -> o8 [from="out8"];
    fork -> o9 [from="out9"];
  ]

def lhs_extract T₁ := (lhs T₁).extract ["fork"] |>.get rfl

theorem double_check_empty_snd T₁ : (lhs_extract T₁).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T₁ := lhs_extract T₁ |>.fst.lower.get rfl

def rhs (m : Nat) : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];
    o3 [type = "io"];
    o4 [type = "io"];
    o5 [type = "io"];
    o6 [type = "io"];
    o7 [type = "io"];
    o8 [type = "io"];
    o9 [type = "io"];

    fork1 [type = "fork2", arg = $(m+1)];
    fork2 [type = "fork8", arg = $(m+2)];

    i -> fork1 [to="in1"];
    fork1 -> fork2 [from="out2", to="in1"];

    fork1 -> o1 [from="out1"];
    fork2 -> o2 [from="out1"];
    fork2 -> o3 [from="out2"];
    fork2 -> o4 [from="out3"];
    fork2 -> o5 [from="out4"];
    fork2 -> o6 [from="out5"];
    fork2 -> o7 [from="out6"];
    fork2 -> o8 [from="out7"];
    fork2 -> o9 [from="out8"];
  ]

def rhs_extract S₁ := (rhs S₁).extract ["fork1", "fork2"] |>.get rfl

def rhsLower T₁ := (rhs_extract T₁).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := []
    params := 1
    pattern := matcher
    rewrite := λ l m => ⟨lhsLower l, rhsLower m⟩
    name := .some "fork-9"
    transformedNodes := [.none]
    addedNodes := [findRhs "fork1" |>.get rfl, findRhs "fork2" |>.get rfl]
    fresh_types := 2
  }

end Graphiti.Fork9Rewrite
