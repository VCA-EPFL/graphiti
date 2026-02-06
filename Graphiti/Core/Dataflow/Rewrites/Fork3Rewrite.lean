/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayatallah Elakhras, Yann Herklotz
-/

module

public import Graphiti.Core.Rewriter
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Dataflow.Component

@[expose] public section

namespace Graphiti.Fork3Rewrite

open StringModule

def matcher : Pattern String (String × Nat) 1 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s

      unless "fork3" == typ.1 do return none

      return some ([inst], #v[typ])
    ) none | throw .done
  return list

def lhs (types : Vector Nat 1) : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];
    o3 [type = "io"];

    fork [type = "fork3", arg = $(types[0])];

    i -> fork [to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
    fork -> o3 [from="out3"];
  ]

def lhs_extract types := (lhs types).extract ["fork"] |>.get rfl

theorem double_check_empty_snd T : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T := lhs_extract T |>.fst.lower.get rfl

def rhs (m : Nat) : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];
    o3 [type = "io"];

    fork1 [type = "fork2", arg = $(m+1)];
    fork2 [type = "fork2", arg = $(m+2)];

    i -> fork1 [to="in1"];
    fork1 -> fork2 [from="out2", to="in1"];

    fork1 -> o1 [from="out1"];
    fork2 -> o2 [from="out1"];
    fork2 -> o3 [from="out2"];
  ]

def rhs_extract m := (rhs m).extract ["fork1", "fork2"] |>.get rfl

def rhsLower m := (rhs_extract m).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := []
    params := 1
    pattern := matcher
    rewrite := fun l m => ⟨lhsLower (l.map (·.2)), rhsLower m.2⟩
    name := .some "fork-3"
    transformedNodes := [.none]
    addedNodes := [findRhs "fork1" |>.get rfl, findRhs "fork2" |>.get rfl]
    fresh_types := fun x => (x.1, x.2+2)
  }

end Graphiti.Fork3Rewrite
