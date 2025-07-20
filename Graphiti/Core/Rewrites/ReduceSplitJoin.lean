/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayatallah Elakhras
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.ReduceSplitJoin

open StringModule

def extractFirstWordAfterJoin (s : String) : String :=
  match s.drop 5 |>.splitOn " " with
  | []      => ""
  | x :: _  => x

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
        unless String.isPrefixOf "split" typ do return none
      let (.some join_nn) := followOutput g inst "out1" | return none
      let (.some join_nn') := followOutput g inst "out2" | return none

      unless String.isPrefixOf "join" join_nn.typ && String.isPrefixOf "join" join_nn'.typ do return none
      unless join_nn.inst = join_nn'.inst do return none
      unless join_nn.inputPort = "in1" && join_nn'.inputPort = "in2" do return none
      unless extractType join_nn.typ = extractType typ do return none
      let .some typ1 := join_nn.typ.splitOn " " |>.get? 1 | throw (.error "Could not extract type 1 from 'join'")
      let .some typ2 := join_nn.typ.splitOn " " |>.get? 2 | throw (.error "Could not extract type 2 from 'join'")

      return some ([join_nn.inst, inst], [typ1, typ2])
    ) none | throw .done
  return list

def lhs (T T' : Type) (Tₛ T'ₛ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    split [typeImp = $(⟨_, split T T'⟩), type = $(s!"split {Tₛ} {T'ₛ}")];
    join [typeImp = $(⟨_, join T T'⟩), type = $(s!"join {Tₛ} {T'ₛ}")];

    i -> split [to="in1"];
    split -> join [from="out1", to="in1"];
    split -> join [from="out2", to="in2"];
    join -> o [from="out1"];
  ]

def lhs_extract T₁ T₂ := (lhs Unit Unit T₁ T₂).fst.extract ["join", "split"] |>.get rfl

-- #eval IO.print ((lhs Unit Unit "T" "T'").fst)

theorem lhs_type_independent a b c d T₁ T₂ : (lhs a b T₁ T₂).fst = (lhs c d T₁ T₂).fst := by rfl

theorem double_check_empty_snd T₁ T₂ : (lhs_extract T₁ T₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T₁ T₂ := lhs_extract T₁ T₂ |>.fst.lower.get rfl

def rhs (T T' : Type) (Tₛ T'ₛ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    queue [typeImp = $(⟨_, queue T⟩), type = $(s!"queue ({Tₛ}×{T'ₛ})")];

    i -> queue [to="in1"];
    queue -> o [from="out1"];
  ]

def rhsLower T₁ T₂ := (rhs Unit Unit T₁ T₂).fst.lower.get rfl

-- #eval IO.print ((rhs Unit Unit "T" "T'").fst)

theorem rhs_type_independent a b c d T₁ T₂ : (rhs a b T₁ T₂).fst = (rhs c d T₁ T₂).fst := by rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ l => do
      let T₁ ← l.get? 0
      let T₂ ← l.get? 1
      return ⟨lhsLower T₁ T₂, rhsLower T₁ T₂⟩
    name := .some "reduce-split-join"
  }

end Graphiti.ReduceSplitJoin
