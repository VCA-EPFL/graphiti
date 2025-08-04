/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayatallah Elakhras
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.JoinSplitLoopCondAlt

open StringModule

-- Search for a fork Bool 2 that feeds an Init and a Branch
def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
        unless typ = "init Bool false" do return none

      let (.some condFork) := followInput g inst "in1" | return none
      unless condFork.typ = "fork Bool 2" do return none

      -- Make sure that the input of the fork is not a split; otherwise, the matcher will apply forever
      let (.some genericInFork) := followInput g condFork.inst "in1" | return none

      let (.some branch) := followOutput g condFork.inst "out2" | return none
      unless String.isPrefixOf "branch" branch.typ && branch.inputPort = "in2" do return none

      let (.some genericInBranch) := followInput g branch.inst "in1" | return none

      unless ¬(genericInBranch.inst == genericInFork.inst) do return none

      return ([branch.inst, inst, condFork.inst], [extractType branch.typ])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs (T : Type) (Tₛ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    d_i [type = "io"];
    c_i [type = "io"];
    o_br_t [type = "io"];
    o_br_f [type = "io"];
    o_init [type = "io"];

    branch [typeImp = $(⟨_, branch T⟩), type = $("branch " ++ Tₛ)];
    condFork [typeImp = $(⟨_, fork Bool 2⟩), type = "fork Bool 2"];
    init [typeImp = $(⟨_, init Bool false⟩), type = "init Bool false"];

    c_i -> condFork [to="in1"];
    d_i -> branch [to="in1"];
    condFork -> branch [from="out2", to="in2"];
    condFork -> init [from="out1", to="in1"];

    branch -> o_br_t [from = "out1"];
    branch -> o_br_f [from = "out2"];
    init -> o_init [from = "out1"];
  ]

def lhs_extract T₁ := (lhs Unit T₁).fst.extract ["branch", "init", "condFork"] |>.get rfl

-- #eval IO.print ((lhs Unit Unit "T" "T'").fst)

theorem lhs_type_independent a c T₁ : (lhs a T₁).fst = (lhs c T₁).fst := by rfl

theorem double_check_empty_snd T₁ : (lhs_extract T₁).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T₁ := lhs_extract T₁ |>.fst.lower.get rfl

def rhs (T : Type) (Tₛ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    d_i [type = "io"];
    c_i [type = "io"];
    o_br_t [type = "io"];
    o_br_f [type = "io"];
    o_init [type = "io"];

    branch [typeImp = $(⟨_, branch T⟩), type = $("branch " ++ Tₛ)];
    condFork [typeImp = $(⟨_, fork Bool 2⟩), type = "fork Bool 2"];
    init [typeImp = $(⟨_, init Bool false⟩), type = "init Bool false"];
    join [typeImp = $(⟨_, join T Bool⟩), type = $("join " ++ Tₛ ++ " Bool")];
    split [typeImp = $(⟨_, split T Bool⟩), type = $("split " ++ Tₛ ++ " Bool")];

    d_i -> join [to="in1"];
    c_i -> join [to="in2"];

    join -> split [from="out1", to="in1"];

    split -> branch [from="out1", to="in1"];
    split -> condFork [from="out2", to="in1"];

    condFork -> branch [from="out1", to="in2"];
    condFork -> init [from="out2", to="in1"];

    branch -> o_br_t [from = "out1"];
    branch -> o_br_f [from = "out2"];
    init -> o_init [from = "out1"];
  ]

def rhsLower T₁ := (rhs Unit T₁).fst.lower.get rfl

-- #eval IO.print ((rhs Unit Unit "T" "T'").fst)

theorem rhs_type_independent a c T₁ : (rhs a T₁).fst = (rhs c T₁).fst := by rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ l => do
      let T₁ ← l.get? 0
      return ⟨ lhsLower T₁, rhsLower T₁ ⟩
    name := .some "join-split-loop-cond-alt"
  }

end Graphiti.JoinSplitLoopCondAlt
