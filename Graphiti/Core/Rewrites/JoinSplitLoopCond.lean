/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayatallah Elakhras, Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.JoinSplitLoopCond

open StringModule

variable (T : Vector Nat 3)
variable (M : Nat)

-- Search for a fork Bool 2 that feeds an Init and a Branch
def matcher : Pattern String (String × Nat) 3 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
        unless typ.1 == "initBool" do return none

      let (.some condFork) := followInput g inst "in1" | return none
      unless condFork.typ.1 == "fork2" do return none

      -- Make sure that the input of the fork is not a split; otherwise, the matcher will apply forever
      let (.some genericInFork) := followInput g condFork.inst "in1" | return none

      let (.some branch) := followOutput g condFork.inst "out1" | return none
      unless "branch" == branch.typ.1 && branch.inputPort = "in2" do return none

      let (.some genericInBranch) := followInput g branch.inst "in1" | return none

      unless ¬(genericInBranch.inst == genericInFork.inst) do return none

      return ([branch.inst, inst, condFork.inst], #v[branch.typ.2, typ.2, condFork.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    d_i [type = "io"];
    c_i [type = "io"];
    o_br_t [type = "io"];
    o_br_f [type = "io"];
    o_init [type = "io"];

    branch [type = "branch", arg = $(T[0])];
    condFork [type = "fork2", arg = $(T[1])];
    init [type = "initBool", arg = $(T[2])];

    c_i -> condFork [to="in1"];
    d_i -> branch [to="in1"];
    condFork -> branch [from="out1", to="in2"];
    condFork -> init [from="out2", to="in1"];

    branch -> o_br_t [from = "out1"];
    branch -> o_br_f [from = "out2"];
    init -> o_init [from = "out1"];
  ]

def lhs_extract := (lhs T).extract ["branch", "init", "condFork"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    d_i [type = "io"];
    c_i [type = "io"];
    o_br_t [type = "io"];
    o_br_f [type = "io"];
    o_init [type = "io"];

    branch [type = "branch", arg = $(M+1)];
    condFork [type = "fork2", arg = $(M+2)];
    init [type = "initBool", arg = $(M+3)];
    join [type = "join", arg = $(M+4)];
    split [type = "split", arg = $(M+5)];

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

def rhs_extract := (rhs M).extract ["branch", "condFork", "init", "join", "split"] |>.get rfl

def rhsLower := (rhs M).lower.get rfl

def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 3
    pattern := matcher,
    rewrite := λ l n => ⟨ lhsLower l, rhsLower n ⟩
    name := .some "join-split-loop-cond"
    transformedNodes := [findRhs "branch", findRhs "init", findRhs "condFork"]
    addedNodes := [findRhs "join" |>.get rfl, findRhs "split" |>.get rfl]
    fresh_types := 5
  }

end Graphiti.JoinSplitLoopCond
