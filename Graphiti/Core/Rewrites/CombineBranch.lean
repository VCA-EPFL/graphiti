/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.CombineBranch

open StringModule

-- Apply the rewrite only if the 2 Branches feed a a Join at one of their outputs
-- indicating that they are feeding a Mux that was combined.
-- Additionally, accept Branches that feed a Split at one of their outputs because
-- this is an indication that the combineBranches rewrite has been already applied
-- to them and we need to apply it one more time including an uncombined Branch.
def matcher : Pattern String (String × Nat) 3 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s

      unless typ.1 == "fork2" do return none
      let (.some branch_nn) := followOutput g inst "out1" | return none

      let (.some branch_nn') := followOutput g inst "out2" | return none

      unless "branch" == branch_nn.typ.1 && branch_nn.inputPort = "in2" do return none
      unless "branch" == branch_nn'.typ.1 && branch_nn'.inputPort = "in2" do return none

      return ([branch_nn.inst, branch_nn'.inst, inst], #v[branch_nn.typ.2, branch_nn'.typ.2, typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

variable (T : Vector Nat 3)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    b1_t_o [type = "io"];
    b1_f_o [type = "io"];
    b2_t_o [type = "io"];
    b2_f_o [type = "io"];
    cond_i [type = "io"];
    b1_i [type = "io"];
    b2_i [type = "io"];

    branch1 [type = "branch", arg = $(T[0])];
    branch2 [type = "branch", arg = $(T[1])];
    condFork [type = "fork2", arg = $(T[2])];

    branch1 -> b1_t_o [from = "out1"];
    branch1 -> b1_f_o [from = "out2"];
    branch2 -> b2_t_o [from = "out1"];
    branch2 -> b2_f_o [from = "out2"];

    cond_i -> condFork [to = "in1"];
    b1_i -> branch1 [to = "in1"];
    b2_i -> branch2 [to = "in1"];

    condFork -> branch1 [from = "out1", to = "in2"];
    condFork -> branch2 [from = "out2", to = "in2"];
  ]

def lhs_extract T := (lhs T).extract ["branch1", "branch2", "condFork"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    b1_t_o [type = "io"];
    b1_f_o [type = "io"];
    b2_t_o [type = "io"];
    b2_f_o [type = "io"];
    cond_i [type = "io"];
    b1_i [type = "io"];
    b2_i [type = "io"];

    join [type = "join", arg = $(M+1)];
    branch [type = "branch", arg = $(M+2)];
    splitT [type = "split", arg = $(M+3)];
    splitF [type = "split", arg = $(M+4)];

    b1_i -> join [to = "in1"];
    b2_i -> join [to = "in2"];
    cond_i -> branch [to = "in2"];

    splitT -> b1_t_o [from = "out1"];
    splitT -> b2_t_o [from = "out2"];
    splitF -> b1_f_o [from = "out1"];
    splitF -> b2_f_o [from = "out2"];

    join -> branch [from = "out1", to = "in1"];
    branch -> splitT [from = "out1", to = "in1"];
    branch -> splitF [from = "out2", to = "in1"];
  ]

def rhs_extract := (rhs M).extract ["branch", "join", "splitT", "splitF"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 3
    pattern := matcher,
    rewrite := λ l n => ⟨ lhsLower l, rhsLower n ⟩
    name := .some "combine-branch"
    transformedNodes := [findRhs "branch", .none, .none]
    addedNodes := [ findRhs "join" |>.get rfl
                  , findRhs "splitT" |>.get rfl, findRhs "splitF" |>.get rfl
                  ]
    fresh_types := 4
  }

end Graphiti.CombineBranch
