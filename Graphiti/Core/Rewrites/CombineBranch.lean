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
def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s

      unless typ = "fork Bool 2" do return none
      let (.some branch_nn) := followOutput g inst "out1" | return none
      -- let (.some branch_nn_out_1) := followOutput g branch_nn.inst "out1" | return none
      -- let (.some branch_nn_out_2) := followOutput g branch_nn.inst "out2" | return none

      let (.some branch_nn') := followOutput g inst "out2" | return none
      -- let (.some branch_nn'_out_1) := followOutput g branch_nn'.inst "out1" | return none
      -- let (.some branch_nn'_out_2) := followOutput g branch_nn'.inst "out2" | return none

      unless String.isPrefixOf "branch" branch_nn.typ && branch_nn.inputPort = "in2" do return none
      unless String.isPrefixOf "branch" branch_nn'.typ && branch_nn'.inputPort = "in2" do return none

      -- unless String.isPrefixOf "join" branch_nn_out_1.typ || String.isPrefixOf "split" branch_nn_out_1.typ || String.isPrefixOf "join" branch_nn_out_2.typ || String.isPrefixOf "split" branch_nn_out_2.typ do return none
      -- unless String.isPrefixOf "join" branch_nn'_out_1.typ || String.isPrefixOf "split" branch_nn'_out_1.typ || String.isPrefixOf "join" branch_nn'_out_2.typ || String.isPrefixOf "split" branch_nn'_out_2.typ do return none

      return ([branch_nn.inst, branch_nn'.inst, inst], [extractType branch_nn.typ, extractType branch_nn'.typ])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs (T T' : Type) (Tₛ T'ₛ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    b1_t_o [type = "io"];
    b1_f_o [type = "io"];
    b2_t_o [type = "io"];
    b2_f_o [type = "io"];
    cond_i [type = "io"];
    b1_i [type = "io"];
    b2_i [type = "io"];

    branch1 [typeImp = $(⟨_, branch T⟩), type = $(s!"branch {Tₛ}")];
    branch2 [typeImp = $(⟨_, branch T'⟩), type = $(s!"branch {T'ₛ}")];
    condFork [typeImp = $(⟨_, fork Bool 2⟩), type = "fork Bool 2"];

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

-- #reduce lhs Unit Unit "H" "Y"

def lhs_extract T₁ T₂ := (lhs Unit Unit T₁ T₂).fst.extract ["branch1", "branch2", "condFork"] |>.get rfl

-- #eval IO.print ((lhs Unit Unit "T" "T'").fst)

theorem lhs_type_independent a b c d T₁ T₂ : (lhs a b T₁ T₂).fst = (lhs c d T₁ T₂).fst := by rfl

theorem double_check_empty_snd T₁ T₂ : (lhs_extract T₁ T₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T₁ T₂ := lhs_extract T₁ T₂ |>.fst.lower.get rfl

def rhs (T T' : Type) (Tₛ Tₛ' : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    b1_t_o [type = "io"];
    b1_f_o [type = "io"];
    b2_t_o [type = "io"];
    b2_f_o [type = "io"];
    cond_i [type = "io"];
    b1_i [type = "io"];
    b2_i [type = "io"];

    join [typeImp = $(⟨_, join T T'⟩), type = $(s!"join {Tₛ} {Tₛ'}")];
    branch [typeImp = $(⟨_, branch (T×T')⟩), type = $(s!"branch ({Tₛ}×{Tₛ'})")];
    splitT [typeImp = $(⟨_, split T T'⟩), type = $(s!"split {Tₛ} {Tₛ'}")];
    splitF [typeImp = $(⟨_, split T T'⟩), type = $(s!"split {Tₛ} {Tₛ'}")];

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

def rhsLower T₁ T₂ := (rhs Unit Unit T₁ T₂).fst.lower.get rfl

-- #eval IO.print ((rhs Unit Unit "T" "T'").fst)

theorem rhs_type_independent a b c d T₁ T₂ : (rhs a b T₁ T₂).fst = (rhs c d T₁ T₂).fst := by rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ l => do
      let T₁ ← l[0]?
      let T₂ ← l[1]?
      return ⟨ lhsLower T₁ T₂, rhsLower T₁ T₂ ⟩
    name := .some "combine-branch"
  }

end Graphiti.CombineBranch
