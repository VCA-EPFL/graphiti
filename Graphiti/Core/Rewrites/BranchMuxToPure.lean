/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.BranchMuxToPure

open StringModule

variable (T : Vector Nat 5)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 5 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s branch_inst (pmap, branch_typ) => do
       if s.isSome then return s

       -- Find the branch
       unless "branch" == branch_typ.1 do return none

       -- Check that the next node is the pure node that also connects to the mux.
       let (.some pure1) := followOutput g branch_inst "out1" | return none
       unless "pure" == pure1.typ.1 && pure1.incomingPort = "in1" do return none

       let (.some mux) := followOutput g pure1.inst "out1" | return none
       unless "mux" == mux.typ.1 && mux.incomingPort = "in3" do return none

       -- Check that the next node is the pure node that also connects to the mux.
       let (.some pure2) := followOutput g branch_inst "out2" | return none
       unless "pure" == pure2.typ.1 && pure2.incomingPort = "in1" do return none

       let (.some mux') := followOutput g pure2.inst "out1" | return none
       unless "mux" == mux'.typ.1 && mux'.incomingPort = "in2" && mux.inst = mux'.inst do return none

       -- -- Follow the fork to the mux
       let (.some fork) := followInput g branch_inst "in2" | return none
       unless "fork2" == fork.typ.1 && fork.incomingPort == "out1" do return none

       let (.some mux'') := followOutput g fork.inst "out2" | return none
       unless mux''.inst = mux.inst && mux''.incomingPort == "in1" do return none

       return some ([branch_inst, mux.inst, fork.inst, pure1.inst, pure2.inst], #v[branch_typ.2, mux.typ.2, fork.typ.2, pure1.typ.2, pure2.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    o1 [type = "io"];

    branch [type = "branch", arg = $(T[0])];
    mux [type = "mux", arg = $(T[1])];
    fork [type = "fork2", arg = $(T[2])];
    pure1 [type = "pure", arg = $(T[3])];
    pure2 [type = "pure", arg = $(T[4])];

    i1 -> fork [to="in1"];
    i2 -> branch [to="in1"];

    fork -> branch [from="out1",to="in2"];
    fork -> mux [from="out2",to="in1"];
    branch -> pure1 [from="out1",to="in1"];
    pure1 -> mux [from="out1",to="in3"];
    branch -> pure2 [from="out2",to="in1"];
    pure2 -> mux [from="out1",to="in2"];

    mux -> o1 [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["branch", "mux", "fork", "pure1", "pure2"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    o1 [type = "io"];

    join [type = "join", arg = $(M+1)];
    pure [type = "pure", arg = $(M+2)];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];

    pure -> o1 [from="out1"];

    join -> pure [from="out1", to="in1"];
  ]

def rhs_extract := (rhs M).extract ["join", "pure"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 5
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "branch-mux-to-pure"
    transformedNodes := [.none, .none, .none, .none, .none]
    addedNodes := [findRhs "join" |>.get rfl, findRhs "pure" |>.get rfl]
    fresh_types := 2
  }

namespace Test

/-- info: true -/
#guard_msgs in
#eval matcher (lhs #v[1, 2, 3, 4, 5]) == .ok (["branch", "mux", "fork", "pure1", "pure2"], #v[1, 2, 3, 4, 5])

end Test

end Graphiti.BranchMuxToPure
