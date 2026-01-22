/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Rewriter
public meta import Graphiti.Core.Rewriter
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Dataflow.Component

@[expose] public section

namespace Graphiti.BranchPureMuxLeft

open StringModule

/--
Matches a region that needs to be converted to a pure on the left hand side of a branch/mux pair that is not empty.
Additionally, it checks that none of the nodes between the branch/mux pair includes another branch.  It does not return
any types.  The assumption is that `out1` from the fork feeds the `in2` of the branch, and `out2` feeds the mux.
-/
def matchAllNodes : Pattern String (String × Nat) 0 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s branch_inst (pmap, branch_typ) => do
       if s.isSome then return s

       -- Find the branch
       unless "branch" == branch_typ.1 do return none

       -- Check that the next node is not a mux
       let (.some nn) := followOutput g branch_inst "out1" | return none
       if "mux" == nn.typ.1 then return none

       -- Follow the fork to the mux
       let (.some fork) := followInput g branch_inst "in2" | return none
       unless "fork2" == fork.typ.1 && fork.incomingPort == "out1" do return none

       let (.some mux) := followOutput g fork.inst "out2" | return none
       unless "mux" == mux.typ.1 && mux.incomingPort == "in1" do return none

       let (.some pp) := followInput g mux.inst "in3" | return none
       if pp.inst == nn.inst then return none

       -- Gather all nodes between
       let .some nodes := findClosedRegion g nn.inst pp.inst | return none

       -- Check if there are any additional branches and muxes in the region
       unless nodes.all (λ x =>
         match g.modules.find? x with
         | .some (_, typ) => !"branch" == typ.1 && !"mux" == typ.1
         | .none => false
       )
       do return none

       return some ([branch_inst, mux.inst, fork.inst, nn.inst, pp.inst] ++ (nodes.erase nn.inst |>.erase pp.inst), #v[])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

/--
Only return the first and last instances of the region.
-/
def matchPreAndPost : Pattern String (String × Nat) 0 := fun g => do
  let (l, _) ← matchAllNodes g
  let .some n := l[3]? | throw (.error s!"{decl_name%}: could not find n")
  let .some p := l[4]? | throw (.error s!"{decl_name%}: could not find p")
  return ([n, p], #v[])

def matcherEmpty : Pattern String (String × Nat) 3 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s branch_inst (pmap, branch_typ) => do
       if s.isSome then return s

       -- Find the branch
       unless "branch" == branch_typ.1 do return none

       -- Check that the next node is the mux node (which also connects to the same fork).
       let (.some mux) := followOutput g branch_inst "out1" | return none
       unless "mux" == mux.typ.1 && mux.incomingPort = "in3" do return none

       -- Follow the fork to the mux
       let (.some fork) := followInput g branch_inst "in2" | return none
       unless "fork2" == fork.typ.1 && fork.incomingPort == "out1" do return none

       let (.some mux') := followOutput g fork.inst "out2" | return none
       unless mux'.inst == mux.inst && mux'.incomingPort == "in1" do return none

       return some ([branch_inst, mux.inst, fork.inst], #v[branch_typ.2, mux.typ.2, fork.typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

variable (T : Vector Nat 3)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    branch [type = "branch", arg = $(T[0])];
    mux [type = "mux", arg = $(T[1])];
    fork [type = "fork2", arg = $(T[2])];

    i1 -> fork [to="in1"];
    i2 -> branch [to="in1"];
    i3 -> mux [to="in2"];

    fork -> branch [from="out1",to="in2"];
    fork -> mux [from="out2",to="in1"];
    branch -> mux [from="out1",to="in3"];

    branch -> o1 [from="out2"];
    mux -> o2 [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["branch", "mux", "fork"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    branch [type = "branch", arg = $(M+1)];
    mux [type = "mux", arg = $(M+2)];
    fork [type = "fork2", arg = $(M+3)];
    pure [type = "pure", arg = $(M+4)];

    i1 -> fork [to="in1"];
    i2 -> branch [to="in1"];
    i3 -> mux [to="in2"];

    fork -> branch [from="out1",to="in2"];
    fork -> mux [from="out2",to="in1"];
    branch -> pure [from="out1",to="in1"];
    pure -> mux [from="out1",to="in3"];

    branch -> o1 [from="out2"];
    mux -> o2 [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["branch", "mux", "fork", "pure"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 3
    pattern := matcherEmpty,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := "branch-pure-mux-left"
    transformedNodes := [findRhs "branch" |>.get rfl, findRhs "mux" |>.get rfl, findRhs "fork" |>.get rfl]
    addedNodes := [findRhs "pure" |>.get rfl]
    fresh_types := 4
  }

namespace Test

/-- info: true -/
#guard_msgs in
#eval (matcherEmpty (lhs #v[1, 2, 3])) == .ok (["branch", "mux", "fork"], #v[1, 2, 3])

def rhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    branch [type = "branch", arg = $(1)];
    mux [type = "mux", arg = $(2)];
    fork [type = "fork2", arg = $(3)];
    pure [type = "pure", arg = $(4)];
    pure2 [type = "pure", arg = $(5)];

    i1 -> fork [to="in1"];
    i2 -> branch [to="in1"];
    i3 -> mux [to="in2"];

    fork -> branch [from="out1",to="in2"];
    fork -> mux [from="out2",to="in1"];
    branch -> pure [from="out1",to="in1"];
    pure -> pure2 [from="out1",to="in1"];
    pure2 -> mux [from="out1",to="in3"];

    branch -> o1 [from="out2"];
    mux -> o2 [from="out1"];
  ]

/-- info: Except.ok true -/
#guard_msgs in
#eval (matchAllNodes rhs).map (·.1 == ["branch", "mux", "fork", "pure", "pure2"])

/-- info: Except.ok true -/
#guard_msgs in
#eval (matchPreAndPost rhs).map (·.1 == ["pure", "pure2"])

end Test

end Graphiti.BranchPureMuxLeft
