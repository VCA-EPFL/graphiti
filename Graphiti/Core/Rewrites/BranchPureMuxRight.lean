/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.BranchPureMuxRight

open StringModule

variable (T₁ : Type)
variable (S₁ : String)

/--
Matches a region that needs to be converted to a pure on the left hand side of a branch/mux pair that is not empty.
Additionally, it checks that none of the nodes between the branch/mux pair includes another branch.  It does not return
any types.  The assumption is that `out1` from the fork feeds the `in2` of the branch, and `out2` feeds the mux.
-/
def matchAllNodes (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s branch_inst (pmap, branch_typ) => do
       if s.isSome then return s

       -- Find the branch
       unless "branch".isPrefixOf branch_typ do return none

       -- Check that the next node is not a mux
       let (.some nn) := followOutput g branch_inst "out2" | return none
       if "mux".isPrefixOf nn.typ then return none

       -- Follow the fork to the mux
       let (.some fork) := followInput g branch_inst "in2" | return none
       unless "fork".isPrefixOf fork.typ && fork.incomingPort == "out1" do return none

       let (.some mux) := followOutput g fork.inst "out2" | return none
       unless "mux".isPrefixOf mux.typ && mux.incomingPort == "in1" do return none

       let (.some pp) := followInput g mux.inst "in2" | return none
       if pp.inst == nn.inst then return none

       -- Gather all nodes between
       let .some nodes := findClosedRegion g nn.inst pp.inst | return none

       -- Check if there are any additional branches and muxes in the region
       unless nodes.all (λ x =>
         match g.modules.find? x with
         | .some (_, typ) => !"branch".isPrefixOf typ && !"mux".isPrefixOf typ
         | .none => false
       )
       do return none

       return some ([branch_inst, mux.inst, fork.inst] ++ nodes, [])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def matcherEmpty (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s branch_inst (pmap, branch_typ) => do
       if s.isSome then return s

       -- Find the branch
       unless "branch".isPrefixOf branch_typ do return none

       -- Check that the next node is the mux node (which also connects to the same fork).
       let (.some mux) := followOutput g branch_inst "out2" | return none
       unless "mux".isPrefixOf mux.typ && mux.incomingPort = "in2" do return none

       -- Follow the fork to the mux
       let (.some fork) := followInput g branch_inst "in2" | return none
       unless "fork".isPrefixOf fork.typ && fork.incomingPort == "out1" do return none

       let (.some mux') := followOutput g fork.inst "out2" | return none
       unless mux'.inst = mux.inst && mux'.incomingPort == "in1" do return none

       return some ([branch_inst, mux.inst, fork.inst], [])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    branch [typeImp = $(⟨_, branch T₁⟩), type = $(s!"branch {S₁}")];
    mux [typeImp = $(⟨_, mux T₁⟩), type = $(s!"mux {S₁}")];
    fork [typeImp = $(⟨_, fork Bool 2⟩), type = $(s!"fork Bool 2")];

    i1 -> fork [to="in1"];
    i2 -> branch [to="in1"];
    i3 -> mux [to="in3"];

    fork -> branch [from="out1",to="in2"];
    fork -> mux [from="out2",to="in1"];
    branch -> mux [from="out2",to="in2"];

    branch -> o1 [from="out1"];
    mux -> o2 [from="out1"];
  ]

def lhs_extract := (lhs Unit S₁).fst.extract ["branch", "mux", "fork"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁).fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    branch [typeImp = $(⟨_, branch T₁⟩), type = $(s!"branch {S₁}")];
    mux [typeImp = $(⟨_, mux T₁⟩), type = $(s!"mux {S₁}")];
    fork [typeImp = $(⟨_, fork Bool 2⟩), type = $(s!"fork Bool 2")];
    pure [typeImp = $(⟨_, pure (@id T₁)⟩), type = $(s!"pure {S₁} {S₁}")];

    i1 -> fork [to="in1"];
    i2 -> branch [to="in1"];
    i3 -> mux [to="in3"];

    fork -> branch [from="out1",to="in2"];
    fork -> mux [from="out2",to="in1"];
    branch -> pure [from="out2",to="in1"];
    pure -> mux [from="out1",to="in2"];

    branch -> o1 [from="out1"];
    mux -> o2 [from="out1"];
  ]

def rhs_extract := (rhs Unit S₁).fst.extract ["branch", "mux", "fork", "pure"] |>.get rfl

def rhsLower := (rhs_extract S₁).fst.lower.get rfl

def findRhs mod := (rhs_extract "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcherEmpty,
    rewrite := λ | [S₁] => .some ⟨lhsLower S₁, rhsLower S₁⟩ | _ => failure,
    name := "pure-split-right"
    transformedNodes := [findRhs "branch" |>.get rfl, findRhs "mux" |>.get rfl, findRhs "fork" |>.get rfl]
    addedNodes := [findRhs "pure" |>.get rfl]
  }

namespace Test

/-- info: true -/
#guard_msgs in
#eval (matcherEmpty (lhs Unit "T").1 |>.run' default) == some (["branch", "mux", "fork"], [])

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    branch [typeImp = $(⟨_, branch T₁⟩), type = $(s!"branch {S₁}")];
    mux [typeImp = $(⟨_, mux T₁⟩), type = $(s!"mux {S₁}")];
    fork [typeImp = $(⟨_, fork Bool 2⟩), type = $(s!"fork Bool 2")];
    pure [typeImp = $(⟨_, pure (@id T₁)⟩), type = $(s!"pure {S₁} {S₁}")];
    pure2 [typeImp = $(⟨_, pure (@id T₁)⟩), type = $(s!"pure {S₁} {S₁}")];

    i1 -> fork [to="in1"];
    i2 -> branch [to="in1"];
    i3 -> mux [to="in3"];

    fork -> branch [from="out1",to="in2"];
    fork -> mux [from="out2",to="in1"];
    branch -> pure [from="out2",to="in1"];
    pure -> pure2 [from="out1",to="in1"];
    pure2 -> mux [from="out1",to="in2"];

    branch -> o1 [from="out1"];
    mux -> o2 [from="out1"];
  ]

/-- info: some true -/
#guard_msgs in
#eval (matchAllNodes (rhs Unit "T").1 |>.run' default).map (·.1 == ["branch", "mux", "fork", "pure", "pure2"])

end Test

end Graphiti.BranchPureMuxRight
