/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.BranchMuxToPure

open StringModule

variable (T₁ T₂ : Type)
variable (f g : T₁ → T₂)
variable (h : Bool × T₁ → T₂)
variable (S₁ S₂ : String)

def matcher : Pattern String String := fun g => do
  let (.some list) ← g.modules.foldlM (λ s branch_inst (pmap, branch_typ) => do
       if s.isSome then return s

       -- Find the branch
       unless "branch".isPrefixOf branch_typ do return none

       -- Check that the next node is the pure node that also connects to the mux.
       let (.some pure1) := followOutput g branch_inst "out1" | return none
       unless "pure".isPrefixOf pure1.typ && pure1.incomingPort = "in1" do return none

       let (.some mux) := followOutput g pure1.inst "out1" | return none
       unless "mux".isPrefixOf mux.typ && mux.incomingPort = "in3" do return none

       -- Check that the next node is the pure node that also connects to the mux.
       let (.some pure2) := followOutput g branch_inst "out2" | return none
       unless "pure".isPrefixOf pure2.typ && pure2.incomingPort = "in1" do return none

       let (.some mux') := followOutput g pure2.inst "out1" | return none
       unless "mux".isPrefixOf mux'.typ && mux'.incomingPort = "in2" && mux.inst = mux'.inst do return none

       -- Follow the fork to the mux
       let (.some fork) := followInput g branch_inst "in2" | return none
       unless "fork".isPrefixOf fork.typ && fork.incomingPort == "out1" do return none

       let (.some mux'') := followOutput g fork.inst "out2" | return none
       unless mux''.inst = mux.inst && mux''.incomingPort == "in1" do return none

       let (.some t1) := branch_typ.splitOn |>.get? 1 | return none
       let (.some t2) := mux.typ.splitOn |>.get? 1 | return none

       return some ([branch_inst, mux.inst, fork.inst, pure1.inst, pure2.inst], [t1, t2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o1 [type = "io"];

    branch [typeImp = $(⟨_, branch T₁⟩), type = $(s!"branch {S₁}")];
    mux [typeImp = $(⟨_, mux T₂⟩), type = $(s!"mux {S₂}")];
    fork [typeImp = $(⟨_, fork Bool 2⟩), type = $(s!"fork Bool 2")];
    pure1 [typeImp = $(⟨_, pure f⟩), type = $(s!"pure {S₁} {S₂}")];
    pure2 [typeImp = $(⟨_, pure g⟩), type = $(s!"pure {S₁} {S₂}")];

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

def lhs_extract := (lhs Unit Unit (λ _ => default) (λ _ => default) S₁ S₂).fst.extract ["branch", "mux", "fork", "pure1", "pure2"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁ S₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁ S₂).fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o1 [type = "io"];

    join [typeImp = $(⟨_, join Bool T₁⟩), type = $(s!"join Bool {S₁}")];
    pure [typeImp = $(⟨_, pure h⟩), type = $(s!"pure (Bool×{S₁}) {S₂}")];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];

    pure -> o1 [from="out1"];

    join -> pure [from="out1", to="in1"];
  ]

def rhs_extract := (rhs Unit Unit (λ _ => default) S₁ S₂).fst.extract ["join", "pure"] |>.get rfl

def rhsLower := (rhs_extract S₁ S₂).fst.lower.get rfl

def findRhs mod := (rhs_extract "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂] => .some ⟨lhsLower S₁ S₂, rhsLower S₁ S₂⟩ | _ => failure,
    name := "branch-mux-to-pure"
    transformedNodes := [.none, .none, .none, .none, .none]
    addedNodes := [findRhs "join" |>.get rfl, findRhs "pure" |>.get rfl]
  }

namespace Test

/-- info: true -/
#guard_msgs in
#eval (matcher (lhs_extract "T" "G").1 |>.run' default) == some (["branch", "mux", "fork", "pure1", "pure2"], ["T", "G"])

end Test

end Graphiti.BranchMuxToPure
