/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.LoopRewrite2

open StringModule

def matcher : Pattern String (String × Nat) 6 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless typ.1 = "initBool" do return none

       let (.some mux) := followOutput g inst "out1" | return none
       unless "mux" == mux.typ.1 do return none

       let (.some mod) := followOutput g mux.inst "out1" | return none
       unless "pure" == mod.typ.1 do return none

       let (.some tag_split) := followOutput g mod.inst "out1" | return none
       unless "split" == tag_split.typ.1 do return none

       let (.some condition_fork) := followOutput g tag_split.inst "out2" | return none
       unless "fork2" == condition_fork.typ.1 do return none

       let (.some branch) := followOutput g tag_split.inst "out1" | return none
       unless "branch" == branch.typ.1 do return none

       return some ([mux.inst, condition_fork.inst, branch.inst, tag_split.inst, mod.inst, inst], #v[mux.typ.2, condition_fork.typ.2, branch.typ.2, tag_split.typ.2, mod.typ.2, typ.2])

    ) none | MonadExceptOf.throw RewriteError.done
  return list

variable (T : Vector Nat 6)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [type = "mux", arg = $(T[0])];
    condition_fork [type = "fork2", arg = $(T[1])];
    branch [type = "branch", arg = $(T[2])];
    tag_split [type = "split", arg = $(T[3])];
    mod [type = "pure", arg = $(T[4])];
    loop_init [type = "initBool", arg = $(T[5])];

    i_in -> mux [to="in2"];
    branch -> o_out [from="out2"];

    loop_init -> mux [from="out1", to="in1"];
    condition_fork -> loop_init [from="out2", to="in1"];
    condition_fork -> branch [from="out1", to="in2"];
    mod -> tag_split [from="out1", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> condition_fork [from="out2", to="in1"];
    mux -> mod [from="out1", to="in1"];
    branch -> mux [from="out1", to="in3"];
  ]

def lhs_extract := (lhs T).extract ["mux", "condition_fork", "branch", "tag_split", "mod", "loop_init"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [type = "tag_untagger_val", arg = $(M+1)];
    merge [type = "merge", arg = $(M+2)];
    branch [type = "branch", arg = $(M+3)];
    tag_split [type = "split", arg = $(M+4)];
    split_tag [type = "split", arg = $(M+5)];
    split_bool [type = "split", arg = $(M+6)];
    join_tag [type = "join", arg = $(M+7)];
    join_bool [type = "join", arg = $(M+8)];
    mod [type = "pure", arg = $(M+9)];

    i_in -> tagger [to="in2"];
    tagger -> o_out [from="out2"];

    tagger -> merge [from="out1",to="in2"];
    merge -> split_tag [from="out1", to="in1"];
    split_tag -> mod [from="out2", to="in1"];
    mod -> split_bool [from="out1", to="in1"];
    split_bool -> join_tag [from="out1", to="in2"];
    split_tag -> join_tag [from="out1", to="in1"];
    join_tag -> join_bool [from="out1", to="in1"];
    split_bool -> join_bool [from="out2", to="in2"];
    join_bool -> tag_split [from="out1", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> branch [from="out2", to="in2"];
    branch -> merge [from="out1", to="in1"];
    branch -> tagger [from="out2", to="in1"];
  ]

def rhs_extract := (rhs M).extract ["merge", "branch", "tag_split", "mod", "tagger", "split_tag", "split_bool", "join_tag", "join_bool"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  {
    params := 6
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := .some "loop-rewrite"
    transformedNodes := [ findRhs "merge" |>.get rfl, .none, findRhs "branch" |>.get rfl
                        , findRhs "tag_split" |>.get rfl, findRhs "mod" |>.get rfl, .none]
    addedNodes := [ findRhs "tagger" |>.get rfl, findRhs "split_tag" |>.get rfl, findRhs "split_bool" |>.get rfl
                  , findRhs "join_tag" |>.get rfl, findRhs "join_bool" |>.get rfl]
    fresh_types := 9
  }

end Graphiti.LoopRewrite2
