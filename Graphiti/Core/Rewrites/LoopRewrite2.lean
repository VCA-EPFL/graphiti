/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.LoopRewrite2

open StringModule

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless typ = "init Bool false" do return none

       let (.some mux) := followOutput g inst "out1" | return none
       unless String.isPrefixOf "mux" mux.typ do return none

       let (.some mod) := followOutput g mux.inst "out1" | return none
       unless "pure".isPrefixOf mod.typ do return none

       let (.some tag_split) := followOutput g mod.inst "out1" | return none
       unless String.isPrefixOf "split" tag_split.typ do return none

       let (.some condition_fork) := followOutput g tag_split.inst "out2" | return none
       unless String.isPrefixOf "fork" condition_fork.typ do return none

       let (.some branch) := followOutput g tag_split.inst "out1" | return none
       unless String.isPrefixOf "branch" branch.typ do return none

       return some ([mux.inst, condition_fork.inst, branch.inst, tag_split.inst, mod.inst, inst], [extractType mux.typ])

    ) none | MonadExceptOf.throw RewriteError.done
  return list

variable (T : Type)
variable (Tₛ : String)
variable (f : T → T × Bool)

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [typeImp = $(⟨_, mux T⟩), type = $(s!"mux {Tₛ}")];
    condition_fork [typeImp = $(⟨_, fork Bool 2 ⟩), type = "fork Bool 2"];
    branch [typeImp = $(⟨_, branch T⟩), type = $(s!"branch {Tₛ}")];
    tag_split [typeImp = $(⟨_, split T Bool⟩), type = $(s!"split {Tₛ} Bool")];
    mod [typeImp = $(⟨_, pure f⟩), type = $(s!"pure {Tₛ} ({Tₛ}×Bool)")];
    loop_init [typeImp = $(⟨_, init Bool false⟩), type = "init Bool false"];

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

def lhs_extract := lhs Unit Tₛ (λ _ => default) |>.1
  |>.extract ["mux", "condition_fork", "branch", "tag_split", "mod", "loop_init"]
  |>.get rfl

theorem double_check_empty_snd : (lhs_extract Tₛ).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract Tₛ).fst.lower.get rfl

abbrev TagT := Nat

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [typeImp = $(⟨_, tagger_untagger_val TagT T T ⟩), type = $(s!"tagger_untagger_val TagT {Tₛ} {Tₛ}")];
    merge [typeImp = $(⟨_, merge (TagT × T) 2⟩), type = $(s!"merge (TagT×{Tₛ}) 2")];
    branch [typeImp = $(⟨_, branch (TagT × T)⟩), type = $(s!"branch (TagT×{Tₛ})")];
    tag_split [typeImp = $(⟨_, split (TagT × T) Bool⟩), type = $(s!"split (TagT×{Tₛ}) Bool")];
    split_tag [typeImp = $(⟨_, split TagT T⟩), type = $(s!"split TagT {Tₛ}")];
    split_bool [typeImp = $(⟨_, split T Bool⟩), type = $(s!"split {Tₛ} Bool")];
    join_tag [typeImp = $(⟨_, join TagT T⟩), type = $(s!"join TagT {Tₛ}")];
    join_bool [typeImp = $(⟨_, join (TagT × T) Bool⟩), type = $(s!"join (TagT×{Tₛ}) Bool")];
    mod [typeImp = $(⟨_, pure f⟩), type = $(s!"pure {Tₛ} ({Tₛ}×Bool)")];

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

def rhsLower := (rhs Unit Tₛ (λ _ => default) |>.1).lower.get rfl

def findRhs mod := (rhs Unit "" (λ _ => default)).1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { pattern := matcher,
    rewrite := λ | [T] => pure ⟨lhsLower T, rhsLower T⟩ | _ => failure
    name := .some "loop-rewrite"
    transformedNodes := [ findRhs "merge" |>.get rfl, .none, findRhs "branch" |>.get rfl
                        , findRhs "tag_split" |>.get rfl, findRhs "mod" |>.get rfl, .none]
    addedNodes := [ findRhs "tagger" |>.get rfl, findRhs "split_tag" |>.get rfl, findRhs "split_bool" |>.get rfl
                  , findRhs "join_tag" |>.get rfl, findRhs "join_bool" |>.get rfl]
  }

end Graphiti.LoopRewrite2
