/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.CombineMux

open StringModule

local instance : MonadExcept IO.Error RewriteResult where
  throw e := throw <| .error <| toString e
  tryCatch m h := throw (.error "Cannot catch IO.Error")

-- Return any 2 Muxes fed by the same fork if the fork has the init as a predecessor (directly or through a tree of forks)
-- TODO: Currently, it assumes that the init is either the direct predecessor or is a predecessor of the predecessor. We should make it more general to accommodate any number of forks until the init

def findUpperForkInput (g : ExprHigh String (String × Nat)) (nn : NextNode String (String × Nat)) : Nat → RewriteResultSL (NextNode String (String × Nat))
| 0 => MonadExceptOf.throw <| RewriteError.error s!"{decl_name%}: max depth reached"
| n+1 => do
  let (.some nextFork) := followInput g nn.inst "in1" | MonadExceptOf.throw <| RewriteError.error s!"{decl_name%}: could not follow input"
  if "fork2" == nextFork.typ.1 then
    findUpperForkInput g nextFork n
  else
    return nextFork

def matcher : Pattern String (String × Nat) 3 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ.1 = "fork2" do return none

      let upperForkInput ← findUpperForkInput g {(default : NextNode String (String × Nat)) with inst := inst} 1000
      unless upperForkInput.typ.1 == "initBool" do return none

      let (.some mux_nn) := followOutput g inst "out1" | return none
      let (.some mux_nn') := followOutput g inst "out2" | return none

      unless "mux" == mux_nn.typ.1 && mux_nn.inputPort = "in1" do return none
      unless "mux" == mux_nn'.typ.1 && mux_nn'.inputPort = "in1" do return none
      return some ([mux_nn.inst, mux_nn'.inst, inst], #v[mux_nn.typ.2, mux_nn'.typ.2, typ.2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

variable (T : Vector Nat 3)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    b1_t_i [type = "io"];
    b1_f_i [type = "io"];
    b2_t_i [type = "io"];
    b2_f_i [type = "io"];
    cond_i [type = "io"];
    b1_o [type = "io"];
    b2_o [type = "io"];

    mux1 [type = "mux", arg = $(T[0])];
    mux2 [type = "mux", arg = $(T[1])];
    condFork [type = "fork2", arg = $(T[2])];

    mux1 -> b1_o [from="out1"];
    mux2 -> b2_o [from="out1"];

    cond_i -> condFork [to="in1"];
    b1_t_i -> mux1 [to="in2"];
    b1_f_i -> mux1 [to="in3"];
    b2_t_i -> mux2 [to="in2"];
    b2_f_i -> mux2 [to="in3"];

    condFork -> mux1 [from="out1", to="in1"];
    condFork -> mux2 [from="out2", to="in1"];
  ]

def lhs_extract T := (lhs T).extract ["mux1", "mux2", "condFork"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract T |>.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    b1_t_i [type = "io"];
    b1_f_i [type = "io"];
    b2_t_i [type = "io"];
    b2_f_i [type = "io"];
    cond_i [type = "io"];
    b1_o [type = "io"];
    b2_o [type = "io"];

    joinT [type = "join", arg = $(M+1)];
    joinF [type = "join", arg = $(M+2)];
    mux [type = "mux", arg = $(M+3)];
    split [type = "split", arg = $(M+4)];

    b1_t_i -> joinT [to="in1"];
    b2_t_i -> joinT [to="in2"];
    b1_f_i -> joinF [to="in1"];
    b2_f_i -> joinF [to="in2"];

    cond_i -> mux [to="in1"];

    joinT -> mux [from="out1", to="in2"];
    joinF -> mux [from="out1", to="in3"];
    mux -> split [from="out1", to="in1"];

    split -> b1_o [from="out1"];
    split -> b2_o [from="out2"];
  ]

def rhs_extract := (rhs M).extract ["mux", "joinT", "joinF", "split"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 3
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := .some "combine-mux"
    transformedNodes := [findRhs "mux", .none, .none]
    addedNodes := [ findRhs "joinT" |>.get rfl, findRhs "joinF" |>.get rfl
                  , findRhs "split" |>.get rfl
                  ]
    fresh_types := 4
  }

end Graphiti.CombineMux
