/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.LoadRewrite

open StringModule

variable (T : Type)
variable [Inhabited T]
variable (Op : String)

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless typ = "load T T" do return none

       let (.some mc) := followOutput g inst "out2" | return none
       unless String.isPrefixOf "operator1" mc.typ do return none

       let (.some load) := followOutput g mc.inst "out1" | return none
       unless load.inst = inst do return none

       let (.some op) := mc.typ.splitOn |>.get? 3 | return none

       return some ([inst, mc.inst], [op])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    load [typeImp = $(⟨_, load T T⟩), type = $("load T T")];
    mc [typeImp = $(⟨_, operator1 T T Op⟩), type = $(s!"operator1 T T {Op}")];

    i_in -> load [to = "in2"];
    load -> o_out [from = "out1"];

    load -> mc [from = "out2", to = "in1"];
    mc -> load [from = "out1", to = "in1"];
  ]

def lhs_extract := (lhs Unit Op).fst.extract ["load", "mc"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract Op).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract Op).fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    pure [typeImp = $(⟨_, StringModule.pure (@NatModule.op1_function T _ T Op)⟩), type = $(s!"pure T T")];

    i_in -> pure [to = "in1"];
    pure -> o_out [from = "out1"];
  ]

def rhs_extract := (rhs Unit Op).fst.extract ["pure"] |>.get rfl

def rhsLower := (rhs_extract Op).fst.lower.get rfl

def findRhs mod := (rhs_extract "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [Op] => .some ⟨lhsLower Op, rhsLower Op⟩ | _ => failure
    name := "load-rewrite"
    transformedNodes := [.none, .none]
    addedNodes := [findRhs "pure" |>.get rfl]
  }

end Graphiti.LoadRewrite
