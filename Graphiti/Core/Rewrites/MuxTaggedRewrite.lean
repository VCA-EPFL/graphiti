/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martina Camaioni
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.MuxTaggedRewrite

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := sorry

@[drunfold_defs] def lhs' : ExprHigh String String := [graph|
    i_t [type = "io"];
    i_f [type = "io"];
    i_c [type = "io"];
    i_tag [type = "io"];
    o_out [type = "io"];

    mux [type = "mux"];
    join [type = "join"];

    i_t -> mux [to = "in1"];
    i_f -> mux [to = "in2"];
    i_c -> mux [to = "in3"];

    i_tag -> join [to = "in1"];

    mux -> join [from = "out1", to = "in2"];

    join -> o_out [from = "out1"];
  ]

@[drunfold_defs] def lhs := lhs'.extract ["mux", "join"] |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

@[drunfold_defs] def lhsLower := lhs.fst.lower.get rfl

@[drunfold_defs] def rhs : ExprHigh String String := [graph|
    i_t [type = "io"];
    i_f [type = "io"];
    i_c [type = "io"];
    i_tag [type = "io"];
    o_out [type = "io"];

    mux [type = "tagged_mux"];
    join_t [type = "join"];
    join_f [type = "join"];
    fork [type = "fork"];
    branch [type = "branch"];

    i_c -> fork [to = "in1"];

    fork -> branch [from = "out1", to = "cond"];
    i_tag -> branch [to = "val"];

    branch -> join_t [from = "true", to = "in1"];
    i_t -> join_t [to = "in2"];

    branch -> join_f [from = "false", to = "in1"];
    i_f -> join_f [to = "in2"];

    join_t -> mux [from = "out1", to = "in1"];
    join_f -> mux [from = "out1", to = "in2"];
    fork -> mux [from = "out2", to = "in3"];

    mux -> o_out [from = "out1"];
  ]

@[drunfold_defs] def rhs_extract := rhs.extract ["mux", "join_f", "join_t", "fork", "branch"] |>.get rfl

@[drunfold_defs] def rhsLower := rhs.lower.get rfl

@[drunfold_defs] def rewrite : Rewrite String String :=
  { pattern := matcher,
    rewrite := fun _ => some ⟨lhsLower, rhsLower⟩
  }

end Graphiti.MuxTaggedRewrite
