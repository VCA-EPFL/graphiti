/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.OoOAdd

def matcher (g : ExprHigh String) : RewriteResult (List String) := sorry

def lhs : ExprHigh String := sorry

def lhs_extract := lhs.extract ["join", "joinL"] |>.get sorry

theorem double_check_empty_snd : lhs_extract.snd = ExprHigh.mk ∅ ∅ := by sorry

def lhsLower := lhs_extract.fst.lower.get sorry

def rhs : ExprHigh String := sorry

def rhsLower := rhs.lower.get sorry

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

end Graphiti.OoOAdd
