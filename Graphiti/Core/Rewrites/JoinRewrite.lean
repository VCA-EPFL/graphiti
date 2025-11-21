/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martina Camaioni
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.JoinRewrite

open StringModule

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) := sorry

@[drunfold_defs]
def lhs (T₁ T₂ T₃ : Type) (S₁ S₂ S₃ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join1 [typeImp = $(⟨_, join T₁ T₂⟩), type = $("join " ++ S₁ ++  " " ++ S₂)];
    join2 [typeImp = $(⟨_, join (T₁ × T₂) T₃⟩), type = $("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃)];

    i_0 -> join1 [to = "in1"];
    i_1 -> join1 [to = "in2"];
    i_2 -> join2 [to = "in2"];

    join1 -> join2 [from = "out1", to = "in1"];

    join2 -> o_out [from = "out1"];
  ]

@[drunfold_defs]
def lhs_extract S₁ S₂ S₃ := (lhs Unit Unit Unit S₁ S₂ S₃).fst.extract ["join1", "join2"] |>.get rfl

theorem double_check_empty_snd S₁ S₂ S₃ : (lhs_extract S₁ S₂ S₃).snd = ExprHigh.mk ∅ ∅ := by rfl

@[drunfold_defs]
def lhsLower S₁ S₂ S₃ := (lhs_extract S₁ S₂ S₃).fst.lower_TR.get rfl

@[drunfold_defs]
def rhs (T₁ T₂ T₃ : Type) (S₁ S₂ S₃ : String) : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join1 [typeImp = $(⟨_, join T₂ T₃⟩), type = $("join " ++ S₂ ++ " " ++ S₃)];
    join2 [typeImp = $(⟨_, join T₁ (T₂ × T₃)⟩), type = $("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")")];
    pure [typeImp = $(⟨_, StringModule.pure (λ ((a, b, c) : T₁ × T₂ × T₃) => ((a, b), c))⟩),
          type = $(s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})")];

    i_1 -> join1 [to = "in1"];
    i_2 -> join1 [to = "in2"];
    i_0 -> join2 [to = "in1"];

    join1 -> join2 [from = "out1", to = "in2"];
    join2 -> pure [from = "out1", to = "in1"];

    pure -> o_out [from = "out1"];
  ]

@[drunfold_defs]
def rhs_extract S₁ S₂ S₃ := (rhs Unit Unit Unit S₁ S₂ S₃).fst.extract ["pure", "join1", "join2"] |>.get rfl

theorem double_check_empty_snd_rhs S₁ S₂ S₃ : (rhs_extract S₁ S₂ S₃).snd = ExprHigh.mk ∅ ∅ := by rfl

@[drunfold_defs]
def rhsLower S₁ S₂ S₃ := (rhs_extract S₁ S₂ S₃).fst.lower_TR.get rfl

-- @[drunfold_defs]
-- def rewrite : Rewrite String String :=
--   { abstractions := []
--     params := 2
--     pattern := matcher
--     rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
--     }

end Graphiti.JoinRewrite
