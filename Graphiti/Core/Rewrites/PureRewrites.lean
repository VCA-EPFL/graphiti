/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

/-
This file transforms every node in a datapath into a pure module with a combination of splits and joins.  This format
can then be optimised externally by egg, and the proof can be reconstructed on the graph.

The file contains all rewrites for this purpose, as they are all relatively simple.
-/

namespace Graphiti.PureRewrites

open StringModule

namespace Constant

def extract_type (typ : String) : RewriteResult (List String) := do
  let [typName, num] := typ.splitOn | throw .done
  unless typName = "constant" do throw .done
  return [num]

def match_node := Graphiti.match_node extract_type

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) :=
  throw (.error s!"{decl_name%}: matcher not implemented")

variable (n : Nat)

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    const [typeImp = $(⟨_, constant n⟩), type = $(s!"constant {n}")];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def lhs_extract := (lhs n).fst.extract ["const"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract n).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract n |>.fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    const [typeImp = $(⟨_, pure (S := Unit) λ _ => n⟩), type = $(s!"pure Unit T")];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def findRhs mod := (rhs 0).1.modules.find? mod |>.map Prod.fst

def rhsLower := (rhs n).fst.lower.get rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ l => do
      let n' ← l.get? 0
      -- SOMEDAY: Replace this by a proper Nat parser
      let exp ← Lean.Json.Parser.num.run n' |>.toOption
      let parsed ← exp.mantissa.toNat'
      return ⟨ lhsLower parsed, rhsLower parsed ⟩
    name := .some "pure-constant"
    transformedNodes := [findRhs "const" |>.get rfl]
  }

end Constant

namespace Operator1

def extract_type (typ : String) : RewriteResult (List String) := do
  let [typName, typ1, typ2, op] := typ.splitOn | throw .done
  unless typName = "operator1" do throw .done
  return [typ1, typ2, op]

def match_node := Graphiti.match_node extract_type

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) :=
  throw (.error s!"{decl_name%}: not implemented")

variable (T₁ T : Type)
variable [Inhabited T]
variable (T₁ₛ Tₛ Op : String)

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    op [typeImp = $(⟨_, operator1 T₁ T Op⟩), type = $(s!"operator1 {T₁ₛ} {Tₛ} {Op}")];

    i -> op [to="in1"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs Unit Unit T₁ₛ Tₛ Op).fst.extract ["op"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract T₁ₛ Tₛ Op).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract T₁ₛ Tₛ Op |>.fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    op [typeImp = $(⟨_, StringModule.pure λ x => @NatModule.op1_function T _ T₁ Op x⟩),
        type = $(s!"pure {T₁ₛ} {Tₛ}")];

    i -> op [to="in1"];
    op -> o [from="out1"];
  ]

def findRhs mod := (rhs Unit Unit "" "" "").1.modules.find? mod |>.map Prod.fst

def rhsLower := (rhs Unit Unit T₁ₛ Tₛ Op).fst.lower.get rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite :=
      λ | [T1s, Ts, Ops] => .some ⟨ lhsLower T1s Ts Ops, rhsLower T1s Ts Ops ⟩
        | _ => .none
    name := .some "pure-operator1"
    transformedNodes := [findRhs "op" |>.get rfl]
  }

end Operator1

namespace Operator2

def extract_type (typ : String) : RewriteResult (List String) := do
  let [typName, typ1, typ2, typ3, op] := typ.splitOn | throw .done
  unless typName = "operator2" do throw .done
  return [typ1, typ2, typ3, op]

def match_node := Graphiti.match_node extract_type

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) :=
  throw (.error s!"{decl_name%}: not implemented")

variable (T₁ T₂ T : Type)
variable [Inhabited T]
variable (T₁ₛ T₂ₛ Tₛ Op : String)

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    op [typeImp = $(⟨_, operator2 T₁ T₂ T Op⟩), type = $(s!"operator2 {T₁ₛ} {T₂ₛ} {Tₛ} {Op}")];

    i1 -> op [to="in1"];
    i2 -> op [to="in2"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs Unit Unit Unit T₁ₛ T₂ₛ Tₛ Op).fst.extract ["op"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract T₁ₛ T₂ₛ Tₛ Op).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract T₁ₛ T₂ₛ Tₛ Op |>.fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    join [typeImp = $(⟨_, join T₁ T₂⟩), type = $(s!"join {T₁ₛ} {T₂ₛ}")];
    op [typeImp = $(⟨_, StringModule.pure λ x => @NatModule.op2_function T _ T₁ T₂ Op x.1 x.2⟩),
        type = $(s!"pure ({T₁ₛ}×{T₂ₛ}) {Tₛ}")];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];
    join -> op [from="out1", to="in1"];
    op -> o [from="out1"];
  ]

def rhs_extract := (rhs Unit Unit Unit T₁ₛ T₂ₛ Tₛ Op).fst.extract ["op", "join"] |>.get rfl

def findRhs mod := (rhs_extract "" "" "" "").1.modules.find? mod |>.map Prod.fst

def rhsLower := (rhs_extract T₁ₛ T₂ₛ Tₛ Op).fst.lower.get rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite :=
      λ | [T1s, T2s, Ts, Ops] => .some ⟨ lhsLower T1s T2s Ts Ops, rhsLower T1s T2s Ts Ops ⟩
        | _ => .none
    name := .some "pure-operator2"
    transformedNodes := [findRhs "op" |>.get rfl]
    addedNodes := [findRhs "join" |>.get rfl]
  }

end Operator2

namespace Operator3

def extract_type (typ : String) : RewriteResult (List String) := do
  let [typName, typ1, typ2, typ3, typ4, op] := typ.splitOn | throw .done
  unless typName = "operator3" do throw .done
  return [typ1, typ2, typ3, typ4, op]

def match_node := Graphiti.match_node extract_type

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) :=
  throw (.error s!"{decl_name%}: not implemented")

variable (T₁ T₂ T₃ T : Type)
variable [Inhabited T]
variable (T₁ₛ T₂ₛ T₃ₛ Tₛ Op : String)

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o [type = "io"];

    op [typeImp = $(⟨_, operator3 T₁ T₂ T₃ T Op⟩), type = $(s!"operator3 {T₁ₛ} {T₂ₛ} {T₃ₛ} {Tₛ} {Op}")];

    i1 -> op [to="in1"];
    i2 -> op [to="in2"];
    i3 -> op [to="in3"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs Unit Unit Unit Unit T₁ₛ T₂ₛ T₃ₛ Tₛ Op).fst.extract ["op"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract T₁ₛ T₂ₛ T₃ₛ Tₛ Op).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract T₁ₛ T₂ₛ T₃ₛ Tₛ Op |>.fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o [type = "io"];

    join1 [typeImp = $(⟨_, join T₂ T₃⟩), type = $(s!"join {T₂ₛ} {T₃ₛ}")];
    join2 [typeImp = $(⟨_, join T₁ (T₂ × T₃)⟩), type = $(s!"join {T₁ₛ} ({T₂ₛ}×{T₃ₛ})")];
    op [typeImp = $(⟨_, StringModule.pure λ (x : T₁ × T₂ × T₃) => @NatModule.op3_function T _ T₁ T₂ T₃ Op x.1 x.2.1 x.2.2⟩),
        type = $(s!"pure ({T₁ₛ}×({T₂ₛ}×{T₃ₛ})) {Tₛ}")];

    i1 -> join2 [to="in1"];
    i2 -> join1 [to="in1"];
    i3 -> join1 [to="in2"];

    join1 -> join2 [from="out1",to="in2"];
    join2 -> op [from="out1", to="in1"];

    op -> o [from="out1"];
  ]

def rhs_extract := (rhs Unit Unit Unit Unit T₁ₛ T₂ₛ T₃ₛ Tₛ Op).fst.extract ["op", "join1", "join2"] |>.get rfl

def findRhs mod := (rhs_extract "" "" "" "" "").1.modules.find? mod |>.map Prod.fst

def rhsLower := (rhs_extract T₁ₛ T₂ₛ T₃ₛ Tₛ Op).fst.lower.get rfl

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite :=
      λ | [T1s, T2s, T3s, Ts, Ops] => .some ⟨ lhsLower T1s T2s T3s Ts Ops, rhsLower T1s T2s T3s Ts Ops ⟩
        | _ => .none
    name := .some "pure-operator3"
    transformedNodes := [findRhs "op" |>.get rfl]
    addedNodes := [findRhs "join1" |>.get rfl, findRhs "join2" |>.get rfl]
  }

end Operator3

namespace Fork

def extract_type (typ : String) : RewriteResult (List String) := do
  let [typName, typ, num] := typ.splitOn | throw .done
  unless typName = "fork" do throw .done
  unless num = "2" do throw .done
  return [typ]

def match_node := Graphiti.match_node extract_type

def matcher (g : ExprHigh String String) : RewriteResult (List String × List String) :=
  throw (.error s!"{decl_name%}: not implemented")

variable (T : Type)
variable [Inhabited T]
variable (Tₛ : String)

def lhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    fork [typeImp = $(⟨_, fork T 2⟩), type = $(s!"fork {Tₛ} 2")];

    i -> fork [to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
  ]

def lhs_extract := (lhs Unit Tₛ).fst.extract ["fork"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract Tₛ).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract Tₛ |>.fst.lower.get rfl

def rhs : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    op [typeImp = $(⟨_, StringModule.pure λ (x : T) => (x, x)⟩),
        type = $(s!"pure {Tₛ} ({Tₛ}×{Tₛ})")];
    split [typeImp = $(⟨_, split T T⟩), type = $(s!"split {Tₛ} {Tₛ}")];

    i -> op [to="in1"];
    op -> split [from="out1",to="in1"];
    split -> o1 [from="out1"];
    split -> o2 [from="out2"];
  ]

def rhs_extract := (rhs Unit Tₛ).fst.extract ["op", "split"] |>.get rfl

def rhsLower := (rhs_extract Tₛ).fst.lower.get rfl

def findRhs mod := (rhs_extract "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String String :=
  { abstractions := [],
    pattern := matcher,
    rewrite :=
      λ | [Ts] => .some ⟨ lhsLower Ts, rhsLower Ts ⟩
        | _ => .none
    name := .some "pure-fork"
    transformedNodes := [.none]
    addedNodes := [findRhs "op" |>.get rfl, findRhs "split" |>.get rfl]
  }

end Fork

-- TODO: do not pass the pattern, instead just precompute the pattern.
def specialisedPureRewrites (p : Pattern String String) :=
  [ { Constant.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          Constant.match_node s g
    }
  , { Operator1.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          Operator1.match_node s g
    }
  , { Operator2.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          Operator2.match_node s g
    }
  , { Operator3.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          Operator3.match_node s g
    }
  , { Fork.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          Fork.match_node s g
    }
  ]

def singleNodePureRewrites (s : String) :=
  [ {Constant.rewrite with pattern := Constant.match_node s }
  , {Operator1.rewrite with pattern := Operator1.match_node s }
  , {Operator2.rewrite with pattern := Operator2.match_node s }
  , {Operator3.rewrite with pattern := Operator3.match_node s }
  , {Fork.rewrite with pattern := Fork.match_node s }
  ]

def chainPureRewrites (l : List String) :=
  l.flatMap singleNodePureRewrites

end Graphiti.PureRewrites
