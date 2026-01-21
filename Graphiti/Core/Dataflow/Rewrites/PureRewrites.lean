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

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "constant" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: matcher not implemented")

variable (T : Vector Nat 1)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    const [type = "constant", arg = $(T[0])];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["const"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    const [type = "pure", arg = $(M+1)];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def rhsLower := (rhs M).lower.get rfl
def findRhs mod := (rhs 0).modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := 1
  pattern := matcher
  rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
  name := .some "pure-constant"
  transformedNodes := [findRhs "const" |>.get rfl]
  fresh_types := 1

end Constant

namespace ConstantNat

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "constantNat" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: matcher not implemented")

variable (T : Vector Nat 1)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    const [type = "constantNat", arg = $(T[0])];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["const"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    const [type = "pure", arg = $(M+1)];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def rhsLower := (rhs M).lower.get rfl
def findRhs mod := (rhs 0).modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := 1
  pattern := matcher
  rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
  name := .some "pure-constant-nat"
  transformedNodes := [findRhs "const" |>.get rfl]
  fresh_types := 1

end ConstantNat

namespace ConstantBool

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "constantBool" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: matcher not implemented")

variable (T : Vector Nat 1)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    const [type = "constantBool", arg = $(T[0])];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["const"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    const [type = "pure", arg = $(M+1)];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def rhsLower := (rhs M).lower.get rfl
def findRhs mod := (rhs 0).modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := 1
  pattern := matcher
  rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
  name := .some "pure-constant-nat"
  transformedNodes := [findRhs "const" |>.get rfl]
  fresh_types := 1

end ConstantBool

namespace Operator1

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "operator1" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: not implemented")

variable (T : Vector Nat 1)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    op [type = "operator1", arg = $(T[0])];

    i -> op [to="in1"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["op"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    op [type = "pure", arg = $(M+1)];

    i -> op [to="in1"];
    op -> o [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["op"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 1
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := .some "pure-operator1"
    transformedNodes := [findRhs "op" |>.get rfl]
    fresh_types := 1
  }

end Operator1

namespace Operator2

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "operator2" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

variable (T : Vector Nat 1)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: not implemented")

def lhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    op [type = "operator2", arg = $(T[0])];

    i1 -> op [to="in1"];
    i2 -> op [to="in2"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["op"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    join [type = "join", arg = $(M+1)];
    op [type = "pure", arg = $(M+2)];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];
    join -> op [from="out1", to="in1"];
    op -> o [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["op", "join"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 1
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := .some "pure-operator2"
    transformedNodes := [findRhs "op" |>.get rfl]
    addedNodes := [findRhs "join" |>.get rfl]
    fresh_types := 2
  }

end Operator2

namespace Operator3

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "operator3" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: not implemented")

variable (T : Vector Nat 1)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o [type = "io"];

    op [type = "operator3", arg = $(T[0])];

    i1 -> op [to="in1"];
    i2 -> op [to="in2"];
    i3 -> op [to="in3"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["op"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o [type = "io"];

    join1 [type = "join", arg = $(M+1)];
    join2 [type = "join", arg = $(M+2)];
    op [type = "pure", arg = $(M+3)];

    i1 -> join2 [to="in1"];
    i2 -> join1 [to="in1"];
    i3 -> join1 [to="in2"];

    join1 -> join2 [from="out1",to="in2"];
    join2 -> op [from="out1", to="in1"];

    op -> o [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["op", "join1", "join2"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := []
    params := 1
    pattern := matcher
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := .some "pure-operator3"
    transformedNodes := [findRhs "op" |>.get rfl]
    addedNodes := [findRhs "join1" |>.get rfl, findRhs "join2" |>.get rfl]
    fresh_types := 3
  }

end Operator3

namespace CondOperator1

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "cond_operator1" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: not implemented")

variable (T : Vector Nat 1)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    op [type = "cond_operator1", arg = $(T[0])];

    i -> op [to="in1"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["op"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o [type = "io"];

    op [type = "pure", arg = $(M+1)];

    i -> op [to="in1"];
    op -> o [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["op"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 1
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := .some "pure-cond_operator1"
    transformedNodes := [findRhs "op" |>.get rfl]
    fresh_types := 1
  }

end CondOperator1

namespace CondOperator2

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "cond_operator2" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

variable (T : Vector Nat 1)
variable (M : Nat)

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: not implemented")

def lhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    op [type = "cond_operator2", arg = $(T[0])];

    i1 -> op [to="in1"];
    i2 -> op [to="in2"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs T).extract ["op"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    join [type = "join", arg = $(M+1)];
    op [type = "pure", arg = $(M+2)];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];
    join -> op [from="out1", to="in1"];
    op -> o [from="out1"];
  ]

def rhs_extract := (rhs M).extract ["op", "join"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 1
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := .some "pure-cond_operator2"
    transformedNodes := [findRhs "op" |>.get rfl]
    addedNodes := [findRhs "join" |>.get rfl]
    fresh_types := 2
  }

end CondOperator2

namespace Fork

def extract_type (typ : String × Nat) : RewriteResultSL (Vector Nat 1) := do
  unless typ.1 == "fork2" do throw .done
  return #v[typ.2]

def match_node := Graphiti.match_node extract_type

def matcher : Pattern String (String × Nat) 1 := fun g => do
  throw (.error s!"{decl_name%}: not implemented")

variable (T : Vector Nat 1)
variable (M : Nat)

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    fork [type = "fork2", arg = $(T[0])];

    i -> fork [to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
  ]

def lhs_extract := (lhs T).extract ["fork"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    op [type = "pure", arg = $(M+1)];
    split [type = "split", arg = $(M+2)];

    i -> op [to="in1"];
    op -> split [from="out1", to="in1"];
    split -> o1 [from="out1"];
    split -> o2 [from="out2"];
  ]

def rhs_extract := (rhs M).extract ["op", "split"] |>.get rfl
def rhsLower := (rhs_extract M).fst.lower.get rfl
def findRhs mod := (rhs_extract 0).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 1
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
    name := .some "pure-fork"
    transformedNodes := [.none]
    addedNodes := [findRhs "op" |>.get rfl, findRhs "split" |>.get rfl]
    fresh_types := 2
  }

end Fork

-- TODO: do not pass the pattern, instead just precompute the pattern.
def specialisedPureRewrites {n} (p : Pattern String (String × Nat) n) :=
  [ { Constant.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          Constant.match_node s g
    }
  , { ConstantNat.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          ConstantNat.match_node s g
    }
  , { ConstantBool.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          ConstantBool.match_node s g
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
  , { CondOperator1.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          CondOperator1.match_node s g
    }
  , { CondOperator2.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          CondOperator2.match_node s g
    }
  , { Fork.rewrite with
        pattern := fun g => do
          let (s :: _, t) ← p g | throw RewriteError.done
          Fork.match_node s g
    }
  ]

def singleNodePureRewrites (s : String) :=
  [ { Constant.rewrite with pattern := Constant.match_node s }
  , { ConstantNat.rewrite with pattern := ConstantNat.match_node s }
  , { ConstantBool.rewrite with pattern := ConstantBool.match_node s }
  , { Operator1.rewrite with pattern := Operator1.match_node s }
  , { Operator2.rewrite with pattern := Operator2.match_node s }
  , { Operator3.rewrite with pattern := Operator3.match_node s }
  , { CondOperator1.rewrite with pattern := Operator1.match_node s }
  , { CondOperator2.rewrite with pattern := Operator2.match_node s }
  , { Fork.rewrite with pattern := Fork.match_node s }
  ]

def chainPureRewrites (l : List String) :=
  l.flatMap singleNodePureRewrites

end Graphiti.PureRewrites
