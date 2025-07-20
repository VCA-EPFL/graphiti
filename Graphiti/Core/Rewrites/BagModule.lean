/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Rewriter
import Graphiti.ExprHighElaborator

namespace Graphiti.BagModule

local instance : MonadExcept IO.Error RewriteResult where
  throw e := throw <| .error <| toString e
  tryCatch m h := throw (.error "Cannot catch IO.Error")

unsafe def oracle (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let merges ← ofExcept <| unsafeIO do
    -- Here you can run an arbitrary command with arguments, where stdout will be passed to `result`.  This can be used
    -- to implement the matcher completely externally.
    let result ← IO.Process.run { cmd := "echo", args := #["merge1, merge2, merge3"] }
    return result.trim.splitOn ", "
  return (merges, [])

/--
We can just return a constant node here because the abstraction mechanism will have already lifted the circuit into
`module`.
-/
def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  return (["module"], [])

def lhs' : ExprHigh String := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    module [type = "module"];

    i_in -> module [to = "in"];
    module -> o_out [from = "out"];
  ]

-- #eval IO.print lhs'

def lhs := lhs'.extract (matcher lhs' |>.run' default |>.get rfl |>.fst) |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl

def rhs : ExprHigh String := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [type = "TaggerCntrlAligner"];
    split [type = "TaggedSplit"];
    join [type = "TaggedJoin"];
    bag [type = "Bag"];
    module [type = "module"];

    i_in -> tagger [to = "enq_untagged"];
    tagger -> split [from = "tagged", to = "in1"];

    split -> module [from = "out2", to = "in"];
    split -> join [from = "out1", to = "in1"];
    module -> join [from = "out", to = "in2"];

    join -> bag [from = "out1", to = "in1"];
    bag -> tagger [from = "out1", to = "complete_tagged"];

    tagger -> o_out [from = "deq_untagged"];
  ]

-- #eval IO.print rhs

def rhsLower := rhs.lower.get rfl

/--
This rewrite adds abstractions to the definition, which provide patterns to
extract parts of the graph.  The `type` given to each extracted node has to
match the `type` of the node in LHS and RHS graphs.
-/
def rewrite : Rewrite String :=
  { abstractions := [⟨unsafe oracle, "module"⟩],
    pattern := matcher,
    rewrite := fun _ => pure ⟨lhsLower, rhsLower⟩,
    name := .some "bag-module"
  }

end Graphiti.BagModule
