/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Rewriter
import Graphiti.ExprHighElaborator

namespace Graphiti.MergeRewrite

/--
The matcher takes in a dot graph and should return the cluster of nodes that
form the subgraph as a list of instance names.
-/
def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ nodes inst (pmap, typ) => do
      if nodes.isSome then return nodes
      unless typ = "Merge" do return none
      let (.some nn) := followOutput g inst "out1" | return none
      unless nn.typ = "Merge" && nn.inputPort = "in1" do return none
      return some [inst, nn.inst]
    ) none | throw .done
  return list

@[drunfold] def mergeLhs : ExprHigh String := [graph|
    out1 [type = "io"];
    in1 [type = "io"];
    in2 [type = "io"];
    in3 [type = "io"];

    merge1 [type = "Merge"];
    merge2 [type = "Merge"];

    in1 -> merge1 [to = "in1"];
    in2 -> merge1 [to = "in2"];
    in3 -> merge2 [to = "in2"];

    merge1 -> merge2 [from = "out1", to = "in1"];

    merge2 -> out1 [from = "out1"];
  ]

#eval IO.print mergeLhs

/--
To get instances in a predictable order, it's a good idea to extract the whole
graph once with the nodes in the order that you want to provide them in the
pattern-matcher.  In this case we want merge1 to be listed before merge2.
-/
def mergeLhsOrdered := mergeLhs.extract ["merge1", "merge2"] |>.get rfl

/--
Graph extraction gives back two graphs, the subgraph and the rest of the graph.
Here we just double check that the rest of the graph is empty, implying we
extracted the whole graph.  The proof of `rfl` should always work for this.
-/
theorem double_check_empty_snd : mergeLhsOrdered.snd = ExprHigh.mk ∅ ∅ := by rfl

/--
We then use the extracted graph to lower to ExprLow, which ensures the right
ordering of instances.
-/
def mergeLhsLower := mergeLhsOrdered.fst.lower.get rfl

@[drunfold] def mergeRhs : ExprHigh String := [graph|
    out1 [type = "io"];
    in1 [type = "io"];
    in2 [type = "io"];
    in3 [type = "io"];

    merge3 [type = "Merge3"];

    in1 -> merge3 [to = "in1"];
    in2 -> merge3 [to = "in2"];
    in3 -> merge3 [to = "in3"];

    merge3 -> out1 [from = "out1"];
  ]

#eval IO.print mergeRhs

def mergeRhsLower := mergeRhs.lower.get rfl

def rewrite : Rewrite String :=
  { pattern := matcher,
    input_expr := mergeLhsLower,
    output_expr := mergeRhsLower }

namespace TestRewriter

def mergeHigh : ExprHigh String :=
  [graph|
    src0 [type="io"];
    snk0 [type="io"];

    fork1 [type="Fork"];
    fork2 [type="Fork"];
    merge2 [type="Merge"];
    merge1 [type="Merge"];

    src0 -> fork1 [to="in1"];

    fork1 -> fork2 [from="out1",to="in1"];

    fork1 -> merge1 [from="out2",to="in1"];
    fork2 -> merge1 [from="out1",to="in2"];
    fork2 -> merge2 [from="out2",to="in2"];

    merge1 -> merge2 [from="out1",to="in1"];

    merge2 -> snk0 [from="out1"];
  ]

/-
info: ok: digraph {

  snk0 [mod = "io", label = "snk0: io"];
  src0 [mod = "io", label = "src0: io"];
  rw0_2 [mod = "merge3", label = "rw0_2: merge3"];
  rw0_1 [mod = "fork", label = "rw0_1: fork"];
  rw0_0 [mod = "fork", label = "rw0_0: fork"];


  rw0_2 -> snk0 [from = "out1", taillabel = "out1"];
  src0 -> rw0_0 [to = "in1", headlabel = "in1"];

  rw0_0 -> rw0_1 [from = "out1", to = "in1", taillabel = "out1", headlabel = "in1",];
  rw0_0 -> rw0_2 [from = "out2", to = "in1", taillabel = "out2", headlabel = "in1",];
  rw0_1 -> rw0_2 [from = "out1", to = "in2", taillabel = "out1", headlabel = "in2",];
  rw0_1 -> rw0_2 [from = "out2", to = "in2", taillabel = "out2", headlabel = "in2",];
}
-/
-- #guard_msgs in
-- #eval Graphiti.rewrite "rw0_" mergeHigh rewrite |> toString |> IO.print

end TestRewriter

end Graphiti.MergeRewrite
