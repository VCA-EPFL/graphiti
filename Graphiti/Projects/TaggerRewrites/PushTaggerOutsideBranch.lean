/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.BranchInorderMux2Merge

-- TODO: 2 inputs, 2 outputs for the taggrCntrlAligner:
-- enq_untagged, complete_tagged are the input ports
-- tagged, deq_untagged are the output ones

/--
Matcher used for abstraction of the left module. Currently we do not check that the Mux and Branch are paired
so it could probably be unsafe (what would happen?).
-/
def matchModLeft : Pattern String := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggerCntrlAligner" do return none
      let (.some branch_nn) := followInput g inst "enq_untagged" | return none
      unless branch_nn.typ = "Branch" && branch_nn.inputPort = "true" do return none
      let (.some begin_m) := followOutput g inst "tagged" | return none
      let (.some end_m) := followInput g inst "complete_tagged" | return none
      let (.some mux_nn) := followOutput g inst "deq_untagged" | return none
      unless mux_nn.typ = "Merge" do return none
      let (.some scc) := findSCCNodes g begin_m.inst end_m.inst | return none
      return some scc
    ) none | throw .done
  return (list, [])


/--
Matcher used for abstraction of the right module
-/
def matchModRight : Pattern String := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggerCntrlAligner" do return none
      let (.some branch_nn) := followInput g inst "enq_untagged" | return none
      unless branch_nn.typ = "Branch" && branch_nn.inputPort = "false" do return none
      let (.some begin_m) := followOutput g inst "tagged" | return none
      let (.some end_m) := followInput g inst "complete_tagged" | return none
      let (.some mux_nn) := followOutput g inst "deq_untagged" | return none
      unless mux_nn.typ = "Merge" do return none
      let (.some scc) := findSCCNodes g begin_m.inst end_m.inst | return none
      return some scc
    ) none | throw .done
  return (list, [])


def matcher : Pattern String := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "Branch" do return none

      let (.some taggerL) := followOutput g inst "true" | return none
      let (.some taggerR) := followOutput g inst "false" | return none

      -- We do not double check we got the right type, as the name of the port should be enough?
      let (.some begin_l) := followOutput g taggerL.inst "tagged" | return none
      let (.some end_l) := followInput g taggerL.inst "complete_tagged" | return none
      let (.some begin_r) := followOutput g taggerR.inst "tagged" | return none
      let (.some end_r) := followInput g taggerR.inst "complete_tagged" | return none
      unless (begin_l.typ = "mod_left") && (begin_r.typ = "mod_right") && (begin_l.inst = end_l.inst) && (begin_r.inst = end_r.inst) do return none
      let (.some mux_nn) := followOutput g taggerL.inst "deq_untagged" | return none
      unless mux_nn.typ = "Merge" do return none
      -- We do not double check that the Mux match the Branch.

      return some [inst, taggerL.inst, taggerR.inst, begin_l.inst, begin_r.inst, mux_nn.inst]
    ) none | throw .done
  return (list, [])

def lhs' : ExprHigh String := [graph|
    i_data [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "Branch"];
    tagger1 [type = "TaggerCntrlAligner"];
    tagger2 [type = "TaggerCntrlAligner"];
    m_left [type = "mod_left"];
    m_right [type = "mod_right"];
    merge [type = "Merge"];

    i_cond -> branch [to = "cond"];

    branch -> tagger1 [from = "true", to = "enq_untagged"];
    branch -> tagger2 [from = "false", to = "enq_untagged"];

    tagger1 -> m_left [from = "tagged", to="m_in"];
    tagger2 -> m_right [from = "tagged", to="m_in"];

    m_left -> tagger1 [from = "m_out", to = "complete_tagged"];
    m_right -> tagger2 [from = "m_out", to = "complete_tagged"];

    tagger1 -> merge [from = "deq_untagged", to = "in1"];
    tagger2 -> merge [from = "deq_untagged", to = "in2"];

    merge -> o_out [from = "out1"];
  ]

def lhs := lhs'.extract ["branch", "tagger1", "tagger2", "m_left", "m_right", "merge"] |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl


def rhs : ExprHigh String := [graph|
    i_data [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "Branch"];
    join [type = "Join"];
    split [type = "Split"];
    tagger [type = "TaggerCntrlAligner"];
    m_left [type = "mod_left"];
    m_right [type = "mod_right"];
    merge [type = "Merge"];


    i_data -> join [to = "in1"];
    i_cond -> join [to = "in2"];

    join -> tagger [from = "out1", to = "enq_untagged"];
    tagger -> split [to = "in1", from = "tagged"];

    split -> branch [from = "out1", to = "data"];
    split -> branch [from = "out2", to = "cond"];

    branch -> m_left [from = "true", to="m_in"];
    branch -> m_right [from = "false", to="m_in"];


    m_left-> merge [from = "m_out", to = "in1"];
    m_right -> merge [from = "m_out", to = "in2"];
    merge -> tagger [from = "m_out", to = "complete_tagged"];

    tagger -> o_out [from = "deq_untagged"];
  ]

def rhsLower := rhs.lower.get rfl
-- Double checking that the left and right abstracter seems to work:
#eval match (matchModRight lhs').run' default with | .some e => IO.print e | _ => IO.print ""
#eval match (matchModLeft lhs').run' default with | .some e => IO.print e | _ => IO.print ""
#eval match (matcher lhs').run' default with | .some e => IO.print e | _ => IO.print ""
#eval IO.print lhs'


/--
This rewrite adds abstractions to the definition, which provide patterns to
extract parts of the graph.  The `type` given to each extracted node has to
match the `type` of the node in LHS and RHS graphs.
-/
def rewrite : Rewrite String :=
  { abstractions := [⟨matchModLeft, "mod_left"⟩, ⟨matchModRight, "mod_right"⟩],
    pattern := matcher,
    rewrite := fun _ => pure ⟨lhsLower, rhsLower⟩ }

namespace TEST

def lhs' : ExprHigh String :=
[graph|
    i_data [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "Branch"];
    tagger1 [type = "TaggerCntrlAligner"];
    tagger2 [type = "TaggerCntrlAligner"];
    m_left1 [type = "mod_left1"];
    m_left2 [type = "mod_left2"];
    m_right [type = "mod_right2"];
    merge [type = "Merge"];

    i_cond -> branch [to = "cond"];

    merge -> o_out [from = "out1"];

    branch -> tagger1 [from = "true", to = "enq_untagged"];
    branch -> tagger2 [from = "false", to = "enq_untagged"];

    tagger1 -> m_left1 [from = "tagged", to="m_in"];
    tagger2 -> m_right [from = "tagged", to="m_in"];

    m_left1 -> m_left2 [from="m_out", to="m_in"];

    m_left2 -> tagger1 [from = "m_out", to = "complete_tagged"];
    m_right -> tagger2 [from = "m_out", to = "complete_tagged"];

    tagger1 -> merge [from = "deq_untagged", to = "in1"];
    tagger2 -> merge [from = "deq_untagged", to = "in2"];

  ]

#eval rewrite.run "rw0_" lhs' |>.run' default |>.get! |> IO.print

end TEST

end Graphiti.BranchInorderMux2Merge
