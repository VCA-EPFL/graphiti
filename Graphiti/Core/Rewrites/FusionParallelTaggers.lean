/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.FusionParallelTagger

-- Rewrite to rewrite parallel matcher input/output taggers.

/--
Matcher used for abstraction of the top module.
-/
def matchModL (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "Join" do return none
      let (.some tagger_l) := followInput g inst "in1" | return none
      let (.some tagger_r) := followInput g inst "in2" | return none
      unless tagger_l.typ = "TaggerCntrlAligner" do return none
      unless tagger_r.typ = "TaggerCntrlAligner" do return none
      let (.some begin_l) := followOutput g tagger_l.inst "tagged" | return none
      let (.some end_l) := followInput g tagger_l.inst "complete_tagged" | return none
      let (.some scc) := findSCCNodes g begin_l.inst end_l.inst | return none
      return some scc
    ) none | throw .done
  return list


/--
Matcher used for abstraction of the right module
-/
def matchModR (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "Join" do return none
      let (.some tagger_l) := followInput g inst "in1" | return none
      let (.some tagger_r) := followInput g inst "in2" | return none
      unless tagger_l.typ = "TaggerCntrlAligner" do return none
      unless tagger_r.typ = "TaggerCntrlAligner" do return none
      let (.some begin_r) := followOutput g tagger_r.inst "tagged" | return none
      let (.some end_r) := followInput g tagger_r.inst "complete_tagged" | return none
      let (.some scc) := findSCCNodes g begin_r.inst end_r.inst | return none
      return some scc
    ) none | throw .done
  return list


def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "Join" do return none
      let (.some tagger_l) := followInput g inst "in1" | return none
      let (.some tagger_r) := followInput g inst "in2" | return none
      unless tagger_l.typ = "TaggerCntrlAligner" do return none
      unless tagger_r.typ = "TaggerCntrlAligner" do return none
      let (.some begin_l) := followOutput g tagger_l.inst "tagged" | return none
      let (.some end_l) := followInput g tagger_l.inst "complete_tagged" | return none
      let (.some begin_r) := followOutput g tagger_r.inst "tagged" | return none
      let (.some end_r) := followInput g tagger_r.inst "complete_tagged" | return none
      unless begin_l.inst == end_l.inst && begin_r.inst == end_r.inst do return none
      return some [inst, tagger_l.inst, tagger_r.inst, begin_l.inst, begin_r.inst]
    ) none | throw .done
  return list

def lhs' : ExprHigh String := [graph|
    i_datal [type = "io"];
    i_datar [type = "io"];
    o_data [type = "io"];

    taggerl [type = "TaggerCntrlAligner"];
    m_l [type = "mod_left"];
    taggerr [type = "TaggerCntrlAligner"];
    m_r [type = "mod_right"];

    j [type = "Join"];

    i_datal -> taggerl [to = "enq_untagged"];
    i_datar -> taggerr [to = "enq_untagged"];

    taggerl -> m_l [from = "tagged", to="m_in"];
    m_l  -> taggerl [from = "m_out", to = "complete_tagged"];

    taggerr -> m_r [from = "tagged", to="m_in"];

    m_r -> taggerr [from = "m_out", to = "complete_tagged"];

    taggerl -> j [from = "deq_untagged", to = "in1"];
    taggerr -> j [from = "deq_untagged", to = "in2"];

    j -> o_data [from = "deq_untagged"];
  ]

def lhs := lhs'.extract [ "j", "taggerl", "taggerr", "m_l","m_r"] |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl


def rhs : ExprHigh String := [graph|
    i_datal [type = "io"];
    i_datar [type = "io"];
    o_data [type = "io"];

    j_in [type = "Join"];
    tagger [type = "TaggerCntrlAligner"];

    m_l [type = "mod_left"];
    m_r [type = "mod_right"];
    sep_tag [ type = "TaggedSplit"];
    sep_data [ type = "Split"];
    fork_tag [type = "Fork"];
    pack1 [ type = "Join"];
    pack2 [ type = "Join"];
    j_out [type = "Aligner"];

    i_datal -> j_in [to = "enq_untagged"];
    i_datar -> j_in [to = "enq_untagged"];

    j_in -> tagger [to = "enq_untagged", from="out1"];

    tagger -> sep_tag [from = "tagged", to="in1"];
    sep_tag -> fork_tag [from = "out1", to="in1"];
    sep_tag -> sep_data [from = "out2", to="in1"];

    sep_data -> pack1 [from = "out1", to="in2"];
    sep_data -> pack2 [from = "out2", to="in2"];
    fork_tag -> pack1 [from = "out1", to="in1"];
    fork_tag -> pack2 [from = "out2", to="in1"];
    pack1 -> m_l [from = "out1", to="m_in"];
    pack2 -> m_r [from = "out1", to="m_in"];


    m_l -> j_out [from = "m_out", to = "in1"];
    m_r -> j_out [from = "m_out", to = "in2"];

    j_out -> tagger [from = "out1", to = "complete_tagged"];
    tagger -> o_data [from = "deq_untagged"];
  ]


def rhsLower := rhs.lower.get rfl
-- Double checking that the left and right abstracter seems to work:
#eval matchModR  lhs'
#eval matchModR lhs'
#eval matcher lhs'
#eval IO.print lhs'


/--
This rewrite adds abstractions to the definition, which provide patterns to
extract parts of the graph.  The `type` given to each extracted node has to
match the `type` of the node in LHS and RHS graphs.
-/
def rewrite : Rewrite String :=
  { abstractions := [⟨matchModL, "mod_left"⟩, ⟨matchModR, "mod_right"⟩],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

namespace TEST

def lhs' : ExprHigh String :=
[graph|
    i_datal [type = "io"];
    i_datar [type = "io"];
    o_data [type = "io"];

    taggerl [type = "TaggerCntrlAligner"];
    m_l [type = "mod_left"];
    taggerr [type = "TaggerCntrlAligner"];
    m_r [type = "mod_right"];

    j [type = "Join"];

    i_datal -> taggerl [to = "enq_untagged"];
    i_datar -> taggerr [to = "enq_untagged"];

    taggerl -> m_l [from = "tagged", to="m_in"];
    m_l  -> taggerl [from = "m_out", to = "complete_tagged"];

    taggerr -> m_r [from = "tagged", to="m_in"];

    m_r -> taggerr [from = "m_out", to = "complete_tagged"];

    taggerl -> j [from = "deq_untagged", to ="in1"];
    taggerr -> j [from = "deq_untagged", to ="in2"];

    j -> o_data [from = "deq_untagged"];
  ]


#eval rewrite.run "rw0_" lhs' |>.toOption |>.get! |> IO.print

end TEST

end Graphiti.FusionParallelTagger
