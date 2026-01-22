/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.Graph.ExprHighElaborator

namespace Graphiti.FusionTaggerTagger

-- Rewrite to rewrite sequence of two single input/output taggers.

/--
Matcher used for abstraction of the top module.
-/
def matchModTop : Pattern String String 0 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggerCntrlAligner" do return none
      let (.some begin_top) := followOutput g inst "tagged" | return none
      let (.some end_top) := followInput g inst "complete_tagged" | return none
      let (.some tagger2) := followOutput g inst "deq_untagged" | return none
      unless tagger2.typ = "TaggerCntrlAligner" do return none
      let (.some begin_bottom) := followOutput g tagger2.inst "tagged" | return none
      let (.some end_bottom) := followInput g tagger2.inst "complete_tagged" | return none
      let (.some scc) := findClosedRegion g begin_top.inst end_top.inst | return none
      return some scc
    ) none | throw .done
  return (list, #v[])


/--
Matcher used for abstraction of the right module
-/
def matchModBottom : Pattern String String 0 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggerCntrlAligner" do return none
      let (.some begin_top) := followOutput g inst "tagged" | return none
      let (.some end_top) := followInput g inst "complete_tagged" | return none
      let (.some tagger2) := followOutput g inst "deq_untagged" | return none
      unless tagger2.typ = "TaggerCntrlAligner" do return none
      let (.some begin_bottom) := followOutput g tagger2.inst "tagged" | return none
      let (.some end_bottom) := followInput g tagger2.inst "complete_tagged" | return none
      let (.some scc) := findClosedRegion g begin_bottom.inst end_bottom.inst | return none
      return some scc
    ) none | throw .done
  return (list, #v[])


def matcher : Pattern String String 0 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggerCntrlAligner" do return none
      let (.some begin_top) := followOutput g inst "tagged" | return none
      let (.some end_top) := followInput g inst "complete_tagged" | return none
      let (.some tagger2) := followOutput g inst "deq_untagged" | return none
      unless tagger2.typ = "TaggerCntrlAligner" && (begin_top.inst == end_top.inst) do return none
      let (.some begin_bottom) := followOutput g tagger2.inst "tagged" | return none
      let (.some end_bottom) := followInput g tagger2.inst "complete_tagged" | return none
      unless (begin_bottom.inst == end_bottom.inst) do return none
      return some [inst, begin_top.inst, tagger2.inst, begin_bottom.inst]
    ) none | throw .done
  return (list, #v[])

def lhs' : ExprHigh String String := [graph|
    i_data [type = "io"];
    o_data [type = "io"];

    tagger1 [type = "TaggerCntrlAligner"];
    m_1 [type = "mod_left"];
    tagger2 [type = "TaggerCntrlAligner"];
    m_2 [type = "mod_right"];

    i_data -> tagger1 [to = "enq_untagged"];

    tagger1 -> m_1 [from = "tagged", to="m_in"];
    m_1  -> tagger1 [from = "m_out", to = "complete_tagged"];

    tagger1 -> tagger2 [from = "deq_untagged", to = "enq_untagged"];
    tagger2 -> m_2 [from = "tagged", to="m_in"];

    m_2 -> tagger2 [from = "m_out", to = "complete_tagged"];

    tagger2 -> o_data [from = "deq_untagged"];
  ]

def lhs := lhs'.extract ["tagger1", "m_1", "tagger2", "m_2" ] |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl


def rhs : ExprHigh String String := [graph|
    i_data [type = "io"];
    o_data [type = "io"];

    tagger [type = "TaggerCntrlAligner"];
    m_1 [type = "mod_left"];
    m_2 [type = "mod_right"];

    i_data -> tagger [to = "enq_untagged"];

    tagger -> m_1 [from = "tagged", to="m_in"];
    m_1 -> m_2 [from = "m_out", to="m_in"];
    m_2  -> tagger [from = "m_out", to = "complete_tagged"];

    tagger -> o_data [from = "deq_untagged"];
  ]


def rhsLower := rhs.lower.get rfl
-- Double checking that the left and right abstracter seems to work:
-- #eval matchModTop lhs'
-- #eval matchModBottom lhs'
-- #eval matcher lhs'
-- #eval IO.print lhs'


/--
This rewrite adds abstractions to the definition, which provide patterns to
extract parts of the graph.  The `type` given to each extracted node has to
match the `type` of the node in LHS and RHS graphs.
-/
def rewrite : Rewrite String String :=
  { abstractions := [⟨0, matchModTop, "mod_left"⟩, ⟨0, matchModBottom, "mod_right"⟩],
    params := 0,
    pattern := matcher,
    rewrite := λ _ _ => ⟨lhsLower, rhsLower⟩
  }

namespace TEST

def lhs' : ExprHigh String String :=[graph|
    i_data [type = "io"];
    o_data [type = "io"];

    tagger1 [type = "TaggerCntrlAligner"];
    m_1 [type = "mod_left"];
    tagger2 [type = "TaggerCntrlAligner"];
    m_2 [type = "mod_right"];

    i_data -> tagger1 [to = "enq_untagged"];

    tagger1 -> m_1 [from = "tagged", to="m_in"];
    m_1  -> tagger1 [from = "m_out", to = "complete_tagged"];

    tagger1 -> tagger2 [from = "deq_untagged", to = "enq_untagged"];
    tagger2 -> m_2 [from = "tagged", to="m_in"];

    m_2 -> tagger2 [from = "m_out", to = "complete_tagged"];

    tagger2 -> o_data [from = "deq_untagged"];
  ]

-- #eval rewrite.run "rw0_" lhs' |>.toOption |>.get! |> IO.print

end TEST

end Graphiti.FusionTaggerTagger
