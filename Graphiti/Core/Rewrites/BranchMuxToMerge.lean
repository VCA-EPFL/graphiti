/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Rewriter
import Graphiti.ExprHighElaborator

namespace Graphiti.BranchMuxToMerge

-- The following namespace just shows two alternative definitions of the matcher
-- and the abstraction matcher that use the domination algorithm instead of
-- following the condition signal.  This is unfortunately incorrect in this case
-- because the branch does not dominate the mux.  However, this would work with
-- a merge instead, where there is no direct connection.
namespace INCORRECT

def matchModLeft' (g : ExprHigh String) : RewriteResult (List String) := do
  let dom ← ofOption (.error "could not calculate dominators") <| findDom 10000 g
  let muxes := g.modules.filter (λ k v => v.snd = "mux") |>.toList |>.map (·.fst)
  let branches := g.modules.filter (λ k v => v.snd = "branch") |>.toList |>.map (·.fst)
  let (.some pair) ← muxes.foldlM (λ s x => do
      if s.isSome then return s
      let br ← ofOption (.error "mux node not in dominators") dom[x]?
      unless br ∈ branches do return none
      return some (br, x)
    ) none | throw .done
  let (.some nn_first) := followOutput g pair.fst "true" | throw (.error "could not follow output")
  let (.some nn_last) := followInput g pair.snd "in1" | throw (.error "could not follow input")
  ofOption (.error "could not find scc nodes") <| findSCCNodes g nn_first.inst nn_last.inst

/--
We can use dominators to make sure we match the same nodes as in the two
previous functions.  This doesn't work in this case though because of the fork.
If the mux were a merge domination would be the right algorithm.
-/
def matcher' (g : ExprHigh String) : RewriteResult (List String) := do
  let dom ← ofOption (.error "could not calculate dominators") <| findDom 10000 g
  let muxes := g.modules.filter (λ k v => v.snd = "mux") |>.toList |>.map (·.fst)
  let branches := g.modules.filter (λ k v => v.snd = "branch") |>.toList |>.map (·.fst)
  let (.some pair) ← muxes.foldlM (λ s x => do
      if s.isSome then return s
      let br ← ofOption (.error "mux node not in dominators") dom[x]?
      unless br ∈ branches do return none
      return some (br, x)
    ) none | throw .done
  ofOption (.error "could not find scc nodes") <| findSCCNodes g pair.fst pair.snd

end INCORRECT

/--
Match the left module so that it can be abstracted.
-/
def matchModLeft (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggedFork" do return none
      let (.some branch_nn) := followOutput g inst "out1" | return none
      unless branch_nn.typ = "TaggedBranch" && branch_nn.inputPort = "cond" do return none
      let (.some mux_nn) := followOutput g inst "out2" | return none
      unless mux_nn.typ = "TaggedMux" && mux_nn.inputPort = "cond" do return none
      let (.some bag_nn) := followOutput g mux_nn.inst "out1" | return none
      unless bag_nn.typ = "Bag" do return none
      let (.some prev_mux_nn) := followInput g mux_nn.inst "in1" | return none
      let (.some after_branch_nn) := followOutput g branch_nn.inst "true" | return none
      let (.some scc) := findSCCNodes g after_branch_nn.inst prev_mux_nn.inst | return none
      return some scc
    ) none | throw .done
  return list

/--
Match the right module so that it can be abstracted.
-/
def matchModRight (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggedFork" do return none
      let (.some branch_nn) := followOutput g inst "out1" | return none
      unless branch_nn.typ = "TaggedBranch" && branch_nn.inputPort = "cond" do return none
      let (.some mux_nn) := followOutput g inst "out2" | return none
      unless mux_nn.typ = "TaggedMux" && mux_nn.inputPort = "cond" do return none
      let (.some bag_nn) := followOutput g mux_nn.inst "out1" | return none
      unless bag_nn.typ = "Bag" do return none
      let (.some prev_mux_nn) := followInput g mux_nn.inst "in2" | return none
      let (.some after_branch_nn) := followOutput g branch_nn.inst "false" | return none
      let (.some scc) := findSCCNodes g after_branch_nn.inst prev_mux_nn.inst | return none
      return some scc
    ) none | throw .done
  return list

/--
Instead of using dominators we can also use the fork and the condition circuit
to match the graph.
-/
def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggedFork" do return none
      let (.some branch_nn) := followOutput g inst "out1" | return none
      unless branch_nn.typ = "TaggedBranch" && branch_nn.inputPort = "cond" do return none
      let (.some mux_nn) := followOutput g inst "out2" | return none
      unless mux_nn.typ = "TaggedMux" && mux_nn.inputPort = "cond" do return none
      let (.some bag_nn) := followOutput g mux_nn.inst "out1" | return none
      unless bag_nn.typ = "Bag" do return none
      let (.some after_branch_nn0) := followOutput g branch_nn.inst "true" | return none
      let (.some after_branch_nn1) := followOutput g branch_nn.inst "false" | return none
      -- Now that we go in two directions, we need two calls to findSCCNodes,
      -- otherwise it will follow the fork and reach an output.
      --
      -- However, now that we have already abstracted the modules, we don't need to search anymore.
      -- let (.some scc0) := findSCCNodes g after_branch_nn0.inst prev_mux_nn0.inst | return none
      -- let (.some scc1) := findSCCNodes g after_branch_nn1.inst prev_mux_nn1.inst | return none
      return some [inst, after_branch_nn0.inst, mux_nn.inst, after_branch_nn1.inst, branch_nn.inst, bag_nn.inst]
    ) none | throw .done
  return list

def lhs' : ExprHigh String := [graph|
    i_branch [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "TaggedBranch"];
    m_left [type = "mod_left"];
    m_right [type = "mod_right"];
    mux [type = "TaggedMux"];
    fork [type = "TaggedFork"];
    bag [type = "Bag"];

    i_branch -> branch [to = "val"];
    i_cond -> fork [to = "in1"];
    fork -> branch [from = "out1", to = "cond"];
    fork -> mux [from = "out2", to = "cond"];

    mux -> bag [from = "out1", to = "in1"];
    bag -> o_out [from = "out1"];

    branch -> m_left [from = "true", to = "m_in"];
    branch -> m_right [from = "false", to = "m_in"];

    m_left -> mux [from = "m_out", to = "in1"];
    m_right -> mux [from = "m_out", to = "in2"];
  ]

#eval IO.print lhs'
-- #eval IO.print lhs'.invert
#eval IO.print lhs'

def lhs := lhs'.extract (matcher lhs' |>.toOption |>.get rfl) |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl

def rhs : ExprHigh String := [graph|
    i_branch [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "TaggedBranch"];
    m_left [type = "mod_left"];
    m_right [type = "mod_right"];
    merge [type = "TaggedMerge"];

    i_branch -> branch [to = "val"];
    i_cond -> branch [to = "cond"];

    merge -> o_out [from = "out"];

    branch -> m_left [from = "true", to = "m_in"];
    branch -> m_right [from = "false", to = "m_in"];

    m_left -> merge [from = "m_out", to = "in1"];
    m_right -> merge [from = "m_out", to = "in2"];
  ]

#eval IO.print rhs

def rhsLower := rhs.lower.get rfl

/--
This rewrite adds abstractions to the definition, which provide patterns to
extract parts of the graph.  The `type` given to each extracted node has to
match the `type` of the node in LHS and RHS graphs.
-/
def rewrite : Rewrite String :=
  { abstractions := [⟨matchModLeft, "mod_left"⟩, ⟨matchModRight, "mod_right"⟩],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

namespace TEST

def lhs' : ExprHigh String := [graph|
    i_branch [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "TaggedBranch"];
    m_left1 [type = "mod_left1"];
    m_left2 [type = "mod_left2"];
    m_right [type = "mod_right2"];
    mux [type = "TaggedMux"];
    fork [type = "TaggedFork"];
    bag [type = "Bag"];

    i_branch -> branch [to = "val"];
    i_cond -> fork [to = "in1"];
    fork -> branch [from = "out1", to = "cond"];
    fork -> mux [from = "out2", to = "cond"];
    m_left1 -> m_left2 [from = "out1", to = "in1"];

    mux -> bag [from = "out1", to = "in1"];
    bag -> o_out [from = "out1"];

    branch -> m_left1 [from = "true", to = "m_in"];
    branch -> m_right [from = "false", to = "m_in"];

    m_left2 -> mux [from = "m_out", to = "in1"];
    m_right -> mux [from = "m_out", to = "in2"];
  ]

#eval matchModLeft lhs'
#eval matchModRight lhs'
#eval matcher lhs'

-- #eval (Abstraction.mk matchModLeft "mod_left").run "rw0_" lhs' |>.toOption |>.get! |> Prod.fst
--       |> (Abstraction.mk matchModRight "mod_right").run "rw1_"
      -- |> matchModRight
      -- |> calcSucc
#eval rewrite.run "rw0_" lhs' |>.toOption |>.get! |> IO.print

end TEST

end Graphiti.BranchMuxToMerge
