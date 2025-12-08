/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewrites.LoopRewrite
import Graphiti.Core.Rewrites.LoopRewrite2
import Graphiti.Core.Rewrites.CombineBranch
import Graphiti.Core.Rewrites.CombineMux
import Graphiti.Core.Rewrites.JoinSplitLoopCond
import Graphiti.Core.Rewrites.JoinSplitLoopCondAlt
import Graphiti.Core.Rewrites.ReduceSplitJoin
import Graphiti.Core.Rewrites.PureRewrites
import Graphiti.Core.Rewrites.LoadRewrite
import Graphiti.Core.Rewrites.JoinQueueLeftRewrite
import Graphiti.Core.Rewrites.JoinQueueRightRewrite
import Graphiti.Core.Rewrites.MuxQueueRightRewrite
import Graphiti.Core.Rewrites.PureSink
import Graphiti.Core.Rewrites.SplitSinkLeft
import Graphiti.Core.Rewrites.SplitSinkRight
import Graphiti.Core.Rewrites.PureSeqComp
import Graphiti.Core.Rewrites.PureJoinLeft
import Graphiti.Core.Rewrites.PureJoinRight
import Graphiti.Core.Rewrites.PureSplitRight
import Graphiti.Core.Rewrites.PureSplitLeft
import Graphiti.Core.Rewrites.JoinSplitElim
import Graphiti.Core.Rewrites.JoinAssocL
import Graphiti.Core.Rewrites.JoinAssocR
import Graphiti.Core.Rewrites.JoinComm
import Graphiti.Core.Rewrites.ForkPure
import Graphiti.Core.Rewrites.ForkJoin
import Graphiti.Core.Rewrites.JoinRewrite
import Graphiti.Core.Rewrites.Fork3Rewrite
import Graphiti.Core.Rewrites.Fork4Rewrite
import Graphiti.Core.Rewrites.Fork5Rewrite
import Graphiti.Core.Rewrites.Fork6Rewrite
import Graphiti.Core.Rewrites.Fork7Rewrite
import Graphiti.Core.Rewrites.Fork8Rewrite
import Graphiti.Core.Rewrites.Fork9Rewrite
import Graphiti.Core.Rewrites.Fork10Rewrite
import Graphiti.Core.Rewrites.BranchMuxToPure
import Graphiti.Core.Rewrites.BranchPureMuxLeft
import Graphiti.Core.Rewrites.BranchPureMuxRight
-- import Graphiti.Rewrites.JoinRewriteCorrect

namespace Graphiti

def rewrite_index :=
  rewrites_to_map
    [ LoopRewrite2.rewrite
    , CombineBranch.rewrite
    , CombineMux.rewrite
    , JoinSplitLoopCond.rewrite
    , JoinSplitLoopCondAlt.rewrite
    , ReduceSplitJoin.rewrite
    , PureRewrites.Constant.rewrite
    , PureRewrites.Operator1.rewrite
    , PureRewrites.Operator2.rewrite
    , PureRewrites.Operator3.rewrite
    , PureRewrites.Fork.rewrite
    , LoadRewrite.rewrite
    , JoinQueueLeftRewrite.rewrite
    , JoinQueueRightRewrite.rewrite
    , MuxQueueRightRewrite.rewrite
    , PureSink.rewrite
    , SplitSinkLeft.rewrite
    , SplitSinkRight.rewrite
    , PureSeqComp.rewrite
    , PureJoinLeft.rewrite
    , PureJoinRight.rewrite
    , PureSplitRight.rewrite
    , PureSplitLeft.rewrite
    , JoinSplitElim.rewrite
    , JoinAssocL.rewrite
    , JoinAssocR.rewrite
    , JoinComm.rewrite
    , ForkPure.rewrite
    , ForkJoin.rewrite
    , Fork3Rewrite.rewrite
    , Fork4Rewrite.rewrite
    , Fork5Rewrite.rewrite
    , Fork6Rewrite.rewrite
    , Fork7Rewrite.rewrite
    , Fork8Rewrite.rewrite
    , Fork9Rewrite.rewrite
    , Fork10Rewrite.rewrite
    , BranchMuxToPure.rewrite
    , BranchPureMuxLeft.rewrite
    , BranchPureMuxRight.rewrite
    ]

def reverse_rewrite_with_index (rinfo : RuntimeEntry) : RewriteResult (Rewrite String (String × Nat)) := do
  let rw ← do
    let name ← ofOption (.error s!"{decl_name%}: no rinfo report") rinfo.name
    (match name with
     | "join-split-elim" => do
       let s ← ofOption (.error s!"{decl_name%}: 'join-split-elim' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return JoinSplitElim.targetedRewrite s
     | "join-comm" => do
       let s ← ofOption (.error s!"{decl_name%}: 'join-comm' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return JoinComm.targetedRewrite s
     | "join-assoc-right" => do
       let s ← ofOption (.error s!"{decl_name%}: 'join-assoc-right' reverse rewrite generation failed") rinfo.matched_subgraph[1]?
       return JoinAssocR.targetedRewrite s
     | "join-assoc-left" => do
       let s ← ofOption (.error s!"{decl_name%}: 'join-assoc-left' reverse rewrite generation failed") rinfo.matched_subgraph[1]?
       return JoinAssocL.targetedRewrite s
     | "pure-fork" => do
       let s ← ofOption (.error s!"{decl_name%}: 'pure-fork' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return {PureRewrites.Fork.rewrite with pattern := PureRewrites.Fork.match_node s}
     | "pure-operator3" => do
       let s ← ofOption (.error s!"{decl_name%}: 'pure-operator3' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return {PureRewrites.Operator3.rewrite with pattern := PureRewrites.Operator3.match_node s}
     | "pure-operator2" => do
       let s ← ofOption (.error s!"{decl_name%}: 'pure-operator2' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return {PureRewrites.Operator2.rewrite with pattern := PureRewrites.Operator2.match_node s}
     | "pure-operator1" => do
       let s ← ofOption (.error s!"{decl_name%}: 'pure-operator1' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return {PureRewrites.Operator1.rewrite with pattern := PureRewrites.Operator1.match_node s}
     | "pure-constant" => do
       let s ← ofOption (.error s!"{decl_name%}: 'pure-constant' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return {PureRewrites.Constant.rewrite with pattern := PureRewrites.Constant.match_node s}
     | "pure-constant-nat" => do
       let s ← ofOption (.error s!"{decl_name%}: 'pure-constant-nat' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return {PureRewrites.ConstantNat.rewrite with pattern := PureRewrites.ConstantNat.match_node s}
     | "pure-constant-bool" => do
       let s ← ofOption (.error s!"{decl_name%}: 'pure-constant-bool' reverse rewrite generation failed") rinfo.matched_subgraph[0]?
       return {PureRewrites.ConstantBool.rewrite with pattern := PureRewrites.ConstantBool.match_node s}
     | s => ofOption (.error s!"{decl_name%}: '{s}' reverse rewrite generation failed") <| rewrite_index.find? name)
  reverse_rewrite rw rinfo

/--
The reverseRewrites function will look through the runitme trace and identify the rewrites that should be inverted using
`rev-start` and `rev-stop` markers.
-/
def reverseRewrites (g : ExprHigh String (String × Nat)) : RewriteResult (ExprHigh String (String × Nat)) := do
  let st ← get
  let st_worklist := st.1.reverse.tail.filter (fun rinfo => rinfo.type != .debug)

  let (_, _, st_worklist_to_be_inverted) := st_worklist.foldl (λ (reverse?, curr, list) entry =>
      if reverse? then
        if entry.stopMarker? then
          (false, [], list.concat curr)
        else
          (true, curr.concat entry, list)
      else (entry.startMarker?, [], list)
    ) (false, [], [])

  st_worklist_to_be_inverted.foldlM (λ g st_worklist' =>
    st_worklist'.foldlM (λ g rinfo => do
      let rewrite ← reverse_rewrite_with_index rinfo
      rewrite.run' (norm := false) g
    ) g) g

end Graphiti
