/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

/- public import Graphiti.Core.Dataflow.Rewrites.LoopRewrite -/
public import Graphiti.Core.Dataflow.Rewrites.LoopRewrite2
public import Graphiti.Core.Dataflow.Rewrites.CombineBranch
public import Graphiti.Core.Dataflow.Rewrites.CombineMux
public import Graphiti.Core.Dataflow.Rewrites.JoinSplitLoopCond
public import Graphiti.Core.Dataflow.Rewrites.JoinSplitLoopCondAlt
public import Graphiti.Core.Dataflow.Rewrites.ReduceSplitJoin
public import Graphiti.Core.Dataflow.Rewrites.PureRewrites
public import Graphiti.Core.Dataflow.Rewrites.LoadRewrite
public import Graphiti.Core.Dataflow.Rewrites.JoinQueueLeftRewrite
public import Graphiti.Core.Dataflow.Rewrites.JoinQueueRightRewrite
public import Graphiti.Core.Dataflow.Rewrites.MuxQueueRightRewrite
public import Graphiti.Core.Dataflow.Rewrites.PureSink
public import Graphiti.Core.Dataflow.Rewrites.SplitSinkLeft
public import Graphiti.Core.Dataflow.Rewrites.SplitSinkRight
public import Graphiti.Core.Dataflow.Rewrites.PureSeqComp
public import Graphiti.Core.Dataflow.Rewrites.PureJoinLeft
public import Graphiti.Core.Dataflow.Rewrites.PureJoinRight
public import Graphiti.Core.Dataflow.Rewrites.PureSplitRight
public import Graphiti.Core.Dataflow.Rewrites.PureSplitLeft
public import Graphiti.Core.Dataflow.Rewrites.JoinSplitElim
public import Graphiti.Core.Dataflow.Rewrites.JoinAssocL
public import Graphiti.Core.Dataflow.Rewrites.JoinAssocR
public import Graphiti.Core.Dataflow.Rewrites.JoinComm
public import Graphiti.Core.Dataflow.Rewrites.ForkPure
public import Graphiti.Core.Dataflow.Rewrites.ForkJoin
/- public import Graphiti.Core.Dataflow.Rewrites.JoinRewrite -/
public import Graphiti.Core.Dataflow.Rewrites.Fork3Rewrite
public import Graphiti.Core.Dataflow.Rewrites.Fork4Rewrite
public import Graphiti.Core.Dataflow.Rewrites.Fork5Rewrite
public import Graphiti.Core.Dataflow.Rewrites.Fork6Rewrite
public import Graphiti.Core.Dataflow.Rewrites.Fork7Rewrite
public import Graphiti.Core.Dataflow.Rewrites.Fork8Rewrite
public import Graphiti.Core.Dataflow.Rewrites.Fork9Rewrite
public import Graphiti.Core.Dataflow.Rewrites.Fork10Rewrite
public import Graphiti.Core.Dataflow.Rewrites.BranchMuxToPure
public import Graphiti.Core.Dataflow.Rewrites.BranchPureMuxLeft
public import Graphiti.Core.Dataflow.Rewrites.BranchPureMuxRight
-- import Graphiti.Rewrites.JoinRewriteCorrect

@[expose] public section

namespace Graphiti

def rewrite_index :=
  rewrites_to_map
    [ LoopRewrite2.rewrite .none
    , CombineBranch.rewrite
    , CombineMux.rewrite
    , JoinSplitLoopCond.rewrite
    , JoinSplitLoopCondAlt.rewrite
    , ReduceSplitJoin.rewrite
    , PureRewrites.ConstantNat.rewrite
    , PureRewrites.ConstantBool.rewrite
    , PureRewrites.Constant.rewrite
    , PureRewrites.Operator1.rewrite
    , PureRewrites.Operator2.rewrite
    , PureRewrites.Operator3.rewrite
    , PureRewrites.CondOperator1.rewrite
    , PureRewrites.CondOperator2.rewrite
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

def reverse_rewrite_with_index (rinfo : RuntimeEntry String (String × Nat)) : RewriteResult' String (String × Nat) Rewrite := do
  let name ← ofOption (.error s!"{decl_name%}: no rinfo report") rinfo.name
  let rw ← ofOption (.error s!"{decl_name%}: '{name}' reverse rewrite generation failed") <| rewrite_index.find? name
  reverse_rewrite rw rinfo

/--
The reverseRewrites function will look through the runitme trace and identify the rewrites that should be inverted using
`rev-start` and `rev-stop` markers.
-/
def reverseRewrites (g : ExprHigh String (String × Nat)) : RewriteResult' String (String × Nat) ExprHigh := do
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
