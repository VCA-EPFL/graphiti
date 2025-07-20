/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Rewrites.LoopRewrite
import Graphiti.Rewrites.LoopRewrite2
import Graphiti.Rewrites.CombineBranch
import Graphiti.Rewrites.CombineMux
import Graphiti.Rewrites.JoinSplitLoopCond
import Graphiti.Rewrites.JoinSplitLoopCondAlt
import Graphiti.Rewrites.ReduceSplitJoin
import Graphiti.Rewrites.PureRewrites
import Graphiti.Rewrites.LoadRewrite
import Graphiti.Rewrites.JoinQueueLeftRewrite
import Graphiti.Rewrites.JoinQueueRightRewrite
import Graphiti.Rewrites.MuxQueueRightRewrite
import Graphiti.Rewrites.PureSink
import Graphiti.Rewrites.SplitSinkLeft
import Graphiti.Rewrites.SplitSinkRight
import Graphiti.Rewrites.PureSeqComp
import Graphiti.Rewrites.PureJoinLeft
import Graphiti.Rewrites.PureJoinRight
import Graphiti.Rewrites.PureSplitRight
import Graphiti.Rewrites.PureSplitLeft
import Graphiti.Rewrites.JoinPureUnit
import Graphiti.Rewrites.JoinSplitElim
import Graphiti.Rewrites.JoinAssocL
import Graphiti.Rewrites.JoinAssocR
import Graphiti.Rewrites.JoinComm
import Graphiti.Rewrites.ForkPure
import Graphiti.Rewrites.ForkJoin
import Graphiti.Rewrites.JoinRewrite
import Graphiti.Rewrites.Fork3Rewrite
import Graphiti.Rewrites.Fork4Rewrite
import Graphiti.Rewrites.Fork5Rewrite
import Graphiti.Rewrites.Fork6Rewrite
import Graphiti.Rewrites.Fork7Rewrite
import Graphiti.Rewrites.Fork8Rewrite
import Graphiti.Rewrites.Fork9Rewrite
import Graphiti.Rewrites.Fork10Rewrite
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
    , JoinPureUnit.rewrite
    , JoinSplitElim.rewrite
    , JoinAssocL.rewrite
    , JoinAssocR.rewrite
    , JoinComm.rewrite
    , ForkPure.rewrite
    , ForkJoin.rewrite
    , JoinRewrite.rewrite
    , Fork3Rewrite.rewrite
    , Fork4Rewrite.rewrite
    , Fork5Rewrite.rewrite
    , Fork6Rewrite.rewrite
    , Fork7Rewrite.rewrite
    , Fork8Rewrite.rewrite
    , Fork9Rewrite.rewrite
    , Fork10Rewrite.rewrite
    ]

end Graphiti
