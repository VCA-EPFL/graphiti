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
import Graphiti.Core.Rewrites.JoinPureUnit
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
