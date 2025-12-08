/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.ExprHigh
import Graphiti.Core.DotParser
import Graphiti.Core.Rewriter
import Graphiti.Core.DynamaticPrinter
import Graphiti.Core.Rewrites
import Graphiti.Core.JSLang

open Batteries (AssocList)

open Graphiti

structure CmdArgs where
  outputFile : Option System.FilePath := none
  inputFile : Option System.FilePath := none
  logFile : Option System.FilePath := none
  logStdout : Bool := false
  noDynamaticDot : Bool := false
  blueSpecDot : Bool := false
  parseOnly : Bool := false
  graphitiOracle : String := "graphiti_oracle"
  fast : Bool := false
  reverse : Bool := false
  help : Bool := false
deriving Inhabited

def CmdArgs.empty : CmdArgs := {}

/--
Split short options up into multiple options: i.e. '-ol' will become '-o -l'.
-/
def preprocess (s : String): List String :=
  if "--".isPrefixOf s then [s] else
  if "-".isPrefixOf s ∧ s.length <= 2 then [s] else
  if ¬ "-".isPrefixOf s then [s] else
  (s.toList.drop 1).map (λ x => "-" ++ toString x)

def parseArgs (args : List String) : Except String CmdArgs := go CmdArgs.empty args
  where
    go (c : CmdArgs) : List String → Except String CmdArgs
    | .cons "-h" _rst | .cons "--help" _rst => .ok {c with help := true}
    | .cons "-o" (.cons fp rst) | .cons "--output" (.cons fp rst) =>
      go {c with outputFile := some fp} rst
    | .cons "-l" (.cons fp rst) | .cons "--log" (.cons fp rst) =>
      go {c with logFile := some fp} rst
    | .cons "--log-stdout" rst =>
      go {c with logStdout := true} rst
    | .cons "--no-dynamatic-dot" rst =>
      go {c with noDynamaticDot := true} rst
    | .cons "--bluespec-dot" rst =>
      go {c with blueSpecDot := true} rst
    | .cons "--parse-only" rst =>
      go {c with parseOnly := true} rst
    | .cons "--oracle" (.cons fp rst) =>
      go {c with graphitiOracle := fp} rst
    | .cons "--fast" rst =>
      go {c with fast := true} rst
    | .cons "--reverse" rst =>
      go {c with reverse := true} rst
    | .cons fp rst => do
      if "-".isPrefixOf fp then throw s!"argument '{fp}' not recognised"
      if c.inputFile.isSome then throw s!"more than one input file passed"
      go {c with inputFile := some fp} rst
    | [] => do
      if c.inputFile.isNone then throw s!"no input file passed"
      return c

def helpText : String :=
  "graphiti -- v0.1.0

FORMAT
  graphiti [OPTIONS...] FILE

OPTIONS
  -h, --help          Print this help text
  -o, --output FILE   Set output file
  -l, --log FILE      Set JSON log output
  --log-stdout        Set JSON log output to STDOUT
  --no-dynamatic-dot  Don't output dynamatic DOT, instead output the raw
                      dot that is easier for debugging purposes.
  --bluespec-dot      Output a dot with BlueSpec types.
  --oracle            Path to the oracle executable.  Default is graphiti_oracle.
  --parse-only        Only parse the input without performing rewrites.
  --fast              Use the fast but unverified rewrite approach.
  --reverse           Feature flag for reverse rewriting.
"

def forkRewrites := [Fork10Rewrite.rewrite, Fork9Rewrite.rewrite, Fork8Rewrite.rewrite, Fork7Rewrite.rewrite,
                     Fork6Rewrite.rewrite, Fork5Rewrite.rewrite, Fork4Rewrite.rewrite, Fork3Rewrite.rewrite]
def combineRewrites := [CombineMux.rewrite, CombineBranch.rewrite, JoinSplitLoopCond.rewrite, JoinSplitLoopCondAlt.rewrite]
def loadRewrite := [LoadRewrite.rewrite]
def reduceRewrites := [ReduceSplitJoin.rewrite, JoinQueueLeftRewrite.rewrite, JoinQueueRightRewrite.rewrite, MuxQueueRightRewrite.rewrite]
def reduceSink := [SplitSinkRight.rewrite, SplitSinkLeft.rewrite, PureSink.rewrite]
def movePureJoin := [PureJoinLeft.rewrite, PureJoinRight.rewrite, PureSplitRight.rewrite, PureSplitLeft.rewrite]

def normaliseLoop (e : ExprHigh String (String × Nat)) : RewriteResult (ExprHigh String (String × Nat)) :=
  rewrite_fix forkRewrites e
  >>= rewrite_loop combineRewrites
  >>= (withUndo <| rewrite_loop loadRewrite ·)
  >>= rewrite_fix reduceRewrites

/--
Given a pattern, it will convert all the nodes matched by the pattern into pure nodes within that region.  It does this
in a few steps:

1. Convert most of the dataflow graph to pure, with the exception of forks and sinks.
2. Move forks as high as possible, and also move pure over joins and under sinks.  Also remove sinks.
3. Turn forks into pure.
4. Move pures to the top and bottom again, we are left with split and join nodes.
-/
def pureGeneration {n} (rw : ExprHigh String (String × Nat)) (p : Pattern String (String × Nat) n) : RewriteResult (ExprHigh String (String × Nat)) :=
  rewrite_fix (PureRewrites.specialisedPureRewrites <| nonPureMatcher p) rw
  >>= (rewrite_fix <| [ForkPure.rewrite, ForkJoin.rewrite] ++ movePureJoin ++ reduceSink)
  >>= (rewrite_fix <| PureRewrites.specialisedPureRewrites <| nonPureForkMatcher p)
  >>= (rewrite_fix <| [PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink)

def pureGenerator' (n : Nat) (g : ExprHigh String (String × Nat)) : List JSLangRewrite → Nat → RewriteResult (ExprHigh String (String × Nat))
| _, 0 => throw <| .error "No fuel"
| [], fuel+1 => pure g
| [jsRw], fuel+1 =>
  jsRw.mapToRewrite.run g
  >>= rewrite_fix ([PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink)
| jsRw :: rst, fuel+1 => do
  let rw ← jsRw.mapToRewrite.run g
  let rst ← update_state JSLang.upd rst
  let (rw, rst) ← rewrite_fix_rename rw ([PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink) JSLang.upd rst
  pureGenerator' n rw rst fuel

def pureGenerator n g js := withUndo <| pureGenerator' n g js (js.length + 1)

def eggPureGenerator {n} (fuel : Nat) (parsed : CmdArgs) (p : Pattern String (String × Nat) n) (g : ExprHigh String (String × Nat)) (st : RewriteState)
  : IO (ExprHigh String (String × Nat) × RewriteState) := do
  match fuel with
  | 0 => throw <| .userError s!"{decl_name%}: no fuel"
  | fuel+1 =>
    let jsRw ← rewriteWithEgg (eggCmd := parsed.graphitiOracle) p g
    if jsRw.length = 0 then return (g, st)
    IO.eprintln (repr jsRw)
    match pureGenerator fuel g jsRw |>.run st with
    | .ok g' st' => eggPureGenerator fuel parsed p g' st'
    | .error e st' =>
      match parsed.logFile with
      | .some lfile => IO.FS.writeFile lfile <| toString <| Lean.toJson st'.1
      | .none =>
        if parsed.logStdout then IO.println <| Lean.toJson st'.1
      IO.eprintln e
      IO.Process.exit 1

def renameAssoc (g : ExprHigh String (String × Nat)) (assoc : AssocList String (AssocList String String)) (r : RuntimeEntry) : AssocList String (AssocList String String) :=
  assoc.mapKey (λ x =>
    if x ∈ g.modules.toList.map Prod.fst then x else
    match r.renamed_input_nodes.find? x with
    | .some (.some x') => x'
    | _ => x)

def renameAssocAll assoc (rlist : RuntimeTrace) (g : ExprHigh String (String × Nat)) := rlist.foldl (renameAssoc g) assoc

def writeLogFile (parsed : CmdArgs) (st : RewriteState) := do
  match parsed.logFile with
  | .some lfile => IO.FS.writeFile lfile <| toString <| Lean.toJson st.1
  | .none =>
    if parsed.logStdout then IO.println <| Lean.toJson st.1

def runRewriter {α} (parsed : CmdArgs) (g : α) (st : RewriteState) (r : RewriteResult α) : IO (α × RewriteState) :=
  match r.run st with
  | .ok a st' => pure (a, st')
  | .error .done st' => pure (g, st')
  | .error p st' => do
    IO.eprintln p
    writeLogFile parsed st'
    IO.Process.exit 1

def runRewriter' {α} (parsed : CmdArgs) (st : RewriteState) (r : RewriteResult α) : IO (α × RewriteState) :=
  match r.run st with
  | .ok a st' => pure (a, st')
  | .error p st' => do
    IO.eprintln p
    writeLogFile parsed st'
    IO.Process.exit 1

def rewriteGraph (parsed : CmdArgs) (g : ExprHigh String (String × Nat)) (st : RewriteState)
    : IO (ExprHigh String (String × Nat) × RewriteState × RewriteState) := do
  let (rewrittenExprHigh, st) ← runRewriter parsed g st <| do
    let rewrittenExprHigh ← normaliseLoop g
    withUndo <| do
      -- let l ← errorIfDone "could not match if-statement" <| BranchPureMuxLeft.matchAllNodes rewrittenExprHigh
      -- addRuntimeEntry <| {RuntimeEntry.debugEntry (toString (repr l)) with input_graph := rewrittenExprHigh, name := "debug1"}
      let rewrittenExprHigh ← pureGeneration rewrittenExprHigh <| BranchPureMuxLeft.matchAllNodes.map (List.drop 3)
      -- addRuntimeEntry <| {RuntimeEntry.debugEntry (toString rewrittenExprHigh) with name := "debug2"}
      -- let l ← errorIfDone "could not match if-statement 2" <| BranchPureMuxRight.matchAllNodes rewrittenExprHigh
      let rewrittenExprHigh ← pureGeneration rewrittenExprHigh <| BranchPureMuxRight.matchAllNodes.map (List.drop 3)
      -- addRuntimeEntry <| {RuntimeEntry.debugEntry "" with input_graph := rewrittenExprHigh, name := "debug2"}
      -- let l ← errorIfDone "could not match the loop" <| (nonPureMatcher (toPattern LoopRewrite.boxLoopBody)) rewrittenExprHigh
      -- addRuntimeEntry <| {RuntimeEntry.debugEntry (toString (repr l)) with name := "debug3"}
      -- addRuntimeEntry <| {RuntimeEntry.debugEntry (toString rewrittenExprHigh) with name := "debug4"}
      -- pureGeneration rewrittenExprHigh <| toPattern LoopRewrite.boxLoopBody
      return rewrittenExprHigh
  let (rewrittenExprHigh, st) ← eggPureGenerator 100 parsed BranchPureMuxLeft.matchPreAndPost rewrittenExprHigh st
  let (_, st) ← runRewriter' parsed st <| addRuntimeEntry <| {RuntimeEntry.debugEntry (toString rewrittenExprHigh) with name := "debug5"}
  let (rewrittenExprHigh, st) ← eggPureGenerator 100 parsed BranchPureMuxRight.matchPreAndPost rewrittenExprHigh st
  let (rewrittenExprHigh, st) ← runRewriter parsed rewrittenExprHigh st <| withUndo <| rewrite_loop [BranchPureMuxLeft.rewrite, BranchPureMuxRight.rewrite, BranchMuxToPure.rewrite] rewrittenExprHigh
  let (rewrittenExprHigh, st) ← runRewriter parsed rewrittenExprHigh st <| withUndo <| pureGeneration rewrittenExprHigh <| toPattern (n := 0) LoopRewrite.boxLoopBody
  let (rewrittenExprHigh, st) ← eggPureGenerator 100 parsed LoopRewrite.boxLoopBodyOther rewrittenExprHigh st
  let (rewrittenExprHigh, st) ← runRewriter parsed rewrittenExprHigh st (LoopRewrite2.rewrite.run rewrittenExprHigh)
  return (rewrittenExprHigh, st, st)

def rewriteGraphAbs (parsed : CmdArgs) (g : ExprHigh String (String × Nat)) (st : RewriteState)
    : IO (ExprHigh String (String × Nat) × RewriteState × RewriteState) := do
  let (g, st) ← runRewriter parsed g st (normaliseLoop g)

  let a : Abstraction String (String × Nat) := ⟨0, λ g => LoopRewrite.boxLoopBody g >>= λ (a, _b) => pure (a, #v[]), ("M", 0)⟩
  let ((bigg, concr), st) ← runRewriter' parsed st <| a.run g
  let .some g := concr.expr |> ExprLow.higher_correct PortMapping.hashPortMapping | throw <| .userError s!"{decl_name%}: failed to higher expr"
  -- IO.print <| bigg
  let st_final := st

  let (g, st) ← runRewriter parsed g st <| pureGeneration g <| toPattern (n := 0) LoopRewrite.boxLoopBody

  let (g, st) ← eggPureGenerator 100 parsed LoopRewrite.boxLoopBodyOther' g st

  let .some subexpr@(.base pmap typ) := g.lower | throw <| .userError s!"{decl_name%}: failed to lower graph"

  -- The first concretisation replaces "M" by the "pure" block
  let newConcr : Concretisation String (String × Nat) := ⟨subexpr, concr.2⟩
  let (g, st) ← runRewriter' parsed st <| newConcr.run bigg

  let (g, st) ← runRewriter parsed g st (LoopRewrite2.rewrite.run g)

  let newConcr' : Concretisation String (String × Nat) := ⟨concr.1, typ⟩
  let (g, st) ← runRewriter parsed g st <| newConcr'.run g

  return (g, st_final, st)

def main (args : List String) : IO Unit := do
  let parsed ←
    try IO.ofExcept <| parseArgs <| args.flatMap preprocess
    catch
    | .userError s => do
      IO.eprintln ("error: " ++ s)
      IO.print helpText
      IO.Process.exit 1
    | e => throw e

  if parsed.help then
    IO.print helpText
    IO.Process.exit 0

  let fileContents ← IO.FS.readFile parsed.inputFile.get!
  let (exprHigh, assoc, name_mapping) ← IO.ofExcept fileContents.toExprHigh

  let exprHigh ← IO.ofExcept <| to_typed_exprhigh exprHigh

  let mut rewrittenExprHigh := exprHigh
  let mut st : RewriteState := default

  if !parsed.parseOnly then
    let (g', _, st') ← (if !parsed.fast then rewriteGraph else rewriteGraphAbs) parsed rewrittenExprHigh st
    let (g', st') ← if parsed.reverse then runRewriter' parsed st' <| reverseRewrites g' else pure (g', st')
    rewrittenExprHigh := g'; st := st'

  writeLogFile parsed st

  let .some g' := rewrittenExprHigh.renameModules name_mapping
    | throw <| .userError s!"{decl_name%}: failed to undo name_mapping"
  rewrittenExprHigh := g'

  /- IO.println (repr (renameAssocAll assoc st.1 rewrittenExprHigh)) -/

  let uf ← IO.ofExcept <| rewrittenExprHigh.infer_equalities ⟨∅, ∅⟩

  let l ← IO.ofExcept <|
    if parsed.noDynamaticDot then
      if parsed.blueSpecDot
      then pure rewrittenExprHigh.toBlueSpec
      else pure (toString rewrittenExprHigh)
    else dynamaticString rewrittenExprHigh uf (renameAssocAll assoc st.1 rewrittenExprHigh)

  match parsed.outputFile with
  | some ofile => IO.FS.writeFile ofile l
  | none => IO.println l
