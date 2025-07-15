/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.ExprHigh
import Graphiti.DotParser
import Graphiti.Rewriter
import Graphiti.DynamaticPrinter
import Graphiti.Rewrites
import Graphiti.JSLang

open Batteries (AssocList)

open Graphiti

structure CmdArgs where
  outputFile : Option System.FilePath
  inputFile : Option System.FilePath
  logFile : Option System.FilePath
  logStdout : Bool
  noDynamaticDot : Bool
  parseOnly : Bool
  graphitiOracle : Option String
  slow : Bool
  help : Bool
deriving Inhabited

def CmdArgs.empty : CmdArgs := default

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
    | .cons "--parse-only" rst =>
      go {c with parseOnly := true} rst
    | .cons "--oracle" (.cons fp rst) =>
      go {c with graphitiOracle := fp} rst
    | .cons "--slow" rst =>
      go {c with slow := true} rst
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
  --parse-only        Only parse the input without performing rewrites.
  --oracle            Path to the oracle executable.  Default is graphiti_oracle.
"

def forkRewrites := [Fork10Rewrite.rewrite, Fork9Rewrite.rewrite, Fork8Rewrite.rewrite, Fork7Rewrite.rewrite, Fork6Rewrite.rewrite, Fork5Rewrite.rewrite, Fork4Rewrite.rewrite, Fork3Rewrite.rewrite]
def combineRewrites := [CombineMux.rewrite, CombineBranch.rewrite, JoinSplitLoopCond.rewrite, JoinSplitLoopCondAlt.rewrite, LoadRewrite.rewrite]
def reduceRewrites := [ReduceSplitJoin.rewrite, JoinQueueLeftRewrite.rewrite, JoinQueueRightRewrite.rewrite, MuxQueueRightRewrite.rewrite]
def reduceSink := [SplitSinkRight.rewrite, SplitSinkLeft.rewrite, PureSink.rewrite]
def movePureJoin := [PureJoinLeft.rewrite, PureJoinRight.rewrite, PureSplitRight.rewrite, PureSplitLeft.rewrite]

def normaliseLoop (e : ExprHigh String) : RewriteResult (ExprHigh String) := do
  let rw ← rewrite_fix (pref := "rw_loop0") e forkRewrites
  let rw ← rewrite_loop (pref := "rw_loop1") rw combineRewrites
  let rw ← rewrite_fix (pref := "rw_loop2") rw reduceRewrites
  return rw

def allPattern (f : String → Bool) : Pattern String :=
  λ g => pure (g.modules.filter (λ _ (_, typ) => f typ) |>.toList |>.map Prod.fst, [])

def pureGeneration (rw : ExprHigh String) (p1 p2 : Pattern String) : RewriteResult (ExprHigh String) := do
  -- Convert most of the dataflow graph to pure.
  -- let rw ← rewrite_fix rw <| PureRewrites.specialisedPureRewrites LoopRewrite.nonPureMatcher
  let rw ← rewrite_fix (pref := "rw_pure1") rw <| PureRewrites.specialisedPureRewrites <| p1
  -- Move forks as high as possible, and also move pure over joins and under sinks.  Also remove sinks.
  let rw ← rewrite_fix (pref := "rw_pure2") rw <| [ForkPure.rewrite, ForkJoin.rewrite] ++ movePureJoin ++ reduceSink
  -- Turn forks into pure.
  let rw ← rewrite_fix (pref := "rw_pure3") rw <| PureRewrites.specialisedPureRewrites p2
  -- Move pures to the top and bottom again, we are left with split and join nodes.
  let rw ← rewrite_fix (pref := "rw_pure4") rw <| [PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink
  return rw

def pureGenerator' (n : Nat) (g : ExprHigh String) : List JSLangRewrite → Nat → RewriteResult (ExprHigh String)
| _, 0 => throw <| .error "No fuel"
| [], fuel+1 => pure g
| [jsRw], fuel+1 => do
  let rw ← jsRw.mapToRewrite.run s!"jsrw_{n}_{fuel}" g
  let rw ← rewrite_fix (pref := s!"jsrw3_{n}_{fuel}") rw ([PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink)
  return rw
| jsRw :: rst, fuel+1 => do
  -- addRewriteInfo {(default : RewriteInfo) with debug := .some s!"{repr jsRw}"}
  let rw ← jsRw.mapToRewrite.run s!"jsrwR_{n}_{fuel}" g
  let rst ← update_state JSLang.upd rst

  let (rw, rst) ← rewrite_fix_rename (pref := s!"jsrw2_{n}_{fuel}") rw ([PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink) JSLang.upd rst
  pureGenerator' n rw rst fuel

def pureGenerator n g js := pureGenerator' n g js (js.length + 1)

def eggPureGenerator (fuel : Nat) (parsed : CmdArgs) (p : Pattern String) (g : ExprHigh String) (st : List RewriteInfo) : IO (ExprHigh String × List RewriteInfo) := do
  match fuel with
  | 0 => throw <| .userError s!"{decl_name%}: no fuel"
  | fuel+1 =>
    let jsRw ← rewriteWithEgg (eggCmd := parsed.graphitiOracle.getD "graphiti_oracle") p g
    if jsRw.length = 0 then return (g, st)
    IO.eprintln (repr jsRw)
    match pureGenerator fuel g jsRw |>.run st with
    | .ok g' st' => eggPureGenerator fuel parsed p g' st'
    | .error e st' =>
      match parsed.logFile with
      | .some lfile => IO.FS.writeFile lfile <| toString <| Lean.toJson st'
      | .none =>
        if parsed.logStdout then IO.println <| Lean.toJson st'
      IO.eprintln e
      IO.Process.exit 1

def renameAssoc (g : ExprHigh String) (assoc : AssocList String (AssocList String String)) (r : RewriteInfo) : AssocList String (AssocList String String) :=
  assoc.mapKey (λ x =>
    if x ∈ g.modules.toList.map Prod.fst then x else
    match r.renamed_input_nodes.find? x with
    | .some (.some x') => x'
    | _ => x)

def renameAssocAll assoc (rlist : List RewriteInfo) (g : ExprHigh String) := rlist.foldl (renameAssoc g) assoc

def writeLogFile (parsed : CmdArgs) (st : List RewriteInfo) := do
  match parsed.logFile with
  | .some lfile => IO.FS.writeFile lfile <| toString <| Lean.toJson st
  | .none =>
    if parsed.logStdout then IO.println <| Lean.toJson st

def runRewriter {α} (parsed : CmdArgs) (g : α) (st : List RewriteInfo) (r : RewriteResult α) : IO (α × List RewriteInfo) :=
  match r.run st with
  | .ok a st' => writeLogFile parsed st' *> pure (a, st')
  | .error .done st' => writeLogFile parsed st' *> pure (g, st')
  | .error p st' => do
    IO.eprintln p
    writeLogFile parsed st'
    IO.Process.exit 1

def runRewriter' {α} (parsed : CmdArgs) (st : List RewriteInfo) (r : RewriteResult α) : IO (α × List RewriteInfo) :=
  match r.run st with
  | .ok a st' => writeLogFile parsed st' *> pure (a, st')
  | .error p st' => do
    IO.eprintln p
    writeLogFile parsed st'
    IO.Process.exit 1

def rewriteGraph (parsed : CmdArgs) (g : ExprHigh String) (st : List RewriteInfo)
    : IO (ExprHigh String × List RewriteInfo × List RewriteInfo) := do
  let (rewrittenExprHigh, st) ← runRewriter parsed g st (normaliseLoop g)
  let (rewrittenExprHigh, st) ← runRewriter parsed rewrittenExprHigh st (pureGeneration rewrittenExprHigh LoopRewrite.nonPureMatcher LoopRewrite.nonPureForkMatcher)
  let (rewrittenExprHigh, st) ← eggPureGenerator 100 parsed LoopRewrite.boxLoopBodyOther rewrittenExprHigh st <* writeLogFile parsed st
  let (rewrittenExprHigh, st) ← runRewriter parsed rewrittenExprHigh st (LoopRewrite2.rewrite.run "loop_rw_" rewrittenExprHigh)
  return (rewrittenExprHigh, st, st)

def rewriteGraphAbs (parsed : CmdArgs) (g : ExprHigh String) (st : List RewriteInfo)
    : IO (ExprHigh String × List RewriteInfo × List RewriteInfo) := do
  let (g, st) ← runRewriter parsed g st (normaliseLoop g)

  let a : Abstraction String := ⟨λ g => LoopRewrite.boxLoopBody g >>= λ (a, _b) => pure (a, []), "M"⟩
  let ((bigg, concr), st) ← runRewriter' parsed st <| a.run "abstr_" g
  let .some g := concr.expr.higherSS | throw <| .userError s!"{decl_name%}: failed to higher expr"
  -- IO.print <| bigg
  let st_final := st

  let (g, st) ← runRewriter parsed g st (pureGeneration g (allPattern LoopRewrite.isNonPure') (allPattern LoopRewrite.isNonPureFork'))

  let (g, st) ← eggPureGenerator 100 parsed LoopRewrite.boxLoopBodyOther' g st <* writeLogFile parsed st

  let .some subexpr@(.base pmap typ) := g.lower | throw <| .userError s!"{decl_name%}: failed to lower graph"

  -- The first concretisation replaces "M" by the "pure" block
  let newConcr : Concretisation String := ⟨subexpr, concr.2⟩
  let (g, st) ← runRewriter' parsed st <| newConcr.run "concr_" bigg

  let (g, st) ← runRewriter parsed g st (LoopRewrite2.rewrite.run "loop_rw_" g)

  let newConcr' : Concretisation String := ⟨concr.1, typ⟩
  let (g, st) ← runRewriter parsed g st <| newConcr'.run "concr2_" g

  return (g, st_final, st)

def reverseRewrites (parsed : CmdArgs) (g : ExprHigh String) (st : List RewriteInfo)
    : IO (ExprHigh String × List RewriteInfo) := do
  let some rw := st.dropLast.getLast?
    | throw <| .userError s!"{decl_name%}: failed to get last"

  let (rewrite, st) ← runRewriter' parsed st <| PureSeqComp.reverse_rewrite rw
  let (g, st) ← runRewriter' parsed st <| rewrite.run' (norm := false) "reverse_" g

  return (g, st)

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
  let (exprHigh, assoc) ← IO.ofExcept fileContents.toExprHigh

  let mut rewrittenExprHigh := exprHigh
  let mut st : List RewriteInfo := default

  if !parsed.parseOnly then
    let (g', _, st') ← (if parsed.slow then rewriteGraph else rewriteGraphAbs) parsed rewrittenExprHigh st
    let (g', st') ← reverseRewrites parsed g' st'
    rewrittenExprHigh := g'; st := st'
  -- IO.println (repr (rewrittenExprHigh.modules.toList.map Prod.fst))
  let some l :=
    if parsed.noDynamaticDot then pure (toString rewrittenExprHigh)
    else dynamaticString rewrittenExprHigh (renameAssocAll assoc st rewrittenExprHigh)
    | IO.eprintln s!"Failed to print ExprHigh: {rewrittenExprHigh}"
  -- IO.print (repr rewrittenExprHigh)

  match parsed.outputFile with
  | some ofile => IO.FS.writeFile ofile l
  | none => IO.println l
