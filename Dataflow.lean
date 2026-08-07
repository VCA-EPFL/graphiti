/-
Copyright (c) 2024-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Graph.ExprHigh
import Graphiti.Core.Dataflow.DotParser
import Graphiti.Core.Dataflow.Rewrites.LoopRewrite
import Graphiti.Core.Rewriter
import Graphiti.Core.Dataflow.DynamaticPrinter
import Graphiti.Core.Dataflow.Rewrites
import Graphiti.Core.Dataflow.JSLang
import Graphiti.Core.Dataflow.BluespecPrinter

open Batteries (AssocList)

open Graphiti

structure CmdArgs where
  outputFile : Option System.FilePath := none
  inputFile : Option System.FilePath := none
  mids : List String := []
  tagNums : Nat := 0
  logFile : Option System.FilePath := none
  pythonInterpreter : String := "uv run"
  noPython : Bool := false
  logStdout : Bool := false
  noDynamaticDot : Bool := false
  blueSpecDot : Bool := false
  parseOnly : Bool := false
  graphitiOracle : Option String := .none
  fast : Bool := false
  reverse : Bool := true
  help : Bool := false
  graphitiDir := "."
deriving Inhabited, Repr

def CmdArgs.empty : CmdArgs := {}

initialize section_num : IO.Ref Nat ← IO.mkRef 0
initialize subsection_num : IO.Ref Nat ← IO.mkRef 0
initialize status : Std.Mutex String ← Std.Mutex.new "starting"

def section_num_to_string (l : List Nat) : String :=
  l.map toString |>.intersperse "." |>.foldl (λ s x => s ++ toString x) ""

def new_section {α} (title : String) (r : RewriteState String (String × Nat))
    (f : IO (α × RewriteState String (String × Nat))) : IO (α × RewriteState String (String × Nat)) := do
  let sec ← section_num.modifyGet (λ x => (x+1, x+1))
  subsection_num.modify (λ x => 0)
  IO.println <| s!"{sec}. {title}"
  (← IO.getStdout).flush
  timeit "took" do
    let (g', r') ← f
    let rws := (r'.1.filter (λ x => x.type == .rewrite)).length - (r.1.filter (λ x => x.type == .rewrite)).length
    if rws == 1 then
      IO.print s!"  Total: {rws} rewrite "
      (← IO.getStdout).flush
    else if rws > 2 then
      IO.print s!"  Total: {rws} rewrites "
      (← IO.getStdout).flush
    return (g', r')

def new_subsection {α} (title : String) (r : RewriteState String (String × Nat))
    (f : IO (α × RewriteState String (String × Nat))) : IO (α × RewriteState String (String × Nat)) := do
  let sec ← section_num.get
  let subsec ← subsection_num.modifyGet (λ x => (x+1, x+1))
  IO.print <| s!"  {sec}.{subsec}. {title} | "
  (← IO.getStdout).flush
  timeit "took" do
    let (g', r') ← f
    let rws := (r'.1.filter (λ x => x.type == .rewrite)).length - (r.1.filter (λ x => x.type == .rewrite)).length
    if rws == 1 then
      IO.print s!"{rws} rewrite "
      (← IO.getStdout).flush
    else if rws > 2 then
      IO.print s!"{rws} rewrites "
      (← IO.getStdout).flush
    return (g', r')

/--
Split short options up into multiple options: i.e. '-ol' will become '-o -l'.
-/
def preprocess (s : String): List String :=
  if "--".isPrefixOf s then [s] else
  if "-".isPrefixOf s ∧ s.length <= 2 then [s] else
  if ¬ "-".isPrefixOf s then [s] else
  (s.toList.drop 1).map (λ x => "-" ++ toString x)

partial def parseArgs (args : List String) : Except String CmdArgs := go CmdArgs.empty args
  where
    go (c : CmdArgs) : List String → Except String CmdArgs
    | .cons "-h" _rst | .cons "--help" _rst => .ok {c with help := true}
    | .cons "-o" (.cons fp rst) | .cons "--output" (.cons fp rst) =>
      go {c with outputFile := some fp} rst
    | .cons "-l" (.cons fp rst) | .cons "--log" (.cons fp rst) =>
      go {c with logFile := some fp} rst
    | .cons "--python" (.cons fp rst) =>
      go {c with pythonInterpreter := fp} rst
    | .cons "-t" (.cons fp rst) | .cons "--tag-nums" (.cons fp rst) =>
      match fp.toNat? with
      | .some fpNum =>
        go {c with tagNums := fpNum} rst
      | .none =>
        throw s!"could not parse a number: {fp}"
    | .cons "-m" rst | .cons "--mids" rst =>
      go {c with mids := rst.takeWhile (λ x => !"-".isPrefixOf x)} <| rst.dropWhile (λ x => !"-".isPrefixOf x)
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
    | .cons "--no-reverse" rst =>
      go {c with reverse := false} rst
    | .cons "--reverse" rst =>
      go {c with reverse := true} rst
    | .cons "--no-python" rst =>
      go {c with noPython := true} rst
    | .cons "--" rst => do
      if c.inputFile.isSome then throw s!"more than one input file passed"
      return {c with inputFile := some ((rst.intersperse " " |>.foldl (· ++ ·) "") : String)}
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
  -h, --help          print this help text
  -o, --output FILE   set output file
  -l, --log FILE      set JSON log output
  -m, --mids          a list of mux IDs to transform
  -t, --tag-nums      number of tags to allocate to all taggers
  --log-stdout        set JSON log output to STDOUT
  --no-dynamatic-dot  don't output dynamatic DOT, instead output the raw
                      dot that is easier for debugging purposes
  --bluespec-dot      output a dot with BlueSpec types
  --no-python         do not run python scripts
  --no-reverse        do not undo rewrites
  --oracle            path to the oracle executable (default: graphiti_oracle)
  --parse-only        only parse the input without performing rewrites
  --python            python interpreter (default: uv run)
  --fast              use the fast but unverified rewrite approach
"

def forkRewrites := [Fork10Rewrite.rewrite, Fork9Rewrite.rewrite, Fork8Rewrite.rewrite, Fork7Rewrite.rewrite,
                     Fork6Rewrite.rewrite, Fork5Rewrite.rewrite, Fork4Rewrite.rewrite, Fork3Rewrite.rewrite]
def combineRewrites := [CombineMux.rewrite, CombineBranch.rewrite, JoinSplitLoopCond.rewrite, JoinSplitLoopCondAlt.rewrite]
def loadRewrite := [LoadRewrite.rewrite]
def reduceRewrites := [ReduceSplitJoin.rewrite, JoinQueueLeftRewrite.rewrite, JoinQueueRightRewrite.rewrite, MuxQueueRightRewrite.rewrite]
def reduceSink := [SplitSinkRight.rewrite, SplitSinkLeft.rewrite, PureSink.rewrite]
def movePureJoin := [PureJoinLeft.rewrite, PureJoinRight.rewrite, PureSplitRight.rewrite, PureSplitLeft.rewrite]

def normaliseLoop (e : ExprHigh String (String × Nat)) : RewriteResult' String (String × Nat) ExprHigh :=
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
def pureGeneration (rw : ExprHigh String (String × Nat))
    (p : Pattern String (String × Nat) 0) : RewriteResult' String (String × Nat) ExprHigh :=
  rewrite_fix (PureRewrites.specialisedPureRewrites <| nonPureMatcher p) rw
  >>= (rewrite_fix <| [ForkPure.rewrite, ForkJoin.rewrite] ++ movePureJoin ++ reduceSink)
  >>= (rewrite_fix <| PureRewrites.specialisedPureRewrites <| nonPureForkMatcher p)
  >>= (rewrite_fix <| [PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink)

def pureGenerator' (n : Nat) (g : ExprHigh String (String × Nat))
    : List JSLangRewrite → Nat → RewriteResult' String (String × Nat) ExprHigh
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

def getLastRewrite (st : RewriteState String (String × Nat)) : Option (RuntimeEntry String (String × Nat)) :=
  st.1.reverse.find? (λ x => x.type == .rewrite)

def writeLogFile (parsed : CmdArgs) (st : RewriteState String (String × Nat)) := do
  match parsed.logFile with
  | .some lfile =>
    (IO.FS.writeFile lfile <| toString <| Lean.toJson st.1)
  | .none =>
    if parsed.logStdout then IO.println <| Lean.toJson st.1

def eggPureGenerator {n} (fuel : Nat) (parsed : CmdArgs) (p : Pattern String (String × Nat) n)
    (g : ExprHigh String (String × Nat)) (st : RewriteState String (String × Nat))
  : IO (ExprHigh String (String × Nat) × RewriteState String (String × Nat)) := do
  match fuel with
  | 0 =>
    writeLogFile parsed st
    throw <| .userError s!"{decl_name%}: no fuel"
  | fuel+1 =>
    let jsRw ←
      try rewriteWithEgg (eggCmd := parsed.graphitiOracle.getD (s!"{parsed.graphitiDir}/bin/graphiti_oracle")) p g
      catch | e => writeLogFile parsed st *> throw e
    if jsRw.length = 0 then return (g, st)
    /- IO.eprintln (repr jsRw) -/
    match pureGenerator fuel g jsRw |>.run st with
    | .ok g' st' => eggPureGenerator fuel parsed p g' st'
    | .error e st' =>
      writeLogFile parsed st'
      IO.eprintln e
      IO.Process.exit 1

def renameAssoc {α} (assoc : AssocList String α × Bool) (r : RuntimeEntry String (String × Nat))
    : AssocList String α × Bool :=
  if r.type == .rewrite && assoc.2 then
    (assoc.1.mapKey (λ x =>
      match r.renamed_input_nodes.find? x with
      | .some (.some x') => x'
      | _ => x), assoc.2)
  else if r.type.stopMarker? then
    (assoc.1, false)
  else if r.type.startMarker? then
    (assoc.1, true)
  else
    assoc

def renameAssocAll {α} assoc (rlist : RuntimeTrace String (String × Nat)) := rlist.foldl (@renameAssoc α) (assoc, true) |>.1

def runRewriter {α} (parsed : CmdArgs) (g : α) (st : RewriteState String (String × Nat))
    (r : RewriteResult String (String × Nat) α) : IO (α × RewriteState String (String × Nat)) :=
  match r.run st with
  | .ok a st' => pure (a, st')
  | .error .done st' => pure (g, st')
  | .error p st' => do
    IO.eprintln p
    writeLogFile parsed st'
    IO.Process.exit 1

def runRewriter' {α} (parsed : CmdArgs) (st : RewriteState String (String × Nat))
    (r : RewriteResult String (String × Nat) α) : IO (α × RewriteState String (String × Nat)) :=
  match r.run st with
  | .ok a st' => pure (a, st')
  | .error p st' => do
    IO.eprintln p
    writeLogFile parsed st'
    IO.Process.exit 1

def rewriteGraph (parsed : CmdArgs) (g : ExprHigh String (String × Nat)) (st : RewriteState String (String × Nat))
    (initNode : String)
    : IO ((ExprHigh String (String × Nat) × RewriteState String (String × Nat)) × RewriteState String (String × Nat)) := do
  /- status.atomically λ x => do x.set "normalising the loop" -/
  let (rewrittenExprHigh, st) ← new_subsection "Normalising IO ports for the loop" st <| runRewriter parsed g st do
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
  let (rewrittenExprHigh, st) ← new_subsection "Generating a pure node for the loop body" st do
    let (rewrittenExprHigh, st) ← eggPureGenerator 100 parsed BranchPureMuxLeft.matchPreAndPost rewrittenExprHigh st
    let (_, st) ← runRewriter' parsed st <| addRuntimeEntry <|
      {RuntimeEntry.debugEntry (toString rewrittenExprHigh) with name := "debug5"}
    let (rewrittenExprHigh, st) ← eggPureGenerator 100 parsed BranchPureMuxRight.matchPreAndPost rewrittenExprHigh st
    let (rewrittenExprHigh, st) ← runRewriter parsed rewrittenExprHigh st <| withUndo <|
      rewrite_loop [BranchPureMuxLeft.rewrite, BranchPureMuxRight.rewrite, BranchMuxToPure.rewrite] rewrittenExprHigh
    /- let graph ← IO.ofExcept (toPattern (n := 0) LoopRewrite.boxLoopBody rewrittenExprHigh)
     - IO.print graph.1 -/
    let (rewrittenExprHigh, st) ← runRewriter parsed rewrittenExprHigh st <| withUndo <|
      pureGeneration rewrittenExprHigh <| toPattern <| fun g => Prod.fst <$> (LoopRewrite.boxLoopBody initNode g)
    eggPureGenerator 100 parsed (LoopRewrite.boxLoopBodyOther initNode) rewrittenExprHigh st
  let (rewrittenExprHigh, st) ← new_subsection "Applying the loop rewrite" st <|
    runRewriter parsed rewrittenExprHigh st ((LoopRewrite2.rewrite initNode).run rewrittenExprHigh)
  return ((rewrittenExprHigh, st), st)

def rewriteGraphAll (parsed : CmdArgs) (g : ExprHigh String (String × Nat)) (st : RewriteState String (String × Nat))
    : IO ((ExprHigh String (String × Nat) × RewriteState String (String × Nat)) × RewriteState String (String × Nat)) := do
  g.modules.filter (λ _ (_, (b, _)) => b == "initBool") |>.foldlM (λ ((g, st), _) k v =>
      new_section "Rewriting the main loop" st <| rewriteGraph parsed g st k
    ) ((g, st), st)

def rewriteGraphAbs (parsed : CmdArgs) (g : ExprHigh String (String × Nat)) (st : RewriteState String (String × Nat))
    : IO ((ExprHigh String (String × Nat) × RewriteState String (String × Nat)) × RewriteState String (String × Nat)) := do
  let (g, st) ← runRewriter parsed g st (normaliseLoop g)

  let a : Abstraction String (String × Nat) :=
    ⟨λ g => LoopRewrite.boxLoopBody .none g >>= λ (a, _b) => pure (a, #v[]), ("M", 0)⟩
  let ((bigg, concr), st) ← runRewriter' parsed st <| a.run g
  let .some g := concr.expr |> ExprLow.higher_correct PortMapping.hashPortMapping
    | throw <| .userError s!"{decl_name%}: failed to higher expr"
  -- IO.print <| bigg
  let st_final := st

  let (g, st) ← runRewriter parsed g st <| pureGeneration g <| toPattern <|
    fun g => Prod.fst <$> (LoopRewrite.boxLoopBody .none g)

  let (g, st) ← eggPureGenerator 100 parsed LoopRewrite.boxLoopBodyOther' g st

  let .some subexpr@(.base pmap typ) := g.lower | throw <| .userError s!"{decl_name%}: failed to lower graph"

  -- The first concretisation replaces "M" by the "pure" block
  let newConcr : Concretisation String (String × Nat) := ⟨subexpr, concr.2⟩
  let (g, st) ← runRewriter' parsed st <| newConcr.run bigg

  let (g, st) ← runRewriter parsed g st ((LoopRewrite2.rewrite .none).run g)

  let newConcr' : Concretisation String (String × Nat) := ⟨concr.1, typ⟩
  let (g, st) ← runRewriter parsed g st <| newConcr'.run g

  return ((g, st_final), st)

def print_animation : Fin 4 → String
| 0 => "[-]" | 1 => "[\\]" | 2 => "[|]" | 3 => "[/]"

def print_msg (n : Fin 4) (prev : String) : IO String := do
  let current_message ← status.atomically λ x => x.get
  let mut prev' := prev
  unless current_message == prev do
    IO.println s!"\r[🗸] {prev}"
    prev' := current_message
  IO.print s!"\r{print_animation n} {current_message}"
  (← IO.getStdout).flush
  return prev'

def main (args : List String) : IO Unit := timeit "Total: " do
  let graphiti_dir ← IO.getEnv "GRAPHITI_REPO" |>.map (·.getD ".")
  let parsed ←
    try IO.ofExcept <| parseArgs <| args.flatMap preprocess
    catch
    | .userError s => do
      IO.eprintln ("error: " ++ s)
      IO.print helpText
      IO.Process.exit 1
    | e => throw e

  let parsed := {parsed with graphitiDir := graphiti_dir}

  if parsed.help then
    IO.print helpText
    IO.Process.exit 0

  /- let (t : Task (Except IO.Error Unit)) ← IO.asTask (prio := Task.Priority.dedicated) do
   -   let mut current_message ← current_status.atomically λ x => x.get
   -   let mut n : Fin 4 := 0
   -   while ! (← IO.checkCanceled) do
   -     current_message ← print_msg n current_status current_message
   -     IO.sleep 250
   -     n := n + 1
   -   IO.println s!"\r[🗸] {current_message}\ndone" -/

  let fileContents ←
    if parsed.noPython then
      IO.FS.readFile parsed.inputFile.get!
    else
      IO.FS.withTempFile λ handle fn => do
        let _ ← IO.Process.run {
            cmd := parsed.pythonInterpreter.splitOn.head!,
            args := parsed.pythonInterpreter.splitOn.tail!.toArray
                    ++ #["--project", graphiti_dir, s!"{graphiti_dir}/scripts/dynamatic-to-graphiti.py",
                         "--output", toString fn, "--mux-ids"]
                    ++ parsed.mids.toArray
                    ++ #["--", toString parsed.inputFile.get!]
          }
        IO.FS.readFile fn

  let (exprHigh, assoc, name_mapping) ← IO.ofExcept fileContents.toExprHigh

  let exprHigh ← IO.ofExcept <| take_first_word_in_type exprHigh
  let (exprHigh, m) := to_typed_exprhigh exprHigh

  let mut rewrittenExprHigh := exprHigh
  let mut st : RewriteState String (String × Nat) :=
    {(default : RewriteState String (String × Nat)) with fresh_type := ("", m)}

  if !parsed.parseOnly then
    let ((g', _), st') ←
      (if !parsed.fast then rewriteGraphAll else rewriteGraphAbs) parsed rewrittenExprHigh st
    let (g', st') ← new_section "Reconstructing graph from pure" st' <|
      if parsed.reverse then runRewriter parsed g' st' <| reverseRewrites g' else pure (g', st')
    rewrittenExprHigh := g'; st := st'

  writeLogFile parsed st
  let name_mapping' := renameAssocAll name_mapping st.1

  let .some g' := rewrittenExprHigh.renameModules name_mapping' |>.normaliseNames_fast
    | throw <| .userError s!"{decl_name%}: failed to undo name_mapping"
  rewrittenExprHigh := g'

  let uf ← IO.ofExcept <| rewrittenExprHigh.infer_equalities ⟨∅, ∅⟩

  let l ← IO.ofExcept <|
    if parsed.noDynamaticDot || parsed.blueSpecDot then
      if parsed.blueSpecDot
      then pure (rewrittenExprHigh.toBlueSpec uf assoc)
      else pure (toString rewrittenExprHigh)
    else dynamaticString rewrittenExprHigh uf assoc

  match parsed.outputFile with
  | some ofile =>
    if parsed.noPython || parsed.noDynamaticDot || parsed.blueSpecDot then
      IO.FS.writeFile ofile l
    else
      IO.FS.withTempFile λ handle fn => do
        handle.putStr l
        handle.flush
        let _ ← IO.Process.run {
            cmd := parsed.pythonInterpreter.splitOn.head!,
            args := parsed.pythonInterpreter.splitOn.tail!.toArray
                    ++ #[ "--project", graphiti_dir, s!"{graphiti_dir}/scripts/graphiti-to-dynamatic.py",
                          "--output", toString ofile, "--tags"
                        , toString parsed.tagNums, toString fn
                        ]
          }
  | none => IO.println l
