/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Projects.CFG.Basic
import Graphiti.Projects.CFG.CFGNodeToDFGNode
import Graphiti.Projects.CFG.MoveRW

open Batteries (AssocList)

namespace Graphiti.CFG.Test

def cccfg' := cccfg.standardiseNames |>.get!

/- #eval cccfg' -/

/- def findNodesFromPures {Typ} [Inhabited Typ] [ToString Typ] [Repr Typ] [DecidableEq Typ] (cmp : Typ → Typ → Bool) (isPure : Typ → Bool) (pat g : ExprHigh String Typ)
 -     : RewriteResultSL (AssocList String GraphSlice) := do
 -   let new_pat ← pokeAllPures isPure pat |>.toExcept (.error "could not remove all pures")
 -   let (l, _) ← match (defaultMatcher (cmp := cmp) (normalizeIOPorts new_pat.1)) g with
 -                 | .error .done => .error (.error s!"could not match poked graph: {new_pat.1}")
 -                 | x => x
 -   let ms ← new_pat.2.toList.foldlM (fun st (k, el) => do
 -       let out ← el.input.find? ⟨.top, "in1"⟩ |>.toExcept (.error "could not find input in pure")
 -       let inp ← el.output.find? ⟨.top, "out1"⟩ |>.toExcept (.error "could not find output in pure")
 -       let res ← extendWithDFS new_pat.1 l out inp g
 -       return st.concat (k, res)
 -     ) []
 -   return ms.toAssocList
 -
 - def runWithPure (pureGen : ExprHigh String DFGandCFG → GraphSlice → RewriteResult' String DFGandCFG ExprHigh)
 -   (rw : RewriteHigh String DFGandCFG) (g : ExprHigh String DFGandCFG) : RewriteResult String DFGandCFG (AssocList String GraphSlice) := do
 -   let l ← findNodesFromPures FuzzyCompare.cmp JSType.isPure (getStructure rw.lhs) g |>.runWithState
 -   /- let g' ← l.toList.foldlM (fun g x => pureGen g x.2) g
 -    - return g' -/
 -   return l -/

/- #eval IO.println cccfg'
 - #eval IO.println <| (RewriteHigh.lower <$> TranslateNode.translate).exec cccfg' ⟨[], 0, default⟩
 - #eval match ((RewriteHigh.lower <$> TranslateNode.translate).exec cccfg'
 -                     >>= fun g => (RewriteHigh.lower <$> MoveRW.move_rw).exec g
 -                     >>= fun g => runWithPure generatePure MoveRW.normalize_rw g
 -                     >>= fun g => runWithPure generatePure MoveRW.normalize_loop_rw g
 -                     >>= fun g => runWithPure generatePure MoveRW.normalize_loop_rw2 g
 -                     /- >>= fun g => pure g -/
 -                     ) ⟨[], 0, default⟩ with
 -       | .ok e s => IO.println <| e
 -       | .error e s => do
 -         IO.println <| Lean.toJson (s.runtime_trace)
 -         /- IO.println <| (s.runtime_trace |>.getLast? |>.get! |>.output_graph) -/
 -         IO.println <| e -/

end Graphiti.CFG.Test
