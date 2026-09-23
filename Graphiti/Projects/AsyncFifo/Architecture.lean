/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.TopRefinement

/-!
# The architecture diagram, checked by the build

`components/architecture.dot` and `components/architecture.svg` draw what builds on what: one box
per component, one band per level, an arrow from a component to each component it uses.  A picture
that can go stale is worse than no picture, so neither file is maintained by hand.

This module recomputes the diagram from the environment -- the same constant-dependency relation
`ReadingSurface.lean` uses for its level check -- and fails the build if either file disagrees:

* the `.dot` must be exactly the text generated here;
* the `.svg` must contain exactly one `<title>` per node and per edge of that graph, which is what
  `dot` emits, so a `.dot` that was updated without re-rendering is caught too.

The arrows are the **transitive reduction**: `Bank -> Mem` is drawn, `Bank -> Gates` is not, since
it follows.  Reading downwards you get the decomposition; reading upwards, what each piece is for.

## Regenerating

When the architecture changes this file fails and writes `components/architecture.dot.actual`
beside the old one.  Then:

```
cd Graphiti/Projects/AsyncFifo/components
mv architecture.dot.actual architecture.dot
./render.sh
```

and build again.  If only the `.svg` is reported stale, `./render.sh` alone is enough.

One limitation worth knowing: the check runs when *this module* is rebuilt, which happens whenever
anything it imports changes -- that is, whenever the architecture could have changed.  Hand-editing
only the `.dot` is not noticed until the next rebuild.
-/

open Lean Elab Command

namespace Graphiti.AsyncFifo.Architecture

/-- `components/levelN/X` ↦ `(some N, X)`, the two entry points ↦ `(none, X)`, anything else ↦
`none`.  These are the modules that get a box. -/
def classify (m : Name) : Option (Option Nat × String) :=
  let s := m.toString
  let base := m.getString!
  if s.endsWith "AsyncFifo.TopSpec" || s.endsWith "AsyncFifo.TopRefinement"
     || s.endsWith "AsyncFifo.TopGates" then some (none, base)
  else
    let parts := s.splitOn "components.level"
    if parts.length < 2 then none
    else match ((parts[1]!).takeWhile Char.isDigit).toNat? with
         | some n => some (some n, base)
         | none => none

/-- What each band is for.  The membership of a band is computed; this line is the one piece of
the picture a human writes, and a component changing level shows up as a diff here. -/
def levelTitle : Option Nat → String
  | none   => "specification, the circuit as gates, and the theorems"
  | some 0 => "streams and Gray code"
  | some 1 => "timing filters and unit-delay gates"
  | some 2 => "the register-level machines the clock domains are specified by"
  | some 3 => "the flip-flop, the timed contracts, the oracle"
  | some 4 => "registers of flip-flops; next-state logic and read port"
  | some 5 => "the register file and the synchroniser"
  | some 6 => "the two register banks"
  | some 7 => "the two clock domains"
  | some 8 => "the FIFO"
  | some n => s!"level {n}"

/-- The boxes and the arrows, as the environment has them. -/
def computeGraph (env : Environment) : Array (String × Option Nat) × List (String × String) := Id.run do
  let mut lvl : Std.HashMap String (Option Nat) := {}
  let mut es : Std.HashSet (String × String) := {}
  for (c, ci) in env.constants.toList do
    if c.isInternal then continue
    let some i := env.getModuleIdxFor? c | continue
    let some (la, na) := classify env.header.moduleNames[i.toNat]! | continue
    lvl := lvl.insert na la
    let mut ts := #[ci.type]
    if let some v := ci.value? then ts := ts.push v
    for t in ts do
      for d in t.getUsedConstants do
        if d.isInternal then continue
        let some j := env.getModuleIdxFor? d | continue
        let some (lb, nb) := classify env.header.moduleNames[j.toNat]! | continue
        lvl := lvl.insert nb lb
        if na != nb then es := es.insert (na, nb)
  let succ : Std.HashMap String (Array String) :=
    es.fold (fun m (a, b) => m.insert a ((m.getD a #[]).push b)) {}
  let rec reach (fuel : Nat) (a b : String) : Bool :=
    match fuel with
    | 0 => false
    | f + 1 => (succ.getD a #[]).any (fun c => c == b || reach f c b)
  let keep := es.toList.filter (fun (a, b) =>
    !(succ.getD a #[]).any (fun c => c != b && reach 32 c b))
  let nodes := lvl.toList.toArray.qsort (fun x y =>
    match x.2, y.2 with
    | none, none => x.1 < y.1
    | none, some _ => true
    | some _, none => false
    | some a, some b => if a == b then x.1 < y.1 else a > b)
  let edges := (keep.toArray.qsort (fun x y => if x.1 == y.1 then x.2 < y.2 else x.1 < y.1)).toList
  return (nodes, edges)

/-- The `.dot` text.  Deterministic: bands from the highest level down, members and arrows sorted. -/
def renderDot (nodes : Array (String × Option Nat)) (edges : List (String × String)) : String := Id.run do
  let q := "\""
  let mut o := "// GENERATED by Graphiti/Projects/AsyncFifo/Architecture.lean -- do not edit by hand.\n"
  o := o ++ "// It is checked on every build; that file says how to regenerate it.\n"
  o := o ++ "digraph AsyncFifo {\n"
  o := o ++ "  rankdir = TB;\n  ranksep = 0.5;\n  nodesep = 0.3;\n"
  o := o ++ "  graph [fontname=" ++ q ++ "Helvetica" ++ q ++ ", fontsize=11, labeljust=l, style=filled, color=" ++ q ++ "#eef1f5" ++ q ++ "];\n"
  o := o ++ "  node  [shape=box, style=" ++ q ++ "filled,rounded" ++ q ++ ", fillcolor=" ++ q ++ "#ffffff" ++ q ++ ", color=" ++ q ++ "#5b6b7a" ++ q ++ ",\n"
  o := o ++ "         fontname=" ++ q ++ "Helvetica" ++ q ++ ", fontsize=10, margin=" ++ q ++ "0.14,0.07" ++ q ++ "];\n"
  o := o ++ "  edge  [color=" ++ q ++ "#8a97a3" ++ q ++ ", arrowsize=0.7];\n"
  -- each band is a cluster; the invisible anchor inside it, chained to its neighbours below,
  -- is what forces one rank per level (without it dot ranks by longest path and a lone level
  -- lands beside its neighbour).
  let anchor : Option Nat → String := fun l => match l with | none => "_top" | some n => s!"_l{n}"
  for l in (nodes.map (·.2)).toList.eraseDups do
    let key := match l with | none => "top" | some n => s!"l{n}"
    let head := match l with | none => "entry points" | some n => s!"level{n}"
    o := o ++ "\n  subgraph cluster_" ++ key ++ " {\n"
    o := o ++ "    label = " ++ q ++ head ++ " — " ++ levelTitle l ++ q ++ ";\n"
    o := o ++ "    " ++ anchor l ++ " [style=invis, shape=point, width=0.01, height=0.01, label=" ++ q ++ q ++ "];\n"
    for m in (nodes.filter (·.2 == l)).map (·.1) do o := o ++ "    " ++ m ++ ";\n"
    o := o ++ "    { rank=same; " ++ anchor l
    for m in (nodes.filter (·.2 == l)).map (·.1) do o := o ++ "; " ++ m
    o := o ++ " }\n"
    o := o ++ "  }\n"
  let lv := (nodes.map (·.2)).toList.eraseDups
  o := o ++ "\n  // the spine that keeps the bands in order\n"
  for (a, b) in lv.zip (lv.drop 1) do
    o := o ++ "  " ++ anchor a ++ " -> " ++ anchor b ++ " [style=invis];\n"
  o := o ++ "\n"
  for (a, b) in edges do o := o ++ "  " ++ a ++ " -> " ++ b ++ ";\n"
  o := o ++ "}\n"
  return o

run_cmd do
  let env ← getEnv
  let (nodes, edges) := computeGraph env
  let dot := renderDot nodes edges
  let dir : System.FilePath := "Graphiti/Projects/AsyncFifo/components"
  let dotPath := dir / "architecture.dot"
  let svgPath := dir / "architecture.svg"
  unless ← dotPath.pathExists do
    IO.FS.writeFile dotPath dot
    logInfo m!"wrote {dotPath} ({nodes.size} boxes, {edges.length} arrows); run components/render.sh"
    return
  let onDisk ← IO.FS.readFile dotPath
  if onDisk != dot then
    IO.FS.writeFile (dir / "architecture.dot.actual") dot
    logError m!"components/architecture.dot is out of date.  The architecture it draws is not the \
      one the build has.  The correct file has been written beside it as architecture.dot.actual; \
      `mv` it over architecture.dot and run components/render.sh."
    return
  -- the .svg must be a rendering of exactly this graph
  unless ← svgPath.pathExists do
    logError m!"components/architecture.svg is missing; run components/render.sh."
    return
  let svg ← IO.FS.readFile svgPath
  let titles := ((svg.splitOn "<title>").drop 1).filterMap (fun s =>
    match s.splitOn "</title>" with
    | t :: _ :: _ =>
      if t.startsWith "cluster_" || t.startsWith "_" || t == "AsyncFifo" then none else some t
    | _ => none)
  let want := (nodes.map (·.1)).toList ++ edges.map (fun (a, b) => a ++ "&#45;&gt;" ++ b)
  let missing := want.filter (fun t => !titles.contains t)
  if !missing.isEmpty || titles.length != want.length then
    logError m!"components/architecture.svg does not match architecture.dot ({titles.length} \
      boxes+arrows drawn, {want.length} expected; first missing: {missing.take 3}).  Run \
      components/render.sh.  (If graphviz changed how it writes <title>, this check needs updating.)"
    return
  logInfo m!"architecture diagram: {nodes.size} boxes, {edges.length} arrows, .dot and .svg current"

end Graphiti.AsyncFifo.Architecture
