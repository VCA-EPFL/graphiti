/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.TopRefinement

/-!
# The reading surface, checked by the build

This development is split in two directories, and the split is a claim:

* `TopSpec.lean`, `TopGates.lean`, `TopRefinement.lean` and `components/` --- the specification,
  the circuit, and the theorems.  To believe `asyncFifoGates_refines`, or any of the per-component
  theorems `X.impl_refines`, you have to read these, because their *statements* are written in
  these definitions and in nothing else.
* `ProofWriteOnly/` --- how they are proved.  Invariants, per-wire lemmas, per-connection case
  analyses, refinement machinery.  A reader who trusts the kernel never has to open any of it:
  nothing there can change what a theorem says, only whether it is proved.

That claim is not a comment, it is checked below.  `stmtClosure` takes the transitive closure of
the constants reachable from the *statement* of a theorem, unfolding the value of every
definition (so the circuit, the spec and the filters are all followed into) but never entering
the proof of a theorem (so lemmas contribute nothing).  It is taken for every theorem of
`TopRefinement.lean`; if any constant in it was declared in `ProofWriteOnly/`, the directory
names are lying and this file fails the build.

Two more properties of `components/` are checked after that: the levels are a stratification,
and an implementation names the *specifications* of its children, never their implementations.
-/

open Lean Elab Command Meta

namespace Graphiti.AsyncFifo.ReadingSurface

/-- Constants reachable from a statement: definitions are unfolded, proofs are not entered. -/
private def stmtClosure (start : Name) : CoreM NameSet := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := #[start]
  while todo.size > 0 do
    let n := todo.back!; todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut es := #[ci.type]
    if !(ci matches .thmInfo _) then
      if let some v := ci.value? then es := es.push v
    for e in es do
      for c in e.getUsedConstants do
        if !seen.contains c then todo := todo.push c
  return seen

run_cmd do
  let env ← getEnv
  let some top := env.getModuleIdx? `Graphiti.Projects.AsyncFifo.TopRefinement
    | logError "TopRefinement is not imported"
  let mut roots : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if c.isInternal || !(ci matches .thmInfo _) then continue
    if env.getModuleIdxFor? c == some top then roots := roots.push c
  let mut cl : NameSet := {}
  for r in roots do
    for c in (← liftCoreM <| stmtClosure r) do cl := cl.insert c
  let mut leaks : Array Name := #[]
  let mut n : Nat := 0
  for (c, _) in env.constants.toList do
    if c.isInternal || !(`Graphiti.AsyncFifo).isPrefixOf c || !cl.contains c then continue
    n := n + 1
    let some idx := env.getModuleIdxFor? c | continue
    if ((env.header.moduleNames[idx.toNat]!).toString.splitOn "ProofWriteOnly").length != 1 then
      leaks := leaks.push c
  unless leaks.isEmpty do
    logError m!"The statements of TopRefinement.lean depend on {leaks.size} declaration(s) in \
      ProofWriteOnly/, so the split is no longer honest.  Move them into components/ \
      (or stop the statements from mentioning them): {leaks.toList}"
  logInfo m!"reading surface: {roots.size} theorems, {n} AsyncFifo constants, none of them in \
    ProofWriteOnly/"

/-! ## The component levels

`components/levelN/` is a stratification: a component may only use components of a *strictly*
lower level.  That is what makes the tree readable top-down or bottom-up -- `level0` rests on
nothing, and nothing in `level3` can secretly depend on `level5`.  Like the split above, it is
checked rather than asserted. -/

private def levelOf (m : Name) : Option Nat := Id.run do
  let parts := m.toString.splitOn "components.level"
  if parts.length < 2 then return none
  let rest := parts[1]!
  let digits := rest.takeWhile Char.isDigit
  if digits.isEmpty then none else digits.toNat?

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name × Nat × Nat) := #[]
  for (c, ci) in env.constants.toList do
    if c.isInternal then continue
    let some i := env.getModuleIdxFor? c | continue
    let mi := env.header.moduleNames[i.toNat]!
    let some li := levelOf mi | continue
    let mut es := #[ci.type]
    if let some v := ci.value? then es := es.push v
    for e in es do
      for d in e.getUsedConstants do
        if d.isInternal then continue
        let some j := env.getModuleIdxFor? d | continue
        let mj := env.header.moduleNames[j.toNat]!
        if mi == mj then continue
        let some lj := levelOf mj | continue
        if lj ≥ li then bad := bad.push (c, d, li, lj)
  unless bad.isEmpty do
    logError m!"{bad.size} level violation(s): a component uses one at the same or a higher \
      level, so `components/` is no longer a stratification.  First: {bad[0]!}"
  logInfo m!"component levels: stratified"

/-! ## Implementations name specifications

A component's implementation is a graph over its children's *specifications*.  That is what lets
a component be reused, and each proof stay the size of one block; the gates are substituted in
only at the top, in `TopGates.lean`.  So no definition in `components/` may use another
component's `…Impl`. -/

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for (c, ci) in env.constants.toList do
    if c.isInternal then continue
    let some i := env.getModuleIdxFor? c | continue
    let mi := env.header.moduleNames[i.toNat]!
    if (levelOf mi).isNone then continue
    let some v := ci.value? | continue
    if ci matches .thmInfo _ then continue
    for d in v.getUsedConstants do
      let some j := env.getModuleIdxFor? d | continue
      let mj := env.header.moduleNames[j.toNat]!
      if mi == mj || (levelOf mj).isNone then continue
      if let .str _ s := d then
        if s.endsWith "Impl" then bad := bad.push (c, d)
  unless bad.isEmpty do
    logError m!"{bad.size} component(s) use another component's implementation instead of its \
      specification: {bad.toList}"
  logInfo m!"implementations name specifications only"

end Graphiti.AsyncFifo.ReadingSurface
