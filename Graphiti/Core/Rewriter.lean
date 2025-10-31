/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.ExprHigh

import Lean.Data.Json

open Batteries (AssocList)

namespace Graphiti

inductive RewriteError where
| error (s : String)
| done
deriving Repr

instance : ToString RewriteError where
  toString
  | .error s => s!"error: {s}"
  | .done => s!"done"

inductive EntryType where
| rewrite
| abstraction
| concretisation
| debug
| marker (s : String)
deriving Repr, Inhabited, DecidableEq

structure RuntimeEntry where
  type : EntryType
  input_graph : ExprHigh String String
  output_graph : ExprHigh String String
  matched_subgraph : List String
  renamed_input_nodes : AssocList String (Option String)
  new_output_nodes : List String
  debug : Option String := .none
  name : Option String := .none
  deriving Repr, Inhabited

def RuntimeEntry.marker (s : String) : RuntimeEntry :=
  {(default : RuntimeEntry) with type := .marker s}

def RuntimeEntry.debugEntry (s : String) : RuntimeEntry :=
  {(default : RuntimeEntry) with type := .debug, debug := .some s }

def RuntimeEntry.startMarker? (entry : RuntimeEntry) : Bool := entry.type == .marker "rev-start"

def RuntimeEntry.stopMarker? (entry : RuntimeEntry) : Bool := entry.type == .marker "rev-stop"

instance : Lean.ToJson RuntimeEntry where
  toJson r :=
    Lean.Json.mkObj
      [ ("type", Lean.Format.pretty <| repr r.type)
      , ("name", Lean.toJson r.name)
      , ("input_graph", toString (repr r.input_graph))
      , ("output_graph", toString (repr r.output_graph))
      , ("matched_subgraph", Lean.toJson r.matched_subgraph)
      , ("renamed_input_nodes", Lean.Json.mkObj <| r.renamed_input_nodes.toList.map (λ a => (a.1, Lean.toJson a.2)))
      , ("new_output_nodes", Lean.toJson r.new_output_nodes)
      , ("debug", Lean.toJson r.debug)
      ]

@[simp] abbrev RuntimeTrace := List RuntimeEntry

structure RewriteState where
  runtime_trace : RuntimeTrace
  fresh_prefix : Nat
  fresh_type : Nat
deriving Repr, Inhabited

abbrev RewriteResult := EStateM RewriteError RewriteState

section Rewrite

variable (Ident Typ)
variable [DecidableEq Ident]
variable [DecidableEq Typ]

@[simp] abbrev Pattern n := ExprHigh Ident Typ → RewriteResult (List Ident × Vector Nat n)

structure Abstraction (n) where
  pattern : Pattern Ident Typ n
  typ : Ident

structure Concretisation where
  expr : ExprLow Ident Typ
  typ : Ident
deriving Repr, Inhabited

structure DefiniteRewrite where
  input_expr : ExprLow Ident Typ
  output_expr : ExprLow Ident Typ

structure Rewrite where
  params : Nat
  pattern : Pattern Ident Typ params
  rewrite : Vector Nat params → DefiniteRewrite Ident Typ
  transformedNodes : List (Option (PortMapping String)) := []
  addedNodes : List (PortMapping String) := []
  fresh_types : Nat := 0
  abstractions : List (Abstraction Ident Typ params) := []
  name : Option String := .none

variable {Ident Typ}
variable [Inhabited Ident]
variable [Inhabited Typ]

def ofOption {ε α σ} (e : ε) : Option α → EStateM ε σ α
| some o => pure o
| none => throw e

def liftError {α σ} : Except String α → EStateM RewriteError σ α
| .ok o => pure o
| .error s => throw (.error s)

end Rewrite

def errorIfDone {α σ} (s : String) (rw : EStateM RewriteError σ α) : EStateM RewriteError σ α :=
  try rw catch
  | .done => throw <| .error s
  | .error s' => throw <| .error s'

def generate_renaming (nameMap : AssocList String String) (fresh_prefix : String) (internals : List (InternalPort String)) :=
  go 0 nameMap ∅ internals
  where
    go (n : Nat) (nameMap : AssocList String String) (p : PortMap String (InternalPort String))
      : List (InternalPort String) → PortMap String (InternalPort String) × AssocList String String
    | (⟨.internal inst, name⟩) :: b =>
      match nameMap.find? inst with
      | some inst' => go n nameMap (p.cons ⟨.internal inst, name⟩ ⟨.internal inst', name⟩) b
      | none =>
        let inst' := "tmp_" ++ fresh_prefix ++ toString n
        let nameMap' := nameMap.cons inst inst'
        go (n+1) nameMap' (p.cons ⟨.internal inst, name⟩ ⟨.internal inst', name⟩) b
    | ⟨.top, name⟩ :: b => go n nameMap p b
    | [] => (p, nameMap)

def portmappingToNameRename' (sub : List String) (p : PortMapping String) : RewriteResult (AssocList String (Option String)) :=
  p.input.foldlM
    (λ | (a : AssocList String (Option String)), ⟨.internal lport, _⟩, ⟨.internal rport, _⟩ =>
         match a.find? lport with
         | .some x => do
           -- if lport ∈ sub && x = .none then return a
           -- if x = .some rport then return a
           -- throw (.error s!"instance names don't match: {x} != {rport} for {lport}")
           return a
         | .none => do
           if lport ∈ sub then return a.cons lport .none
           return a.cons lport (.some rport)
       | a, _, _ => pure a
       ) ∅
  >>= fun inps => p.output.foldlM
    (λ | (a : AssocList String (Option String)), ⟨.internal lport, _⟩, ⟨.internal rport, _⟩ =>
         match a.find? lport with
         | .some x => do
           -- if lport ∈ sub && x = .none then return a
           -- if x = .some rport then return a
           -- throw (.error s!"instance names don't match: {x} != {rport} for {lport}")
           return a
         | .none => do
           if lport ∈ sub then return a.cons lport .none
           return a.cons lport (.some rport)
       | a, _, _ => pure a
       ) inps

def addRuntimeEntry (rinfo : RuntimeEntry) : RewriteResult Unit := do
  let l ← EStateM.get
  EStateM.set <| ⟨l.1.concat rinfo, l.2, l.3⟩

def addRuntimeMarker (s : String) : RewriteResult Unit := do
  let l ← EStateM.get
  EStateM.set <| ⟨l.1.concat (RuntimeEntry.marker s), l.2, l.3⟩

def rmRuntimeEntry : RewriteResult Unit := do
  let l ← EStateM.get
  EStateM.set <| ⟨l.1.dropLast, l.2, l.3⟩

def updRuntimeEntry (f : RuntimeEntry → RuntimeEntry) : RewriteResult Unit := do
  let l ← EStateM.get
  let last ← ofOption (.error "last element in RewriteResult not available") <| l.1.getLast?
  EStateM.set <| ⟨l.1.dropLast.concat (f last), l.2, l.3⟩

def updFreshPrefix : RewriteResult Unit := do
  let l ← EStateM.get
  EStateM.set ⟨l.1, l.2+1, l.3⟩

def EStateM.guard {ε σ} (e : ε) (b : Bool) : EStateM ε σ Unit :=
  if b then pure () else EStateM.throw e

def mergeRenamingMaps (rmap1 rmap2 : AssocList String (Option String)) : RewriteResult (AssocList String (Option String)) :=
  ofOption (.error s!"{decl_name%}: conversion failed") <| rmap2.foldlM (λ st k v => do
    let .some v := v | return st
    let v' ← rmap1.find? v
    let st' := st.eraseAll k
    return st'.cons k v'
  ) rmap1

def renamePortMapping (i r : PortMapping String) : PortMapping String :=
  (PortMapping.mk (i.input.mapVal (λ _ => r.input.bijectivePortRenaming))
                  (i.output.mapVal (λ _ => r.output.bijectivePortRenaming)))

/--
Perform a rewrite in the graph by lowering it into an inductive expression using the right ordering, replacing it, and
then reconstructing the graph.

In the process, all names are generated again so that they are guaranteed to be fresh.  This could be unnecessary,
however, currently the low-level expression language does not remember any names.
-/
@[drunfold] def Rewrite.run' (g : ExprHigh String (String × Nat)) (rewrite : Rewrite String (String × Nat)) (norm : Bool := true)
  : RewriteResult (ExprHigh String (String × Nat)) := do

  let current_state ← EStateM.get
  let fresh_prefix := s!"rw_{current_state.fresh_prefix}_"

  -- Pattern match on the graph and extract the first list of nodes that correspond to the first subgraph.
  let (sub, types) ← rewrite.pattern g
  let def_rewrite := rewrite.rewrite types

  -- Extract the actual subgraph from the input graph using the list of nodes `sub`.
  let (g₁, g₂) ← ofOption (.error "could not extract graph") <| g.extract sub

  -- Lower the subgraph g₁ to an `ExprLow` expression.
  let e_sub ← ofOption (.error "could not lower subgraph: graph is empty") <| g₁.lower

  -- g_lower is the fully lowered graph with the sub expression that is to be replaced rearranged so that it can be
  -- pattern matched.
  let canon := ExprLow.comm_connections' g₁.connections
  let g_lower ← ofOption (.error "failed lowering of the graph: graph is empty") g.lower
  let sub' ← ofOption (.error "could not extract base information") <| sub.mapM (λ a => g.modules.find? a)
  let g_lower := canon <| ExprLow.comm_bases sub'.reverse g_lower

  addRuntimeEntry <| RuntimeEntry.mk EntryType.rewrite (g.map (λ (x, y) => x)) default sub default .nil .none rewrite.name
  updRuntimeEntry λ rw => {rw with debug := (.some <| (toString <| repr e_sub) ++ "\n\n" ++ ((toString <| repr def_rewrite.input_expr)))}

  -- beq is an α-equivalence check that returns a mapping to rename one expression into the other.  This mapping is
  -- split into the external mapping and internal mapping.
  -- addRuntimeEntry <| RuntimeEntry.mk EntryType.rewrite g default sub default default (.some s!"{repr sub}") rewrite.name
  let (ext_mapping, int_mapping) ← liftError <| def_rewrite.input_expr.weak_beq e_sub

  let comb_mapping := ext_mapping.append int_mapping |>.filterId
  -- EStateM.guard (.error "input mapping not invertible") <| comb_mapping.input.invertible
  -- EStateM.guard (.error "output mapping not invertible") <| comb_mapping.output.invertible

  updRuntimeEntry λ rw => {rw with debug := (.some (toString ext_mapping))}

  -- We rewrite the output expression external ports to match the external ports of the internal expression it is
  -- replacing.  In addition to that, we also rename the internal ports of the input_expr so that they match the
  -- internal ports of the extracted subgraph.  We apply the same renaming map to the output_expr, which will mainly
  -- just rename the external ports though.
  let e_sub_output' ← ofOption (.error "renaming failed: 1") <| def_rewrite.output_expr.renamePorts comb_mapping
  let e_sub_input ← ofOption (.error "renaming failed: 2") <| def_rewrite.input_expr.renamePorts comb_mapping

  -- `norm` is a function that canonicalises the connections of the input expression given a list of connections as the
  -- ordering guide.
  -- We use def_rewrite, because we only want to normalise fresh internal names that are introduced.
  let e_output_norm := if norm then def_rewrite.output_expr.normalisedNamesMap fresh_prefix |>.filterId else ∅

  updRuntimeEntry λ rw => {rw with debug := (.some (toString e_output_norm))}
  EStateM.guard (.error "normalisation modifies IO") <| e_sub_output'.ensureIOUnmodified e_output_norm

  let e_sub_output ← ofOption (.error "could not rename output") <| e_sub_output'.renamePorts e_output_norm

  -- We are now left with `e_sub_output` which contains an expression where the external ports are renamed, and the
  -- internal ports have not been renamed from the original graph.  `e_sub_input` where all signals have been renamed so
  -- that e_sub_input has all the same internal and external wire names, even though it won't be structurally equal to
  -- `e_sub` yet.  For that we will have to canonicalise both sides.

  -- Finally we do the actual replacement.
  let (rewritten, b) := g_lower.force_replace (canon e_sub_input) e_sub_output

  -- throw (.error s!"mods :: {repr sub'}rhs :: {repr g_lower}\n\ndep :: {repr (canon e_sub_input)}")
  EStateM.guard (.error s!"rewrite: subexpression not found in the graph: {repr g_lower}\n\n{repr (canon e_sub_input)}") b

  let out ← rewritten |> ExprLow.higher_correct PortMapping.hashPortMapping
    |> ofOption (.error s!"could not lift expression to graph: {repr rewritten}")

  let renamedNodes := rewrite.transformedNodes.map (·.map (renamePortMapping · comb_mapping))
    |>.map (·.map (renamePortMapping · e_output_norm))
    |>.map (·.map PortMapping.hashPortMapping)
  let addedNodes := rewrite.addedNodes.map (renamePortMapping · comb_mapping)
    |>.map (renamePortMapping · e_output_norm)
    |>.map PortMapping.hashPortMapping

  -- Using comb_mapping to find the portMap does not work because with rewrites where there is a single module, the name
  -- won't even appear in the rewrite.
  updRuntimeEntry <| λ _ => RuntimeEntry.mk EntryType.rewrite (g.map λ x => x.1) (out.map λ x => x.1) sub (sub.zip renamedNodes).toAssocList
    addedNodes (.some (toString renamedNodes ++ "\n\n" ++ toString addedNodes)) rewrite.name
  -- updRuntimeEntry λ rw => {rw with debug := (.some (toString e_output_norm))}
  EStateM.guard (.error s!"found duplicate node") out.modules.keysList.Nodup

  updFreshPrefix
  return out

def generateRenaming (l : List (PortMapping String)) (e : ExprLow String String) : Option (PortMapping String) :=
  (l.zip e.getPortMaps)
  |>.mapM (Function.uncurry PortMapping.generateRenamingPortMapping)
  |>.map PortMapping.combinePortMapping

def reverse_rewrite' (def_rewrite : DefiniteRewrite String String) (rinfo : RuntimeEntry) : RewriteResult (Rewrite String String) := do

  -- First we get the list of PortMappings associated with the lhs in their original (unrenamed) form.
  let lhsNodes ← ofOption (.error "reverse_rewrite: nodes not found")
    <| rinfo.matched_subgraph.mapM (λ x => rinfo.input_graph.modules.find? x |>.map Prod.fst)

  -- addRuntimeEntry <| RuntimeEntry.mk EntryType.rewrite default default default default .nil (.some <| s!"{repr }") rw.name

  -- Next we get the list of PortMappings for the rhs in their original form.  We split these up in multiple
  -- definitions so we can refer to different node groupings later on.  We first get the rhs nodes that were
  -- renamed from the lhs, then we get the fresh PortMappings that were introduced by the rewrite.
  let rhsNodes_renamed' := rinfo.renamed_input_nodes.toList.flatMap (λ (x, y) => y.toList)
  let rhsNodes_renamed ← ofOption (.error "reverse_rewrite: nodes not found")
    <| rhsNodes_renamed'.mapM (λ x => rinfo.output_graph.modules.find? x |>.map Prod.fst)
  let rhsNodes_added ← ofOption (.error "reverse_rewrite: nodes not found")
    <| rinfo.new_output_nodes.mapM (λ x => rinfo.output_graph.modules.find? x |>.map Prod.fst)
  let rhsNodes' := rhsNodes_renamed' ++ rinfo.new_output_nodes
  let rhsNodes := rhsNodes_renamed ++ rhsNodes_added

  -- -- TODO: add types into rinfo
  -- -- We run the matcher again to get the types.
  -- let (_nodes, l) ← pattern rinfo.input_graph

  -- We get the concrete lhs and rhs specialised by the types.
  -- let def_rewrite ← ofOption (.error "could not generate rewrite") <| rewrite l

  let rhs_renaming ← ofOption (.error "could not generate renaming map")
    <| generateRenaming rhsNodes def_rewrite.output_expr

  let lhs_renaming ← ofOption (.error "could not generate renaming map")
    <| generateRenaming lhsNodes def_rewrite.input_expr

  -- We generate a single renaming for correctness sake, i.e. renaming both expressions with the same renaming is
  -- correct regardless of the renaming.
  let full_renaming := rhs_renaming.squash lhs_renaming

  -- We rename the rhs and lhs expressions into the specialised forms that match the graph directly.  This allows
  -- us to apply the rewrites without renaming, allowing us to chain backwards rewrites.
  let lhs_renamed ← ofOption (.error "could not rename") <| def_rewrite.input_expr.renamePorts full_renaming
  let rhs_renamed ← ofOption (.error "could not rename") <| def_rewrite.output_expr.renamePorts full_renaming

  addRuntimeEntry <| RuntimeEntry.mk EntryType.debug default default default default .nil (.some <| s!"{repr lhs_renamed}\n\n{repr rhs_renamed}\n\n{repr full_renaming}\n\n{repr rhs_renaming}\n\n{repr lhs_renaming}") s!"rev-{rinfo.name.getD "unknown"}"

  return ({ params := 0
            pattern := λ _ => pure (rhsNodes', default),
            rewrite := λ _ => ⟨rhs_renamed, lhs_renamed⟩,
            name := s!"rev-{rinfo.name.getD "unknown"}",
            -- TODO: These dictate ordering of nodes quite strictly.
            transformedNodes := rhsNodes_renamed.map some ++ rhsNodes_added.map (λ _ => none),
            addedNodes := lhsNodes.drop rhsNodes_renamed.length
          })

/--
Generate a reverse rewrite from a rewrite and the RuntimeEntry associated with the execution.
-/
def reverse_rewrite (rw : Rewrite String String) (rinfo : RuntimeEntry) : RewriteResult (Rewrite String String) := do
  let (_nodes, l) ← rw.pattern rinfo.input_graph
  let def_rewrite := rw.rewrite l
  reverse_rewrite' def_rewrite rinfo

-- /--
-- Abstract a subgraph into a separate node.  One can imagine that the node type is then a node in the environment which is
-- referenced in the new graph.

-- These two functions do not have to have any additional proofs, because the proofs that are already present in the
-- framework should be enough.
-- -/
-- @[drunfold] def Abstraction.run (g : ExprHigh String String)
--   (abstraction : Abstraction String String) (norm : Bool := false)
--   : RewriteResult (ExprHigh String String × Concretisation String String) := do
--   let current_state ← EStateM.get
--   let fresh_prefix := s!"rw_{current_state.fresh_prefix}_"

--   -- Extract a list of modules that match the pattern.
--   let (sub, _) ← abstraction.pattern g
--   let sub := sub.pwFilter (· ≠ ·)
--   -- Extract the subgraph that matches the pattern.
--   let (g₁, _g₂) ← ofOption (.error "could not extract graph") <| g.extract sub
--   -- Lower the subgraph g₁ to ExprLow
--   let g₁_l ← ofOption (.error "could not lower subgraph: graph is empty") <| g₁.lower

--   -- g_lower is the fully lowered graph with the sub expression that is to be replaced rearranged so that it can be
--   -- pattern matched.
--   let canon := ExprLow.comm_connections' g₁.connections
--   let g_lower ← ofOption (.error "failed lowering of the graph: graph is empty") g.lower
--   let sub' ← ofOption (.error "could not extract base information") <| sub.mapM (λ a => g.modules.find? a)
--   let g_lower := canon <| ExprLow.comm_bases sub' g_lower

--   -- Here we have to make sure that the context contains a renamed version of e_sub to show equivalence to the
--   -- abstracted version, because the abstracted version has `.top` IO ports.  These are needed because of the matcher
--   -- that comes in the second phase.
--   let g₁_lc := canon <| ExprLow.comm_bases sub' g₁_l
--   let portMapping := g₁_lc.build_interface.toIdentityPortMapping'
--   let (abstracted', b) := g_lower.force_abstract g₁_lc portMapping abstraction.typ
--   EStateM.guard (.error s!"abstraction: subexpression not found in the graph: {repr g₁_l}\n\n{repr g₁_lc}") b

--   let g₁_lcr ← ofOption (.error "renaming failed: 4") <| g₁_lc.renamePorts portMapping.inverse

--   let mut abstracted := abstracted'
--   let mut portMap : AssocList String (Option String) := .nil

--   if norm then
--     let norm := abstracted.normalisedNamesMap fresh_prefix
--     abstracted ← ofOption (.error "renaming failed: 3") <| abstracted.renamePorts norm
--     portMap ← portmappingToNameRename' sub norm
--   let highered ← abstracted |>.higherSS |> ofOption (.error "Could not normalise names 1")

--   updFreshPrefix
--   return (highered, ⟨g₁_lcr, abstraction.typ⟩)

/--
Can be used to concretise the abstract node again.  Currently it assumes that it is unique in the graph (which could be
checked explicitly).  In addition to that, it currently assumes that the internal signals of the concretisation are
still fresh in the graph.
-/
@[drunfold] def Concretisation.run (g : ExprHigh String String)
  (concretisation : Concretisation String String) (norm : Bool := false) (debug := false) : RewriteResult (ExprHigh String String) := do
  let current_state ← EStateM.get
  let fresh_prefix := s!"rw_{current_state.fresh_prefix}_"

  let g_lower ← ofOption (.error "could not lower graph") <| g.lower

  -- may need to uniquify the concretisation internal connections
  let base ← ofOption (.error "Could not find base of concretisation")
    <| g_lower.findBase concretisation.typ

  let e_sub ← ofOption (.error "concretisation: could not rename ports") <| concretisation.expr.renamePorts base
  let (concr', b) := g_lower.force_concretise e_sub base concretisation.typ
  if debug then
    throw (.error s!"concr: {repr concretisation.expr}\n\n{repr e_sub}\n\n{repr base}")
  EStateM.guard (.error s!"concretisation: subexpression not found in the graph: {repr g_lower}\n\n{repr base}") b

  let mut concr := concr'
  let mut portMap : AssocList String (Option String) := .nil
  if norm then
    let norm := concr.normalisedNamesMap fresh_prefix
    concr ← ofOption (.error "renaming failed: 5") <| concr.renamePorts norm
    portMap ← portmappingToNameRename' [concretisation.typ] norm
  let concr_g ← concr.higherSS |> ofOption (.error "Could not normalise names 2")

  updFreshPrefix
  return concr_g

@[drunfold] def Rewrite.run (g : ExprHigh String (String × Nat)) (rewrite : Rewrite String (String × Nat))
  : RewriteResult (ExprHigh String (String × Nat)) := do
  -- let (g, c, _) ← rewrite.abstractions.foldlM (λ (g', c', n) a => do
  --     let (g'', c'') ← a.run (norm := true) g'
  --     return (g'', c''::c', n+1)
  --   ) (g, [], 0)
  rewrite.run' g
  -- c.foldlM (λ (g, n) (c : Concretisation String String) => do
  --   let g' ← c.run (norm := true) g
  --   return (g', n+1)) (g, 0) |>.map Prod.fst

def update_state {α} (f : AssocList String (Option String) → α → RewriteResult α) (a : α) : RewriteResult α := do
  let st ← get >>= λ a => ofOption (.error s!"{decl_name%}: could not get last element") a.1.getLast?
  f st.renamed_input_nodes a

def rewrite_loop' {α} (f : AssocList String (Option String) → α → RewriteResult α) (a : α)
    (orig_n : Nat) (g : ExprHigh String (String × Nat))
    : (rewrites : List (Rewrite String (String × Nat))) → Nat → RewriteResult (Option (ExprHigh String (String × Nat) × α))
| _, 0 | [], _ => return .none
| r :: rs, fuel' + 1 =>
  try
    let g' ← r.run g
    let a' ← update_state f a
    return (← rewrite_loop' f a' orig_n g' (r :: rs) fuel').getD (g', a')
  catch
  | .done => rewrite_loop' f a orig_n g rs orig_n
  | .error s => throw <| .error s

/--
Loops over the [rewrite] function, applying one rewrite exhaustively until moving on to the next.  Maybe we should add a
timeout for each single rewrite as well, so that infinite loops in a single rewrite means the next one can still be
started.
-/
def rewrite_loop (rewrites : List (Rewrite String (String × Nat))) (g : ExprHigh String (String × Nat)) (depth : Nat := 10000)
    : RewriteResult (ExprHigh String (String × Nat)) := do
  return (← rewrite_loop' (λ _ _ => pure Unit.unit) Unit.unit depth g rewrites depth).map (·.fst) |>.getD g

def rewrite_fix (rewrites : List (Rewrite String (String × Nat))) (g : ExprHigh String (String × Nat)) (max_depth : Nat := 10000) (depth : Nat := 10000)
    : RewriteResult (ExprHigh String (String × Nat)) := do
  match depth with
  | 0 => throw <| .error s!"{decl_name%}: ran out of fuel"
  | depth+1 =>
    match ← rewrite_loop' (λ _ _ => pure Unit.unit) Unit.unit max_depth g rewrites max_depth with
    | .some (g', _) => rewrite_fix rewrites g' max_depth depth
    | .none => return g

def rewrite_fix_rename {α} (g : ExprHigh String (String × Nat)) (rewrites : List (Rewrite String (String × Nat)))
      (upd : AssocList String (Option String) → α → RewriteResult α) (a : α)
      (max_depth : Nat := 10000) (depth : Nat := 10000)
    : RewriteResult (ExprHigh String (String × Nat) × α) := do
  match depth with
  | 0 => throw <| .error s!"{decl_name%}: ran out of fuel"
  | depth+1 =>
    match ← rewrite_loop' upd a max_depth g rewrites max_depth with
    | .some (g', a') => rewrite_fix_rename g' rewrites upd a' max_depth depth
    | .none => return (g, a)

def withUndo {α} (rw : RewriteResult α) : RewriteResult α := do
  match (addRuntimeMarker "rev-stop" *> rw) (← get) with
  | .ok a st => set st *> addRuntimeMarker "rev-start" *> pure a
  | .error .done st => set st *> addRuntimeMarker "rev-start" *> throw .done
  | .error e st => set st *> addRuntimeMarker "rev-start" *> throw e

section

variable {Ident Typ} [DecidableEq Ident]

/--
Follow an output to the next node.  A similar function could be written to
follow the input to the previous node.
-/
def followOutput' (g : ExprHigh Ident Typ) (inst : Ident) (output : InternalPort Ident) : RewriteResult (NextNode Ident Typ) := do
  let (pmap, _) ← ofOption (.error "instance not in modules")
    <| g.modules.find? inst
  let localOutputName ← ofOption (.error "port not in instance portmap")
    <| pmap.output.find? output
  let c@⟨_, localInputName⟩ ← ofOption (.error "output not in connections")
    <| g.connections.find? (λ c => c.output = localOutputName)
  let (inst, iport) ← ofOption (.error "input port not in modules")
    <| ExprHigh.findInputPort' localInputName g.modules
  ofOption (.error "instance not in modules") <| (g.modules.findEntry? inst).map (λ x => ⟨inst, iport, output.name, x.2.1, x.2.2, c⟩)

def followOutput (g : ExprHigh Ident Typ) (inst output : Ident) : Option (NextNode Ident Typ) :=
  (followOutput' g inst ⟨.top, output⟩).run' default

def followOutputFull (g : ExprHigh Ident Typ) (inst : Ident) (output : InternalPort Ident) : Option (NextNode Ident Typ) :=
  (followOutput' g inst output).run' default

/--
Follow an output to the next node.  A similar function could be written to
follow the input to the previous node.
-/
def followInput' (g : ExprHigh Ident Typ) (inst input : Ident) : RewriteResult (NextNode Ident Typ) := do
  let (pmap, _) ← ofOption (.error "instance not in modules")
    <| g.modules.find? inst
  let localInputName ← ofOption (.error "port not in instance portmap")
    <| pmap.input.find? ⟨.top, input⟩
  let c@⟨localOutputName, _⟩ ← ofOption (.error "output not in connections")
    <| g.connections.find? (λ c => c.input = localInputName)
  let (inst, iport) ← ofOption (.error "input port not in modules")
    <| ExprHigh.findOutputPort' localOutputName g.modules
  ofOption (.error "instance not in modules") <| (g.modules.findEntry? inst).map (λ x => ⟨inst, iport, input, x.2.1, x.2.2, c⟩)

def followInput (g : ExprHigh Ident Typ) (inst input : Ident) : Option (NextNode Ident Typ) :=
  (followInput' g inst input).run' default

def findType [DecidableEq Typ] (g : ExprHigh Ident Typ) (typ : Typ) : List Ident :=
  g.modules.foldl (λ l a b => if b.snd = typ then a :: l else l) []

def calcSucc (g : ExprHigh String Typ) : Option (Std.HashMap String (Array (NextNode String Typ))) :=
  g.modules.foldlM (λ succ k v => do
      let a ← v.fst.output.foldlM (λ succ' (k' v' : InternalPort String) => do
          if v'.inst.isTop then return succ'
          let out ← followOutputFull g k k'
          return succ'.push out
        ) ∅
      return succ.insert k a
    ) ∅

end

def isNonPure' typ :=
  !"split".isPrefixOf typ
  && !"join".isPrefixOf typ
  && !"pure".isPrefixOf typ
  && !"fork".isPrefixOf typ
  && !"sink".isPrefixOf typ
  && !"mux".isPrefixOf typ
  && !"branch".isPrefixOf typ

def isNonPure (g : ExprHigh String String) (node : String) : Bool :=
  match g.modules.find? node with
  | .none => false
  | .some inst => isNonPure' inst.2

def isNonPureFork' typ :=
  !"split".isPrefixOf typ
  && !"join".isPrefixOf typ
  && !"pure".isPrefixOf typ
  && !"sink".isPrefixOf typ
  && !"mux".isPrefixOf typ
  && !"branch".isPrefixOf typ

def isNonPureFork (g : ExprHigh String String) (node : String) : Bool :=
  match g.modules.find? node with
  | .none => false
  | .some inst => isNonPureFork' inst.2

-- def nonPureMatcher {n} (p : Pattern String String n) : Pattern String String n
-- | g => p g |>.map λ body => (body.1.filter (isNonPure g), #v[])

-- def nonPureForkMatcher {n} (p : Pattern String String n) : Pattern String String n
-- | g => p g |>.map λ body => (body.1.filter (isNonPureFork g), [])

-- def toPattern {α Ident Typ} (f : ExprHigh Ident Typ → RewriteResult (List Ident × α)) : Pattern Ident Typ
-- | g => f g >>= λ x => pure (x.1, [])

-- def Pattern.map {Ident Typ} (f : List Ident → List Ident) (p : Pattern Ident Typ) : Pattern Ident Typ
-- | g => p g >>= λ x => pure (f x.1, [])

-- def Pattern.nest {Ident Typ} [DecidableEq Ident] (a b : Pattern Ident Typ) : Pattern Ident Typ
-- | g => a g >>= λ x => b {g with modules := g.modules.filter λ k v => k ∈ x.1}

-- def allPattern (f : String → Bool) : Pattern String String
-- | g => pure (g.modules.filter (λ _ (_, typ) => f typ) |>.toList |>.map Prod.fst, [])

/--
Calculate a successor hashmap for a graph which includes a single root node and
a single leaf node which connects to all inputs and all outputs respectively.
It's much easier to work on this successor structure than on the unstructured
graph.
-/
def fullCalcSucc (g : ExprHigh String String) (rootNode : String := "_root_") (leafNode : String := "_leaf_") : Option (Std.HashMap String (Array String)) := do
  let succ ← calcSucc g
  let succ := succ.map λ _ b => b.map (·.inst)
  let succ := succ.insert rootNode g.inputNodes.toArray
  let succ := succ.insert leafNode ∅
  return g.outputNodes.foldl (λ succ n => succ.insert n (succ[n]?.getD #[] |>.push leafNode) ) succ

structure EvalLinkState where
  ancestor : Std.HashMap String String
  label : Std.HashMap String String
deriving Repr

def link (v w : String) (s : EvalLinkState) : EvalLinkState := {s with ancestor := s.ancestor.insert w v}

def compress (v : String) (semi : Std.HashMap String Int) (s : EvalLinkState) : Nat → EvalLinkState
| 0 => s
| n+1 => Id.run do
  let mut s' := s
  if s'.ancestor[s'.ancestor[v]!]! ≠ "" then
    s' := compress s'.ancestor[v]! semi s' n
    if semi[s'.label[s'.ancestor[v]!]!]! < semi[s'.label[v]!]! then
      s' := {s' with label := s'.label.insert v s'.label[s'.ancestor[v]!]!}
    s' := {s' with ancestor := s'.ancestor.insert v s'.ancestor[s'.ancestor[v]!]!}
  return s'

def eval (fuel : Nat) (v : String) (semi : Std.HashMap String Int) (s : EvalLinkState) : String × EvalLinkState := Id.run do
  if s.ancestor[v]! = "" then
    return (v, s)
  else
    let s' := compress v semi s fuel
    return (s'.label[v]!, s)

structure DomState where
  semi : Std.HashMap String Int
  vertex : Array String
  parent : Std.HashMap String String
  pred : Std.HashMap String (Array String)
  bucket : Std.HashMap String (Array String)
  dom : Std.HashMap String String
deriving Repr

def DomState.dfs (fuel : Nat) (succ : Std.HashMap String (Array String)) (dom : DomState) (v : String) : DomState × Nat :=
  go dom v 0 fuel
  where
    go (dom : DomState) (v : String) (n : Nat) : Nat → DomState × Nat
    | 0 => (dom, n)
    | fuel+1 => Id.run do
      let mut n' := n + 1
      let mut dom' := dom
      dom' := {dom' with semi := dom'.semi.insert v n', vertex := dom'.vertex.set! n' v}
      for w in succ[v]! do
        if dom'.semi[w]! = 0 then
          dom' := {dom' with parent := dom'.parent.insert w v }
          (dom', n') := go dom' w n' fuel
        dom' := {dom' with pred := dom'.pred.insert w (dom'.pred[w]!.push v)}
      return (dom', n')

/--
Find dominators in a graph, taken from "A fast algorithm for finding dominators
in a flowgraph" by T. Lengauer and R. E. Tarjan.

Don't ask me how the algorithm works, but it seems to output reasonable results.
-/
def findDom (fuel : Nat) (g : ExprHigh String String) := do
  let mut n := 0
  let mut dom : DomState := ⟨∅, ∅, ∅, ∅, ∅, ∅⟩
  let mut succ ← fullCalcSucc g
  let mut evalLabel : EvalLinkState := ⟨∅, ∅⟩
  -- succ := succ.insert "_leaf_" ∅

  -- Step 1
  dom := {dom with vertex := dom.vertex.push ""}
  for v in succ do
    dom := {dom with pred := dom.pred.insert v.fst ∅
                     semi := dom.semi.insert v.fst 0
                     bucket := dom.bucket.insert v.fst ∅
                     dom := dom.dom.insert v.fst ""
                     parent := dom.parent.insert v.fst ""
                     vertex := dom.vertex.push ""}
    evalLabel := {evalLabel with ancestor := evalLabel.ancestor.insert v.fst ""
                                 label := evalLabel.label.insert v.fst v.fst}
  (dom, n) := dom.dfs fuel succ "_root_"
  for i' in [0:n-1] do
    let i := n - i'
    let w := dom.vertex[i]!

    -- Step 2
    for v in dom.pred[w]! do
      let (u, evalLabel') := eval fuel v dom.semi evalLabel
      evalLabel := evalLabel'
      if dom.semi[u]! < dom.semi[w]! then
        dom := {dom with semi := dom.semi.insert w dom.semi[v]! }
    let vert : String := dom.vertex[dom.semi[w]!.toNat]!
    dom := {dom with bucket := dom.bucket.insert vert (dom.bucket[vert]!.push w)}
    evalLabel := link dom.parent[w]! w evalLabel

    -- Step 3
    for v in dom.bucket[dom.parent[w]!]! do
      let l := dom.bucket[dom.parent[w]!]!
      dom := {dom with bucket := dom.bucket.insert dom.parent[w]! (l.filter (· ≠ v)) }
      let (u, evalLabel') := eval fuel v dom.semi evalLabel
      evalLabel := evalLabel'
      dom := {dom with dom := dom.dom.insert v (if dom.semi[u]! < dom.semi[v]! then u else dom.parent[w]!)}

  -- Step 4
  for i in [2:n+1] do
    let w := dom.vertex[i]!
    if dom.dom[w]! ≠ dom.vertex[dom.semi[w]!.toNat]! then
      dom := {dom with dom := dom.dom.insert w dom.dom[dom.dom[w]!]!}
  dom := {dom with dom := dom.dom.insert "_root_" ""}
  return dom.dom

/--
Find post dominators of a node by finding dominators on the inverted graph.
-/
def findPostDom (fuel : Nat) (g : ExprHigh String String) :=
  findDom fuel g.invert

def findClosedRegion' (succ : Std.HashMap String (Array String)) (startN endN : String) : Option (List String) :=
  go (succ.size+1) ∅ [startN]
  where
    go (worklist : Nat) (visited : List String) : List String → Option (List String)
    | [] => if endN ∈ visited then some visited else none
    | x :: q => do
      match worklist with
      | 0 => none
      | w+1 =>
        let visited' := visited.cons x
        if x = endN then
          go w visited' q
        else
          let nextNodes ← succ[x]?.map (·.toList)
          if "_leaf_" ∈ nextNodes then none
          if startN ∈ nextNodes then none
          let nextNodes' := nextNodes.filter (· ∉ visited')
          go w visited' (nextNodes'.union q)

/--
Find all nodes in between two nodes by performing a DFS that checks that one has
never reached an output node.
-/
def findClosedRegion (g : ExprHigh String String) (startN endN : String) : Option (List String) := do
  let l ← findClosedRegion' (← fullCalcSucc g) startN endN
  let l' ← findClosedRegion' (← fullCalcSucc g.invert) endN startN
  return l.union l'

def extractType (s : String) : String :=
  let parts := s.splitOn " "
  parts.tail.foldl (λ a b => a ++ " " ++ b) "" |>.drop 1

def match_node (extract_type : String → RewriteResult (List String)) (nn : String) (g : ExprHigh String String)
    : RewriteResult (List String × List String) := do
  let (_map, typ) ← ofOption (.error s!"{decl_name%}: module '{nn}' not found") (g.modules.find? nn)
  let types ← extract_type typ
  return ([nn], types)

def rewrites_to_map (l : List (Rewrite String String)) : AssocList String (Rewrite String String) :=
  l.flatMap (λ x => match x.name with | .some n => [(n, x)] | _ => []) |>.toAssocList

end Graphiti
