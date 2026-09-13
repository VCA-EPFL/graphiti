/-
Copyright (c) 2026 VCA Lab, EPFL.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Graphiti.Core.Graph.ExprHigh
public import Graphiti.Core.Graph.ExprHighElaborator

@[expose] public section

open Batteries (AssocList)

namespace Graphiti

instance {Ident} [ToString Ident] : Lean.ToJson (Connection Ident) where
  toJson e :=
    Lean.Json.mkObj [("output", Lean.toJson e.output), ("input", Lean.toJson e.input)]

instance {Ident} [FromString Ident] : Lean.FromJson (Connection Ident) where
  fromJson? e := do
    let out ← e.getObjVal? "output" >>= Lean.fromJson?
    let inp ← e.getObjVal? "input" >>= Lean.fromJson?
    return Connection.mk out inp

instance {Ident Typ} [ToString Ident] [Lean.ToJson Ident] [Lean.ToJson Typ] : Lean.ToJson (Graphiti.ExprHigh Ident Typ) where
  toJson e :=
    Lean.Json.mkObj [("nodes", Lean.toJson e.modules), ("edges", Lean.toJson e.connections)]

instance {Ident Typ} [FromString Ident] [Lean.FromJson Ident] [Lean.FromJson Typ] : Lean.FromJson (Graphiti.ExprHigh Ident Typ) where
  fromJson? e := do
    let modules ← e.getObjVal? "nodes" >>= Lean.fromJson?
    let connections ← e.getObjVal? "edges" >>= Lean.fromJson?
    return ExprHigh.mk modules connections

instance {Ident Typ} [ToString Ident] [Lean.ToJson Ident] [Lean.ToJson Typ] : Lean.ToJson (Graphiti.ExprHigh Ident Typ) where
  toJson e :=
    Lean.Json.mkObj [("nodes", Lean.toJson e.modules), ("edges", Lean.toJson e.connections)]

/--
We parse the graph from a json object.  One thing we want to do is normalise the identifiers of each object already, we
then save the mappings as a different AssocList.
-/
abbrev parseGraph {α} [Lean.FromJson α] (js : String) : Except String (ExprHigh String α × AssocList String String) := do
  ExprHigh.hash_portmappings <$> (Lean.Json.parse js >>= Lean.fromJson?)

abbrev printGraph {α} [Lean.ToJson α] [DecidableEq α] (graph : ExprHigh String α) (renameList : AssocList String String := .nil) (normalisePortNames : Bool := true) : String :=
  let graph := graph |>.renameModules renameList
  let graph := if normalisePortNames then graph.normaliseNames_fast |>.getD graph else graph
  graph |> Lean.toJson |> Lean.Json.pretty

end Graphiti
