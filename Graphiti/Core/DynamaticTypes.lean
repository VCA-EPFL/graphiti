/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.AssocList

public section

open Batteries (AssocList)

namespace Graphiti

def graphitiPrefix := "_graphiti_"

/--
Mapping from Graphiti names to Dynamatic names.

TODO: This needs to be a bit less ad-hoc, i.e. a true 2-way mapping with port information from Dynamatic.
-/
def dynamatic_types : AssocList String String :=
  [ ("join", "Concat")
  , ("split", "Split")
  , ("branch", "Branch")
  , ("fork2", "Fork")
  , ("fork3", "Fork")
  , ("fork4", "Fork")
  , ("fork5", "Fork")
  , ("fork", "Fork")
  , ("merge", "Merge")
  , ("merge2", "Merge")
  , ("operator1", "Operator")
  , ("operator2", "Operator")
  , ("operator3", "Operator")
  , ("operator4", "Operator")
  , ("operator5", "Operator")
  , ("mux", "Mux")
  , ("input", "Entry")
  , ("output", "Exit")
  , ("sink", "Sink")
  , ("constantNat", "Constant")
  , ("constantBool", "Constant")
  , ("initBool", "Init")
  , ("tag_untagger_val", "TaggerUntagger")
  , ("load", "Operator")
  ].toAssocList

def dynamaticToGraphiti (s : String) : String :=
  match dynamatic_types.inverse.find? s with
  | some s' => s'
  | none => graphitiPrefix ++ s

def graphitiToDynamatic (s : String) : Option String :=
  match dynamatic_types.find? s with
  | some s' => some s'
  | none =>
    if graphitiPrefix.isPrefixOf s then some (s.drop graphitiPrefix.length) else some ("__unknown__"++s)

end Graphiti
