/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.AssocList
public import Graphiti.Core.Basic

public section

open Batteries (AssocList)

namespace Graphiti

def graphitiPrefix := "_graphiti_"

/--
Mapping from Graphiti names to Dynamatic names.
-/
def dynamatic_types : AssocList String (String × List (Option Nat) × List (Option Nat)) :=
  [ ("join", ("Concat", [.none, .none], [.none]))
  , ("split", ("Split", [.none], List.replicate 2 .none))
  , ("branch", ("Branch", [.none, .some 1], List.replicate 2 .none))
  , ("fork2", ("Fork", [.none], List.replicate 2 .none))
  , ("fork3", ("Fork", [.none], List.replicate 3 .none))
  , ("fork4", ("Fork", [.none], List.replicate 4 .none))
  , ("fork5", ("Fork", [.none], List.replicate 5 .none))
  , ("fork6", ("Fork", [.none], List.replicate 6 .none))
  , ("fork7", ("Fork", [.none], List.replicate 7 .none))
  , ("fork8", ("Fork", [.none], List.replicate 8 .none))
  , ("fork9", ("Fork", [.none], List.replicate 9 .none))
  , ("fork10", ("Fork", [.none], List.replicate 10 .none))
  , ("merge2", ("Merge", List.replicate 2 .none, [.none]))
  , ("operator1", ("Operator", [.some 32], [.some 32]))
  , ("operator2", ("Operator", List.replicate 2 (.some 32), [.some 32]))
  , ("operator3", ("Operator", List.replicate 3 (.some 32), [.some 32]))
  , ("operator4", ("Operator", List.replicate 4 (.some 32), [.some 32]))
  , ("operator5", ("Operator", List.replicate 5 (.some 32), [.some 32]))
  , ("cond_operator1", ("Operator", List.replicate 1 (.some 32), [.some 1]))
  , ("cond_operator2", ("Operator", List.replicate 2 (.some 32), [.some 1]))
  , ("cond_operator3", ("Operator", List.replicate 3 (.some 32), [.some 1]))
  , ("mc", ("MC", [.some 32], [.some 32, .some 0]))
  , ("mux", ("Mux", [.some 1, .none, .none], [.none]))
  , ("input", ("Entry", [.some 0], [.some 0]))
  , ("inputNat", ("Entry", [.some 32], [.some 32]))
  , ("inputBool", ("Entry", [.some 1], [.some 1]))
  , ("outputNat0", ("Exit", [], [.some 32]))
  , ("output0", ("Exit", [], [.some 0]))
  , ("outputBool0", ("Exit", [], [.some 1]))
  , ("outputNat1", ("Exit", [.none], [.some 32]))
  , ("output1", ("Exit", [.none], [.some 0]))
  , ("outputBool1", ("Exit", [.none], [.some 1]))
  , ("outputNat2", ("Exit", [.none, .none], [.some 32]))
  , ("output2", ("Exit", [.none, .none], [.some 0]))
  , ("outputBool2", ("Exit", [.none, .none], [.some 1]))
  , ("outputNat3", ("Exit", [.none, .none, .none], [.some 32]))
  , ("output3", ("Exit", [.none, .none, .none], [.some 0]))
  , ("outputBool3", ("Exit", [.none, .none, .none], [.some 1]))
  , ("outputNat4", ("Exit", [.none, .none, .none, .none], [.some 32]))
  , ("output4", ("Exit", [.none, .none, .none, .none], [.some 0]))
  , ("outputBool4", ("Exit", [.none, .none, .none, .none], [.some 1]))
  , ("outputNat5", ("Exit", [.none, .none, .none, .none, .none], [.some 32]))
  , ("output5", ("Exit", [.none, .none, .none, .none, .none], [.some 0]))
  , ("outputBool5", ("Exit", [.none, .none, .none, .none, .none], [.some 1]))
  , ("sink", ("Sink", [.none], []))
  , ("constantNat", ("Constant", [.some 0], [.some 32]))
  , ("constantBool", ("Constant", [.some 0], [.some 1]))
  , ("initBool", ("Init", [.some 1], [.some 1]))
  , ("tag_untagger_val", ("TaggerUntagger", [.none, .none], [.none, .none]))
  , ("load", ("Operator", [.some 32, .some 32], [.some 32, .some 32]))
  ].toAssocList

def similar {α} [BEq α] (l1 l2 : List (Option α)) : Bool :=
  match l1, l2 with
  | [], [] => true
  | .cons a1 b1, .cons a2 b2 =>
    match a1, a2 with
    | .none, _ => similar b1 b2
    | _, .none => similar b1 b2
    | .some v1, .some v2 => v1 == v2 && similar b1 b2
  | _, _ => false

def dynamaticToGraphiti (s : String) (inp out : List (Option Nat)) : String :=
  match dynamatic_types.findEntryP? (λ k v => v.1 == s && similar v.2.1 inp && similar v.2.2 out) with
  | some (k, v) => k
  | none => graphitiPrefix ++ s

def graphitiToDynamatic (s : String) : String × List (Option Nat) × List (Option Nat) :=
  match dynamatic_types.find? s with
  | some s' => s'
  | none =>
    if graphitiPrefix.isPrefixOf s then (s.drop graphitiPrefix.length, [], []) else ("__unknown__"++s, [], [])

def fromDynamaticPorts {α} (pref : String) (l : List α) : PortMap String α :=
  l.foldl (λ st a => (st.1.cons ↑s!"{pref}{st.2}" a, st.2+1)) (∅, 1) |>.1

def fromDynamaticInputPorts {α} := @fromDynamaticPorts α "inp"
def fromDynamaticOutputPorts {α} := @fromDynamaticPorts α "out"

def toDynamaticPorts {α} (pref : String) (p : PortMap String α) : Nat → Option (List α)
| 0 => .some []
| n+1 => do
  let el ← p.find? ↑s!"{pref}{n}"
  let l ← toDynamaticPorts pref p n
  return l.concat el

def toDynamaticInputPorts {α} := @toDynamaticPorts α "inp"
def toDynamaticOutputPorts {α} := @toDynamaticPorts α "out"

end Graphiti
