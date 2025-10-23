/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Module
import Graphiti.Core.Simp
import Graphiti.Core.ExprHigh
import Graphiti.Core.AssocList.Basic
import Graphiti.Core.TypeExpr

open Batteries (AssocList)

namespace Graphiti.NatModule

@[drunfold, drcomponents] def io (T : Type) : NatModule (List T) :=
  {
    inputs := [(0, ⟨ T, λ s tt s' => s' = s.concat tt ⟩)].toAssocList,
    outputs := [(0, ⟨ T, λ s tt s' => s = tt :: s' ⟩)].toAssocList,
    init_state := λ s => s = [],
  }

@[drunfold, drcomponents]
def merge_inputs {S} (mod : NatModule S) (in1 in2 : InternalPort Nat) : Option (NatModule S)  := do
  let in1_t ← mod.inputs.find? in1
  let in2_t ← mod.inputs.find? in2
  let rmin2 := mod.inputs.erase in2
  some {
    inputs := rmin2.cons in2 ⟨ in1_t.1 × in2_t.1, λ s (v1,v2) s' =>
      ∃ s_int, in1_t.2 s v1 s_int ∧ in2_t.2 s_int v2 s'⟩,
    outputs := mod.outputs,
    internals := mod.internals,
    init_state := mod.init_state,
  }

@[drunfold, drcomponents]
def merge_outputs {S} (mod : NatModule S) (out1 out2 : InternalPort Nat) : Option (NatModule S) := do
  let out1_t ← mod.outputs.find? out1
  let out2_t ← mod.outputs.find? out2
  let rmout2 := mod.outputs.erase out2
  some {
    inputs := mod.inputs
    outputs := rmout2.cons out2 ⟨ out1_t.1 × out2_t.1, λ s (v1,v2) s' =>
      ∃ s_int, out1_t.2 s v1 s_int ∧ out2_t.2 s_int v2 s' ⟩,
    internals := mod.internals,
    init_state := mod.init_state,
  }

abbrev Named (s : String) (T : Type _) := T

@[drunfold, drcomponents] def merge T (n : Nat) (name : String := "merge") : NatModule (Named name (List T)) :=
  {
    inputs := List.range n |>.map (Prod.mk ↑·
      ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩
    ) |>.toAssocList,
    outputs := [
      (0, ⟨ T, λ oldList oldElement newList =>
        ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

-- Strictest definition of a merge, where input are totally ordered
@[drunfold, drcomponents]
def merge' T (n : Nat) (name : String := "merge'") : NatModule (Named name (List T)) :=
  {
    inputs := List.range n |>.map (Prod.mk ↑·
      ⟨ T, λ oldList newElement newList => newList = oldList.concat newElement ⟩
    ) |>.toAssocList,
    outputs := [
      (0, ⟨ T, λ oldList oldElement newList => oldList = oldElement :: newList⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

@[drunfold, drcomponents]
def cntrl_merge T (name : String := "cntrl_merge") : NatModule (Named name (List T × List Bool)) :=
  {
    inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                    newListL = oldListL.concat newElement ∧ newListR = oldListR.concat true ⟩)
              , (1, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                    newListL = oldListL.concat newElement ∧ newListR = oldListR.concat false ⟩)
              ].toAssocList,
    outputs := [ (0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                    oldElement :: newListL = oldListL ∧ newListR = oldListR ⟩)
               , (1, ⟨ Bool, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                    oldElement :: newListR = oldListR ∧ newListL = oldListL ⟩)
               ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def cntrl_merge_n T (n : Nat) (name : String := "cntrl_merge_n") : NatModule (Named name (List T × List Nat)) :=
  {
    inputs := List.range n |>.map (Prod.mk ↑· (⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                newListL = oldListL.concat newElement ∧ newListR = oldListR.concat n ⟩)) |>.toAssocList,
    outputs := [ (0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                       oldElement :: newListL = oldListL ∧ newListR = oldListR ⟩)
               , (1, ⟨ Nat, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                       oldElement :: newListR = oldListR ∧ newListL = oldListL ⟩)
               ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

-- @[drunfold] def fork T (n : Nat) : NatModule (Named name (List T)) :=
--   { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = oldList.concat newElement ⟩)].toAssocList,
--     outputs := List.range n |>.map (Prod.mk ↑· ⟨ T, λ oldList oldElement newList => oldElement :: newList = oldList⟩) |>.toAssocList
--   }

@[drunfold, drcomponents]
def fork2 T (name := "fork2") : NatModule (Named name (List T × List T)) :=
  {
    inputs := [
      (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
        newListR = oldListR.concat newElement ∧ newListL = oldListL.concat newElement ⟩),
    ].toAssocList,
    outputs := [
      (0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
        oldElement :: newListL = oldListL ∧ newListR = oldListR ⟩),
      (1, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
        oldElement :: newListR = oldListR ∧ newListL = oldListL ⟩),
    ] |>.toAssocList
    init_state := λ s => s = ⟨[], []⟩,
  }

def push_n {T} (n : Nat) (l : List (List T)) (t : T) : Option (List (List T)) :=
  List.range n |>.foldlM (λ m i => l[i]? >>= λ l' => m.set i (l'.concat t)) (List.replicate n [])

def cons_n {T} (n : Nat) (l : List (List T)) (t : T) : Option (List (List T)) :=
  l[n]? >>= λ l' => l.set n (t :: l')

@[drunfold, drcomponents] def fork T (n : Nat) : NatModule (List (List T)) :=
  {
    inputs := [(0, ⟨ T, λ ol el nl => .some nl = push_n n ol el ⟩)].toAssocList,
    outputs := List.range n |>.map (
        λ ind => (↑ind, ⟨ T, λ ol el nl =>
          .some ol = cons_n ind nl el
      ⟩)) |>.toAssocList,
    init_state := λ s => s = [],
  }

@[drunfold, drcomponents] def queue T (name := "queue") : NatModule (Named name (List T)) :=
  {
    inputs := [
      (0, ⟨ T, λ oldList newElement newList => newList = oldList.concat newElement ⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ T, λ oldList oldElement newList =>  oldElement :: newList = oldList ⟩)
    ].toAssocList
    init_state := λ s => s = [],
  }

@[drunfold, drcomponents]
def init T (default : T) (name := "init") : NatModule (Named name (List T × Bool)) :=
  {
    inputs := [
      (0, ⟨ T, λ (oldList, oldState) newElement (newList, newState) =>
        newList = oldList.concat newElement ∧ oldState = newState ⟩)
    ].toAssocList,
    outputs := [(0, ⟨ T, λ (oldList, oldState) oldElement (newList, newState) =>
      if oldState then
        oldElement :: newList = oldList ∧ oldState = newState
      else
        newList = oldList ∧ newState = true ∧ oldElement = default ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], false⟩,
  }

@[drunfold, drcomponents]
def join T T' (name := "join") : NatModule (Named name (List T × List T')) :=
  {
    inputs := [
      (0, ⟨ T, λ ol el nl => nl.1 = ol.1.concat el ∧ nl.2 = ol.2⟩),
      (1, ⟨ T', λ ol el nl => nl.2 = ol.2.concat el ∧ nl.1 = ol.1⟩),
    ].toAssocList,
    outputs := [
      (0, ⟨ T × T', λ ol el nl => ol.1 = el.1 :: nl.1 ∧ ol.2 = el.2 :: nl.2 ⟩),
    ].toAssocList
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def split T T' (name := "split") : NatModule (Named name (List T × List T')) :=
  {
    inputs := [
      (0, ⟨ T × T', λ (oldListL, oldListR) (newElementL, newElementR) (newListL, newListR) =>
        newListL = oldListL.concat newElementL ∧ newListR = oldListR.concat newElementR⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ T, λ (oldListL, oldListR) oldElementL (newListL, newListR) =>
        oldListL = oldElementL :: newListL ∧ oldListR = newListR ⟩),
      (1, ⟨ T', λ (oldListL, oldListR) oldElementR (newListL, newListR) =>
         oldListR = oldElementR :: newListR ∧ oldListL = newListL ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def branch T (name := "branch") : NatModule (Named name (List T × List Bool)) :=
  {
    inputs := [
      (0, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
       newValList = oldValList.concat val ∧ newBoolList = oldBoolList ⟩),
      (1, ⟨ Bool, λ (oldValList, oldBoolList) b (newValList, newBoolList) =>
       newValList = oldValList ∧ newBoolList = oldBoolList.concat b ⟩)
    ].toAssocList
    outputs := [
      (0, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
        val :: newValList = oldValList ∧ true :: newBoolList = oldBoolList ⟩),
      (1, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
        val :: newValList = oldValList ∧ false :: newBoolList = oldBoolList ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def mux T (name := "mux") : NatModule (Named name (List T × List T × List Bool)) :=
  {
    inputs := [
      (2, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
        newTrueList = oldTrueList.concat val ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList ⟩),
      (1, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
       newTrueList = oldTrueList ∧ newFalseList = oldFalseList.concat val ∧ newBoolList = oldBoolList ⟩),
      (0, ⟨ Bool, λ (oldTrueList, oldFalseList, oldBoolList) b (newTrueList, newFalseList, newBoolList) =>
       newTrueList = oldTrueList ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList.concat b ⟩)
    ].toAssocList
    outputs := [
      (0, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
        ∃ b, b :: newBoolList = oldBoolList
        ∧ if b then val :: newTrueList = oldTrueList ∧ newFalseList = oldFalseList
         else newTrueList = oldTrueList ∧ val :: newFalseList = oldFalseList ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], [], []⟩,
  }

@[drunfold, drcomponents]
def muxC T (name := "muxC") : NatModule (Named name (List T × List T × List Bool)) :=
  {
    inputs := [
      (2, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
        newTrueList = oldTrueList.concat val ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList ⟩),
      (1, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
         newTrueList = oldTrueList ∧ newFalseList = oldFalseList.concat val ∧ newBoolList = oldBoolList ⟩),
      (0, ⟨ Bool, λ (oldTrueList, oldFalseList, oldBoolList) b (newTrueList, newFalseList, newBoolList) =>
         newTrueList = oldTrueList ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList.concat b ⟩)
    ].toAssocList
    outputs := [
      (0, ⟨ T × Bool, λ (oldTrueList, oldFalseList, oldBoolList) (val, b) (newTrueList, newFalseList, newBoolList) =>
        b :: newBoolList = oldBoolList
        ∧ if b then val :: newTrueList = oldTrueList ∧ newFalseList = oldFalseList
        else newTrueList = oldTrueList ∧ val :: newFalseList = oldFalseList ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], [], []⟩,
  }

@[drunfold, drcomponents]
def joinC T T' T'' (name := "joinC") : NatModule (Named name (List T × List (T'× T''))) :=
  {
    inputs := [
      (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
        newListL = oldListL.concat newElement ∧ newListR = oldListR⟩),
      (1, ⟨ T' × T'', λ (oldListL, oldListR) newElement (newListL, newListR) =>
       newListR = oldListR.concat newElement ∧ newListL = oldListL⟩),
    ].toAssocList,
    outputs := [
      (0, ⟨ T × T', λ (oldListL, oldListR) (oldElementL, oldElementR) (newListL, newListR) =>
         ∃ x, oldListL =  oldElementL :: newListL ∧ oldListR = (oldElementR, x) :: newListR ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents] def empty (name := "empty") : NatModule (Named name Unit) :=
  {
    inputs := AssocList.nil,
    outputs := AssocList.nil,
    init_state := λ _ => True,
  }

@[drunfold, drcomponents] def bag T (name := "bag") : NatModule (Named name (List T)) :=
  {
    inputs := [
      (0, ⟨ T, λ oldList newElement newList => newList = oldList.concat newElement ⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

@[drunfold, drcomponents]
def tagger_untagger (TagT : Type 0) [_i: DecidableEq TagT] (T : Type 0) (name := "tagger_untagger") : NatModule (Named name (List TagT × (AssocList TagT T))) :=
  {
    inputs := [
      -- Complete computation
      (0, ⟨ TagT × T, λ (oldOrder, oldMap) (tag,el) (newOrder, newMap) =>
        -- Tag must be used, but no value ready, otherwise block:
        (tag ∈ oldOrder ∧ oldMap.find? tag = none) ∧
        newMap = oldMap.cons tag el ∧ newOrder = oldOrder⟩)
    ].toAssocList,
    outputs := [
      -- Allocate fresh tag
      (0, ⟨ TagT, λ (oldOrder, oldMap) (tag) (newOrder, newMap) =>
        -- Tag must be unused otherwise block (alternatively we
        -- could an implication to say undefined behavior):
        (tag ∉ oldOrder ∧ oldMap.find? tag = none) ∧
        newMap = oldMap ∧ newOrder = tag :: oldOrder⟩),
        -- Dequeue + free tag
      (1, ⟨ T, λ (oldorder, oldmap) el (neworder, newmap) =>
        -- tag must be used otherwise, but no value brought, undefined behavior:
        ∃ l tag , oldorder = l.cons tag ∧ oldmap.find? tag = some el ∧
        newmap = oldmap.eraseAll tag ∧ neworder = l ⟩),
    ].toAssocList,
    init_state := λ s => s = ⟨[], AssocList.nil⟩,
  }

/--
Essentially tagger + join without internal rule
-/
@[drunfold, drcomponents]
def tagger_untagger_val (TagT : Type 0) [_i: DecidableEq TagT] (T T' : Type 0) (name := "tagger_untagger_val") : NatModule (Named name (List TagT × AssocList TagT T' × List T)) :=
  {
    inputs := [
      -- Complete computation
      -- Models the input of the Cal + Untagger (coming from a previously tagged region)
      (0, ⟨ TagT × T', λ (oldOrder, oldMap, oldVal) (tag,el) (newOrder, newMap, newVal) =>
        -- Tag must be used, but no value ready, otherwise block:
        (tag ∈ oldOrder ∧ oldMap.find? tag = none) ∧
        newMap = oldMap.cons tag el ∧ newOrder = oldOrder ∧ newVal = oldVal ⟩),
      -- Enq a value to be tagged
      -- Models the input of the Tagger (coming from outside)
      (1, ⟨ T, λ (oldOrder, oldMap, oldVal) v (newOrder, newMap, newVal) =>
        newMap = oldMap ∧ newOrder = oldOrder ∧ newVal = oldVal.concat v ⟩)
    ].toAssocList,
    outputs := [
      -- Allocate fresh tag and output with value
      -- Models the output of the Tagger
      (0, ⟨ TagT × T, λ (oldOrder, oldMap, oldVal) (tag, v) (newOrder, newMap, newVal) =>
        -- Tag must be unused otherwise block (alternatively we
        -- could an implication to say undefined behavior):
        (tag ∉ oldOrder ∧ oldMap.find? tag = none) ∧
        newMap = oldMap ∧ newOrder = oldOrder.concat tag ∧ v :: newVal = oldVal⟩),
        -- Dequeue + free tag
        -- Models the output of the Cal + Untagger
      (1, ⟨ T', λ (oldorder, oldmap, oldVal) el (neworder, newmap, newVal) =>
        -- tag must be used otherwise, but no value brought, undefined behavior:
        ∃ tag , oldorder = tag :: neworder ∧ oldmap.find? tag = some el ∧
        newmap = oldmap.eraseAll tag ∧ newVal = oldVal ⟩),
    ].toAssocList,
    init_state := λ s => s = ⟨[], AssocList.nil, []⟩,
  }

@[drunfold, drcomponents]
def tagger (TagT : Type) [DecidableEq TagT] T (name := "tagger") : NatModule (Named name (List (TagT × T) × List TagT)) :=
  {
    inputs := [
      -- Allocate tag
      (0, ⟨ T, λ (oldEl, oldOrder) el (newEl, newOrder) =>
        ∃ tag, tag ∉ oldOrder ∧ newEl = oldEl.concat (tag, el) ∧ newOrder = oldOrder.concat tag ⟩),
      -- Free tag
      (1, ⟨ TagT, λ (oldEl, oldOrder) t (newEl, newOrder) =>
        newOrder = oldOrder.erase t ∧ newEl = oldEl ⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ TagT × T, λ (oldEl, oldOrder) el (newEl, newOrder) =>
        el :: newEl = oldEl ∧ newOrder = oldOrder⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def aligner TagT [DecidableEq TagT] T (name := "aligner") : NatModule (Named name (List (TagT × T) × List (TagT × T))) :=
  {
    inputs := [
      (0, ⟨ TagT × T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
          newListL = oldListL.concat newElement ⟩),
      (1, ⟨ TagT × T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
          newListR = oldListR.concat newElement ⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ (TagT × T) × (TagT × T), λ (oldListL, oldListR) oldElement (newListL, newListR) =>
         ∃ t v v', (t, v) ∈ oldListL ∧ (t, v') ∈ oldListR
           ∧ newListL = oldListL.eraseP (·.fst = t)
           ∧ newListR = oldListR.eraseP (·.fst = t)
           ∧ oldElement = ((t, v), (t, v')) ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def sink (T : Type _) (sz : Nat) (name := "sink") : NatModule (Named name Unit) :=
  {
    inputs := List.range sz |>.map (λ n => ⟨n, ⟨T, λ _ _ _ => True⟩⟩) |>.toAssocList,
    outputs := ∅,
    init_state := λ _ => True,
  }

@[drunfold, drcomponents]
def unary_op {α R} (f : α → R) (name := "unary_op"): NatModule (Named name (List α)) :=
  {
    inputs := [
      (0, ⟨ α, λ oldList newElement newList => newList = oldList.concat newElement ⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ R, λ oldList oldElement newList => ∃ a, a :: newList = oldList ∧ oldElement = f a ⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

@[drunfold, drcomponents]
def binary_op {α β R} (f : α → β → R) (name := "binary_op"): NatModule (Named name (List α × List β)) :=
  {
    inputs := [
        (0, ⟨ α, λ ol el nl => nl.1 = ol.1.concat el ∧ nl.2 = ol.2 ⟩),
        (1, ⟨ β, λ ol el nl => nl.2 = ol.2.concat el ∧ nl.1 = ol.1 ⟩),
      ].toAssocList,
    outputs := [
      (0, ⟨ R, λ ol el nl =>
        ∃ a b, ol.1 = a :: nl.1 ∧ ol.2 = b :: nl.2 ∧ el = f a b ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def ternary_op {α β γ R} (f : α → β → γ → R) (name := "ternary_op"): NatModule (Named name (List α × List β × List γ)) :=
  {
    inputs := [
      (0, ⟨ α, λ ol el nl => nl.1 = ol.1.concat el ∧ nl.2 = ol.2 ⟩),
      (1, ⟨ β, λ ol el nl => nl.2.1 = ol.2.1.concat el ∧ nl.1 = ol.1 ∧ nl.2.2 = ol.2.2 ⟩),
      (2, ⟨ γ, λ ol el nl => nl.2.2 = ol.2.2.concat el ∧ nl.1 = ol.1 ∧ nl.2.1 = ol.2.1 ⟩),
    ].toAssocList,
    outputs := [
      (0, ⟨ R, λ ol el nl =>
        ∃ a b g, ol.1 = a :: nl.1 ∧ ol.2.1 = b :: nl.2.1 ∧ ol.2.2 = g :: nl.2.2 ∧ el = f a b g ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], [], []⟩
  }

@[drunfold, drcomponents]
def constant {T} (t : T) (name := "constant") : NatModule (Named name (List Unit)) :=
  {
    inputs := [
      (0, ⟨ Unit, λ oldList newElement newList => newList = oldList.concat newElement ⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ T, λ oldList oldElement newList => ∃ a, a :: newList = oldList ∧ oldElement = t ⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

@[drunfold, drcomponents]
def sync {T S} (name := "sync") : NatModule (Named name (List S × List T)) :=
  {
    inputs := [
      (0, ⟨ S, λ (lo, ro) s (ln, rn) => lo.concat s = ln ∧ ro = rn ⟩),
      (1, ⟨ T, λ (lo, ro) t (ln, rn) => ro.concat t = rn ∧ lo = ln ⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ T, λ (lo, ro) t (ln, rn) => ∃ s, lo = s :: ln ∧ ro = t :: rn ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def sync1 {T S} (name := "sync1") : NatModule (Named name (Option S × List T)) :=
  {
    inputs := [
      (0, ⟨ S, λ (lo, ro) s (ln, rn) => lo = none ∧ ln = some s ∧ ro = rn ⟩),
      (1, ⟨ T, λ (lo, ro) t (ln, rn) => ro.concat t = rn ∧ lo = ln ⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ T, λ (lo, ro) t (ln, rn) => ∃ s, lo = some s ∧ ln = none ∧ ro = t :: rn ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨none, []⟩,
  }

@[drunfold, drcomponents]
def dsync {T S} (f : T → S) (name := "dsync") : NatModule (Named name (List S × List T)) :=
  {
    inputs := [
        (0, ⟨ T, λ (lo, ro) t (ln, rn) => lo.concat (f t) = ln ∧ ro.concat t = rn ⟩),
      ].toAssocList,
    outputs := [
      (0, ⟨ S, λ (lo, ro) s (ln, rn) => lo = s :: ln ⟩),
      (1, ⟨ T, λ (lo, ro) t (ln, rn) => ro = t :: rn ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def dsyncU {T} (name := "dsyncU") : NatModule (Named name (List Unit × List T)) :=
  dsync (λ _ => ())

@[drunfold, drcomponents]
def dsync1 {T S} (f : T → S) (name := "dsync1") : NatModule (Named name (Option S × List T)) :=
  {
    inputs := [
      (0, ⟨ T, λ (lo, ro) t (ln, rn) => lo = none ∧ ln = some (f t) ∧ ro.concat t = rn ⟩),
    ].toAssocList,
    outputs := [
      (0, ⟨ S, λ (lo, ro) s (ln, rn) => lo = some s ∧ ln = none ⟩),
      (1, ⟨ T, λ (lo, ro) t (ln, rn) => ro = t :: rn ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨none, []⟩,
  }

@[drunfold, drcomponents]
def dsync1U {T} (name := "dsync1U") : NatModule (Named name (Option Unit × List T)) :=
  dsync1 (λ _ => ()) (name := name)

@[drunfold, drcomponents]
def load S T (name := "load") : NatModule (Named name (List S × List T)) :=
  {
    inputs := [
      (0, ⟨S, λ before el after => after.1 = before.1.concat el ∧ after.2 = before.2⟩),
      (1, ⟨T, λ before el after => after.2 = before.2.concat el ∧ after.1 = before.1⟩),
    ].toAssocList,
    outputs := [
      (0, ⟨S, λ before el after => el :: after.1 = before.1 ∧ after.2 = before.2⟩),
      (1, ⟨T, λ before el after => el :: after.2 = before.2 ∧ after.1 = before.1⟩),
    ].toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drunfold, drcomponents]
def pure {S T} (f : S → T) (name := "pure") : NatModule (Named name (List T)) :=
  {
    inputs := [
      (0, ⟨S, λ before el after => after = before.concat (f el)⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨T, λ before el after => el :: after = before⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

section
variable {T} [Inhabited T]
opaque polymorphic_add : T → T → T
opaque polymorphic_sub : T → T → T
opaque polymorphic_mult : T → T → T
opaque polymorphic_div : T → T → T
opaque polymorphic_shift_left : T → T → T
opaque polymorphic_getelemptr : T → T → T → T

variable (T) in
opaque op0_function : String → T

opaque op1_function {T₁} : String → T₁ → T
opaque op2_function {T₁ T₂} : String → T₁ → T₂ → T
opaque op3_function {T₁ T₂ T₃} : String → T₁ → T₂ → T₃ → T

opaque constant_a : T
opaque constant_b : T
opaque constant_c : T
opaque constant_d : T
opaque constant_e : T
opaque constant_f : T
opaque constant_g : T
end

def operator1 T₁ T [Inhabited T] (s : String) :=
  unary_op (name := s!"operator1 {s}") (@op1_function T _ T₁ s)

def operator2 T₁ T₂ T [Inhabited T] (s : String) :=
  binary_op (name := s!"operator2 {s}") (@op2_function T _ T₁ T₂ s)

def operator3 T₁ T₂ T₃ T [Inhabited T] (s : String) :=
  ternary_op (name := s!"operator3 {s}") (@op3_function T _ T₁ T₂ T₃ s)

def cast S T [Inhabited T] :=
  unary_op (name := s!"cast") (@op1_function T _ S "cast")

namespace FixedSize

def BoundedList T n := { ls : List T // ls.length <= n }

def BoundedList.empty T n : BoundedList T n := ⟨[], by simpa⟩

@[drunfold, drcomponents]
def join T T' n : NatModule (BoundedList T n × BoundedList T' n) :=
  {
    inputs := [
      (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
        newListL.val = newElement :: oldListL.val ∧ newListR = oldListR ⟩),
      (1, ⟨ T', λ (oldListL, oldListR) newElement (newListL, newListR) =>
        newListR.val = newElement :: oldListR.val ∧ newListL = oldListL⟩),
    ].toAssocList,
    outputs := [
      (0, ⟨ T × T', λ (oldListL, oldListR) (oldElementL, oldElementR) (newListL, newListR) =>
        oldListL.val = newListL.val.concat oldElementL
        ∧ oldListR.val = newListR.val.concat oldElementR ⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨BoundedList.empty T n, BoundedList.empty T' n⟩,
  }

@[drunfold, drcomponents]
def joinL T T' T'' n : NatModule (BoundedList (T × T') n × BoundedList T'' n) :=
  {
    inputs := [
      (0, ⟨ T × T', λ (oldListL, oldListR) newElement (newListL, newListR) =>
        newListL.val = newElement :: oldListL.val ∧ newListR = oldListR ⟩),
      (1, ⟨ T'', λ (oldListL, oldListR) newElement (newListL, newListR) =>
        newListR.val = newElement :: oldListR.val ∧ newListL = oldListL⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨ T × T' × T'', λ (oldListL, oldListR) (oldElementL₁, oldElementL₂, oldElementR) (newListL, newListR) =>
        oldListL.val = newListL.val.concat (oldElementL₁, oldElementL₂)
        ∧ oldListR.val = newListR.val.concat oldElementR⟩)
    ].toAssocList,
    init_state := λ s => s = ⟨
      BoundedList.empty (T × T') n,
      BoundedList.empty T'' n
    ⟩,
  }

end FixedSize

end Graphiti.NatModule

namespace Graphiti.StringModule

@[drunfold, drcomponents] def empty := NatModule.empty |>.stringify

@[drunfold, drcomponents] def bag T := NatModule.bag T |>.stringify

@[drunfold, drcomponents] def merge T n := NatModule.merge T n |>.stringify

@[drunfold, drcomponents] def merge' T n := NatModule.merge' T n |>.stringify

@[drunfold, drcomponents] def fork T n := NatModule.fork T n |>.stringify

@[drunfold, drcomponents] def cntrl_merge T := NatModule.cntrl_merge T |>.stringify

@[drunfold, drcomponents] def queue T := NatModule.queue T |>.stringify

@[drunfold, drcomponents] def fork2 T := NatModule.fork2 T|>.stringify

@[drunfold, drcomponents] def join T T' := NatModule.join T T' |>.stringify

@[drunfold, drcomponents] def split T T' := NatModule.split T T' |>.stringify

@[drunfold, drcomponents] def sink T n := NatModule.sink T n |>.stringify

@[drunfold, drcomponents] def branch T := NatModule.branch T |>.stringify
  -- |>.mapIdent (λ | 0 => "val" | _ => "cond") (λ | 0 => "true" | _ => "false")

@[drunfold, drcomponents] def mux T := NatModule.mux T
  |>.stringify

@[drunfold, drcomponents] def tagger TagT [DecidableEq TagT] T := NatModule.tagger TagT T
  |>.stringify

@[drunfold, drcomponents] def aligner TagT [DecidableEq TagT] T := NatModule.aligner TagT T
  |>.stringify

@[drunfold, drcomponents] def unary_op {α R} (f : α → R) := NatModule.unary_op f
  |>.stringify

@[drunfold, drcomponents] def binary_op {α β R} (f : α → β → R) := NatModule.binary_op f
  |>.stringify

@[drunfold, drcomponents] def init T default := NatModule.init T default |>.stringify

@[drunfold, drcomponents] def constant {T} (t : T) := NatModule.constant t |>.stringify

@[drunfold, drcomponents] def sync {T S} := @NatModule.sync T S |>.stringify

@[drunfold, drcomponents] def sync1 {T S} := @NatModule.sync1 T S |>.stringify

@[drunfold, drcomponents] def dsync {T S} f := @NatModule.dsync T S f |>.stringify

@[drunfold, drcomponents] def dsyncU {T} := @NatModule.dsyncU T |>.stringify

@[drunfold, drcomponents] def dsync1 {T S} f := @NatModule.dsync1 T S f |>.stringify

@[drunfold, drcomponents] def dsync1U {T} := @NatModule.dsync1U T |>.stringify

@[drunfold, drcomponents] def pure {S T} f := @NatModule.pure S T f |>.stringify

@[drunfold, drcomponents] def operator1 T₁ T [Inhabited T] s := NatModule.operator1 T₁ T s |>.stringify

@[drunfold, drcomponents] def operator2 T₁ T₂ T [Inhabited T] s := NatModule.operator2 T₁ T₂ T s |>.stringify

@[drunfold, drcomponents] def operator3 T₁ T₂ T₃ T [Inhabited T] s := NatModule.operator3 T₁ T₂ T₃ T s |>.stringify

@[drunfold, drcomponents] def cast S T [Inhabited T] := NatModule.cast S T |>.stringify

@[drunfold, drcomponents] def load S T := NatModule.load S T |>.stringify

@[drunfold, drcomponents] def tagger_untagger_val TagT [DecidableEq TagT] T T' :=
  NatModule.tagger_untagger_val TagT T T' |>.stringify

-- -- Associate the above modules with a String name to be used in the matcher of each rewrite
-- -- Essentially, those constitute our primitives
-- def ε (Tag : Type) [DecidableEq Tag] (T : Type) [Inhabited T] : Env :=
--   [ ("Join", ⟨_, StringModule.join T T⟩)
--   , ("TaggedJoin", ⟨_, StringModule.join Tag T⟩)

--   , ("Split", ⟨_, StringModule.split T T⟩)
--   , ("TaggedSplit", ⟨_, StringModule.split Tag T⟩)

--   , ("Merge", ⟨_, StringModule.merge T 2⟩)
--   , ("TaggedMerge", ⟨_, StringModule.merge (Tag × T) 2⟩)

--   , ("Sink", ⟨_, StringModule.sink T 1⟩)
--   , ("TaggedSink", ⟨_, StringModule.sink Tag 1⟩)

--   -- , ("Fork", ⟨_, StringModule.fork T 2⟩)
--   -- , ("Fork3", ⟨_, StringModule.fork T 3⟩)
--   -- , ("Fork4", ⟨_, StringModule.fork T 4⟩)
--   -- , ("Fork5", ⟨_, StringModule.fork T 5⟩)
--   -- , ("Fork6", ⟨_, StringModule.fork T 6⟩)
--   -- , ("TagggedFork", ⟨_, StringModule.fork (Tag × T) 2⟩)

--   , ("CntrlMerge", ⟨_, StringModule.cntrl_merge T⟩)
--   , ("TagggedCntrlMerge", ⟨_, StringModule.cntrl_merge (Tag × T)⟩)

--   , ("Branch", ⟨_, StringModule.branch T⟩)
--   , ("BranchC", ⟨_, StringModule.branch Unit⟩)
--   , ("TaggedBranch", ⟨_, StringModule.branch (Tag × T)⟩)

--   , ("Mux", ⟨_, StringModule.mux T⟩)
--   , ("MuxC", ⟨_, StringModule.mux Unit⟩)
--   , ("TagggedMux", ⟨_, StringModule.mux (Tag × T)⟩)

--   , ("Buffer", ⟨_, StringModule.queue T⟩)
--   , ("BufferC", ⟨_, StringModule.queue Unit⟩)
--   , ("BufferB", ⟨_, StringModule.queue Bool⟩)
--   , ("TagggedBuffer", ⟨_, StringModule.queue (Tag × T)⟩)

--   , ("Bag", ⟨_, StringModule.bag (Tag × T)⟩)

--   , ("Aligner", ⟨_, StringModule.aligner Tag T⟩)
--   , ("TaggerCntrlAligner", ⟨_, StringModule.tagger_untagger_val Tag T T⟩)

--   -- , ("ConstantA", ⟨_, StringModule.constant (@constant_a T)⟩)
--   -- , ("ConstantB", ⟨_, StringModule.constant (@constant_b T)⟩)
--   -- , ("ConstantC", ⟨_, StringModule.constant (@constant_c T)⟩)
--   -- , ("ConstantD", ⟨_, StringModule.constant (@constant_d T)⟩)
--   -- , ("ConstantE", ⟨_, StringModule.constant (@constant_e T)⟩)
--   -- , ("ConstantF", ⟨_, StringModule.constant (@constant_f T)⟩)
--   -- , ("ConstantG", ⟨_, StringModule.constant (@constant_g T)⟩)

--   -- , ("Add", ⟨_, StringModule.binary_op (@polymorphic_add T _)⟩)
--   -- , ("Mul", ⟨_, StringModule.binary_op (@polymorphic_mult T _)⟩)
--   -- , ("Div", ⟨_, StringModule.binary_op (@polymorphic_div T _)⟩)
--   -- , ("Shl", ⟨_, StringModule.binary_op (@polymorphic_shift_left T _)⟩)
--   -- , ("Sub", ⟨_, StringModule.binary_op (@polymorphic_sub T _)⟩)
--   ].toAssocList

@[drunfold, drcomponents] def muxC T := NatModule.muxC T |>.stringify

@[drunfold, drcomponents] def joinC T T' T'' := NatModule.joinC T T' T'' |>.stringify

def ε_global' (s : String) (args : List FuncExpr) : Option (Σ (T : Type), StringModule T) :=
  match s, args with
  | "merge", [.typ t] => .some ⟨ _, merge t.denote 2 ⟩
  | "cntrl_merge", [.typ t] => .some ⟨ _, cntrl_merge t.denote ⟩
  | "fork2", [.typ t] => .some ⟨ _, fork2 t.denote ⟩
  | "queue", [.typ t] => .some ⟨ _, queue t.denote ⟩
  | "init", [.typ b, .val v] =>
    if h: v.type = b
    then .some ⟨ _, init b.denote (h ▸ v.denote) ⟩
    else .none
  | "join", [.typ t1, .typ t2] => .some ⟨ _, join t1.denote t2.denote ⟩
  | "split", [.typ t1, .typ t2] => .some ⟨ _, split t1.denote t2.denote ⟩
  | "branch", [.typ t] => .some ⟨ _, branch t.denote ⟩
  | "mux", [.typ t] => .some ⟨ _, mux t.denote ⟩
  | "muxC", [.typ t] => .some ⟨ _, muxC t.denote ⟩
  | "joinC", [.typ t1, .typ t2, .typ t3] => .some ⟨ _, joinC t1.denote t2.denote t3.denote ⟩
  | "bag", [.typ t] => .some ⟨ _, bag t.denote ⟩
  | "tagger_untagger_val", [.typ t1, .typ t2] => .some ⟨ _, tagger_untagger_val Nat t1.denote t2.denote ⟩
  | "aligner", [.typ t] => .some ⟨ _, aligner Nat t.denote ⟩
  | "sink", [.typ t] => .some ⟨ _, sink t.denote 1 ⟩
  -- | "pure", [f] => .some ⟨ _, pure f ⟩
  | _, _ => .none

namespace FixedSize

@[drunfold, drcomponents] def join T T' n := NatModule.FixedSize.join T T' n |>.stringify

@[drunfold, drcomponents] def joinL T T' T'' n := NatModule.FixedSize.joinL T T' T'' n |>.stringify

end FixedSize
end Graphiti.StringModule
