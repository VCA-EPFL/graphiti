/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Module
import Batteries.Data.RBMap

open Batteries (RBMap)

namespace Graphiti.DC

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
-- @[simp]
-- def connect' (mod : Module S) (o i : Ident) : Module S :=
--        { inputs := mod.inputs.erase i ,
--          outputs :=  mod.outputs.erase o,
--          internals :=  (λ st st' => ∀ wf : (mod.inputs.getIO i).1 = (mod.outputs.getIO o).1,
--                             ∃ consumed_output output, (mod.outputs.getIO o).2 st output consumed_output ∧
--                               (mod.inputs.getIO i).2 consumed_output (Eq.rec id wf output) st')
--                               :: mod.internals }

def join : Module (List Nat × List Nat) :=
  { inputs := RBMap.ofList [
           ("in_0", ⟨ Nat, λ s n s' => s' = (s.1.concat n, s.2) ⟩),
           ("in_1", ⟨ Nat, λ s n s' => s' = (s.1, s.2.concat n) ⟩)] _,
    outputs := RBMap.ofList [("out", ⟨ Nat × Nat, λ s n s' => s.1 = n.1 :: s'.1 ∧ s.2 = n.2 :: s'.2 ⟩)] _,
    internals := [],
  }

def pack : Module (List Nat) :=
  { inputs := RBMap.ofList [
           ("in_0", ⟨ Nat, λ s n s' => s' = (s.1.concat n, s.2) ⟩),
           ("in_1", ⟨ Nat, λ s n s' => s' = (s.1, s.2.concat n) ⟩)] _,
    outputs := RBMap.ofList [("out", ⟨ Nat × Nat, λ s n s' => s.1 = n.1 :: s'.1 ∧ s.2 = n.2 :: s'.2 ⟩)] _,
    internals := [],
  }

def channel : Module (List Nat) :=
  { inputs := RBMap.ofList [ ("in_0", ⟨ Nat, λ s n s' => s' = s.concat n ⟩) ] _,
    outputs := RBMap.ofList [("out", ⟨ Nat, λ s n s' => s = n :: s' ⟩)] _,
    internals := [],
  }

def join' : Module (Option Nat × Option Nat) :=
  { inputs := RBMap.ofList [
           ("in_0", ⟨ Nat, λ s n s' => s.1 = none ∧ s' = (some n, s.2) ⟩),
           ("in_1", ⟨ Nat, λ s n s' => s.2 = none ∧ s' = (s.1, some n) ⟩)] _,
    outputs := RBMap.ofList [("out", ⟨ Nat × Nat, λ s n s' => s.1 = some n.1 ∧ s.2 = some s.2 ∧ s' = (none, none) ⟩)] _,
    internals := [],
  }

structure JoinState where
  left : Option Nat
  right : Option Nat
  out_ready : Bool
  in_0_valid : Bool
  in_1_valid : Bool

def join'' : Module JoinState :=
  { inputs := RBMap.ofList [
           ("in_0", ⟨ Nat, λ s n s' => s.in_0_valid ∧ s.left.isNone ∧ s' = { s with left := some n } ⟩),
           ("in_1", ⟨ Nat, λ s n s' => s.in_1_valid ∧ s.right.isNone ∧ s' = { s with right := some n } ⟩),
           ("in_0_valid", ⟨ Bool, λ s b s' => s' = { s with in_0_valid := b } ⟩),
           ("in_1_valid", ⟨ Bool, λ s b s' => s' = { s with in_1_valid := b } ⟩),
           ("out_ready", ⟨ Bool, λ s b s' => s' = { s with out_ready := b } ⟩),
           ] _,
    outputs := RBMap.ofList [ ("out", ⟨ Nat × Nat, λ s n s' => s.1 = some n.1 ∧ s.2 = some s.2
                                                               ∧ s' = ⟨ none, none, false, s.in_0_valid, s.in_1_valid ⟩ ⟩)
                            , ("out_valid", ⟨ Bool, λ s b s' => s = s' ∧ b = (s.left.isSome ∧ s.right.isSome) ⟩)
                            , ("in_0_ready", ⟨ Bool, λ s b s' => s = s' ∧ b = s.1.isNone ⟩)
                            , ("in_1_ready", ⟨ Bool, λ s b s' => s = s' ∧ b = s.2.isNone ⟩)
                            ] _,
    internals := [],
  }

structure PackState where
  val : Option Nat
  in_0_valid : Bool
  out_ready : Bool

def unpack : Module PackState :=
  { inputs := RBMap.ofList [
           ("in_0", ⟨ Nat, λ s n s' => s.in_0_valid ∧ s.val.isNone ∧ s' = { s with val := some n } ⟩),
           ("in_0_valid", ⟨ Bool, λ s b s' => s' = { s with in_0_valid := b } ⟩),
           ("out_ready", ⟨ Bool, λ s b s' => s' = { s with out_ready := b } ⟩),
           ] _,
    outputs := RBMap.ofList [ ("out", ⟨ Unit, λ s n s' => n = () ∧ s' = s ⟩)
                            , ("out_valid", ⟨ Bool, λ s b s' => s = s' ∧ b = s.val.isSome ⟩)
                            , ("out_num", ⟨ Nat, λ s n s' => s' = { s with val := none } ∧ s.val = some n ⟩)
                            , ("out_num_valid", ⟨ Bool, λ s b s' => s = s' ∧ b = s.val.isSome ⟩)
                            , ("in_0_ready", ⟨ Bool, λ s b s' => s = s' ∧ b = s.1.isNone ⟩)
                            ] _,
    internals := [],
  }

def graph :=
[graph|
  unpack0 [shape = polygon, type = "unpack"]                                     ;
  unpack1 [shape = polygon, type = "unpack"]                                       ;
  unpack2 [shape = polygon, type = "unpack"]                                       ;
  unpack3 [shape = polygon, type = "unpack"]                                       ;
  unpack4 [shape = polygon, type = "unpack"]                                       ;
  unpack5 [shape = polygon, type = "unpack"]                                       ;
  unpack6 [shape = polygon, type = "unpack"]                                       ;
  unpack7 [shape = polygon, type = "unpack"]                                       ;
  combSge8 [shape = polygon, type = "combSge"]                                     ;
  combMux9 [shape = polygon, type = "combMux"]                                     ;
  combSge10 [shape = polygon, type = "combSge"]                                    ;
  combMux11 [shape = polygon, type = "combMux"]                                    ;
  combSge12 [shape = polygon, type = "combSge"]                                    ;
  combMux13 [shape = polygon, type = "combMux"]                                    ;
  combSge14 [shape = polygon, type = "combSge"]                                    ;
  combMux15 [shape = polygon, type = "combMux"]                                    ;
  combSge16 [shape = polygon, type = "combSge"]                                    ;
  combMux17 [shape = polygon, type = "combMux"]                                    ;
  combSge18 [shape = polygon, type = "combSge"]                                    ;
  combMux19 [shape = polygon, type = "combMux"]                                    ;
  combSge20 [shape = polygon, type = "combSge"]                                    ;
  combMux21 [shape = polygon, type = "combMux"]                                    ;
  join22 [shape = polygon, type = "join"]                                          ;
  pack23 [shape = polygon, type = "pack"]                                          ;
  src_0  [type = "io"];
  src_1  [type = "io"];
  src_2  [type = "io"];
  src_3  [type = "io"];
  src_4  [type = "io"];
  src_5  [type = "io"];
  src_6  [type = "io"];
  src_7  [type = "io"];
  in_0 [type = "io"];
  src_0 -> unpack0 [inp = "in_0", out = "out", label = "in_0"]                    ;
  src_1 -> unpack1 [inp = "in_0", out = "out", label = "in_3"]                    ;
  src_2 -> unpack2 [inp = "in_0", out = "out", label = "in_6"]                    ;
  src_3 -> unpack3 [inp = "in_0", out = "out", label = "in_9"]                    ;
  src_4 -> unpack4 [inp = "in_0", out = "out", label = "in_12"]                   ;
  src_5 -> unpack5 [inp = "in_0", out = "out", label = "in_15"]                   ;
  src_6 -> unpack6 [inp = "in_0", out = "out", label = "in_18"]                   ;
  src_7 -> unpack7 [inp = "in_0", out = "out", label = "in_21"]                   ;
  unpack0 -> combSge8 [inp = "in_0", out = "out", label = "in_2"]                 ;
  unpack0 -> combMux9 [inp = "in_1", out = "out", label = "in_2"]                 ;
  unpack0 -> join22 [inp = "in_0", out = "out", label = "token_1"]                ;
  unpack1 -> combSge8 [inp = "in_1", out = "out", label = "in_5"]                 ;
  unpack1 -> combMux9 [inp = "in_2", out = "out", label = "in_5"]                 ;
  unpack1 -> join22 [inp = "in_1", out = "out", label = "token_4"]                ;
  unpack2 -> combSge10 [inp = "in_0", out = "out", label = "in_8"]                ;
  unpack2 -> combMux11 [inp = "in_1", out = "out", label = "in_8"]                ;
  unpack2 -> join22 [inp = "in_2", out = "out", label = "token_7"]                ;
  unpack3 -> combSge10 [inp = "in_1", out = "out", label = "in_11"]               ;
  unpack3 -> combMux11 [inp = "in_2", out = "out", label = "in_11"]               ;
  unpack3 -> join22 [inp = "in_3", out = "out", label = "token_10"]               ;
  unpack4 -> combSge12 [inp = "in_0", out = "out", label = "in_14"]               ;
  unpack4 -> combMux13 [inp = "in_1", out = "out", label = "in_14"]               ;
  unpack4 -> join22 [inp = "in_4", out = "out", label = "token_13"]               ;
  unpack5 -> combSge12 [inp = "in_1", out = "out", label = "in_17"]               ;
  unpack5 -> combMux13 [inp = "in_2", out = "out", label = "in_17"]               ;
  unpack5 -> join22 [inp = "in_5", out = "out", label = "token_16"]               ;
  unpack6 -> combSge14 [inp = "in_0", out = "out", label = "in_20"]               ;
  unpack6 -> combMux15 [inp = "in_1", out = "out", label = "in_20"]               ;
  unpack6 -> join22 [inp = "in_6", out = "out", label = "token_19"]               ;
  unpack7 -> combSge14 [inp = "in_1", out = "out", label = "in_23"]               ;
  unpack7 -> combMux15 [inp = "in_2", out = "out", label = "in_23"]               ;
  unpack7 -> join22 [inp = "in_7", out = "out", label = "token_22"]               ;
  combSge8 -> combMux9 [inp = "in_0", out = "out", label = "in_24"]               ;
  combMux9 -> combSge16 [inp = "in_0", out = "out", label = "in_25"]              ;
  combMux9 -> combMux17 [inp = "in_1", out = "out", label = "in_25"]              ;
  combSge10 -> combMux11 [inp = "in_0", out = "out", label = "in_26"]             ;
  combMux11 -> combSge16 [inp = "in_1", out = "out", label = "in_27"]             ;
  combMux11 -> combMux17 [inp = "in_2", out = "out", label = "in_27"]             ;
  combSge12 -> combMux13 [inp = "in_0", out = "out", label = "in_28"]             ;
  combMux13 -> combSge18 [inp = "in_0", out = "out", label = "in_29"]             ;
  combMux13 -> combMux19 [inp = "in_1", out = "out", label = "in_29"]             ;
  combSge14 -> combMux15 [inp = "in_0", out = "out", label = "in_30"]             ;
  combMux15 -> combSge18 [inp = "in_1", out = "out", label = "in_31"]             ;
  combMux15 -> combMux19 [inp = "in_2", out = "out", label = "in_31"]             ;
  combSge16 -> combMux17 [inp = "in_0", out = "out", label = "in_32"]             ;
  combMux17 -> combSge20 [inp = "in_0", out = "out", label = "in_33"]             ;
  combMux17 -> combMux21 [inp = "in_1", out = "out", label = "in_33"]             ;
  combSge18 -> combMux19 [inp = "in_0", out = "out", label = "in_34"]             ;
  combMux19 -> combSge20 [inp = "in_1", out = "out", label = "in_35"]             ;
  combMux19 -> combMux21 [inp = "in_2", out = "out", label = "in_35"]             ;
  combSge20 -> combMux21 [inp = "in_0", out = "out", label = "in_36"]             ;
  combMux21 -> pack23 [inp = "in_1", out = "out", label = "in_37"]                ;
  join22 -> pack23 [inp = "in_0", out = "out", label = "in_38"]                   ;
  pack23 -> in_0 [inp = "in_0", out = "out", label = "in_39"]                     ;
  ]

#print graph

end Graphiti.DC
