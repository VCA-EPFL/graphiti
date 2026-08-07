/-
Copyright (c) 2024-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean
public import Batteries.Data.AssocList

public meta import Graphiti.Core.Simp

@[expose] public section

open Batteries (AssocList)

namespace Graphiti

attribute [drnat] OfNat.ofNat instOfNatNat

attribute [drcompute]
  Option.bind_some
  AssocList.foldl_eq AssocList.findEntryP?_eq
  List.partition_eq_filter_filter List.mem_cons List.not_mem_nil or_false not_or
  Bool.decide_and decide_not Batteries.AssocList.toList List.reverse_cons List.reverse_nil
  List.nil_append List.cons_append List.toAssocList List.foldl_cons
  List.foldl_nil
  and_self decide_false Bool.false_eq_true not_false_eq_true List.find?_cons_of_neg
  decide_true List.find?_cons_of_pos Option.isSome_some Bool.and_self
  List.filter_cons_of_pos List.filter_nil Function.comp_apply
  List.filter_cons_of_neg Option.get_some decide_not
  Bool.not_eq_eq_eq_not Bool.not_true decide_eq_false_iff_not ite_not AssocList.foldl_eq
  Batteries.AssocList.toList List.foldl_cons and_true
  and_false List.foldl_nil
  beq_iff_eq not_false_eq_true
  BEq.rfl Option.map_some Option.getD_some
  List.concat_eq_append
  eq_mp_eq_cast cast_eq Prod.exists forall_const ne_eq
  not_true_eq_false imp_self
  String.append_empty

attribute [drunfold_defs] List.foldlM

attribute [drlogic]
  false_and and_false and_true and_self true_and
  exists_const exists_false
  not_and_self
  Option.getD_none eq_mp_eq_cast
  imp_false imp_self
  forall_const
  not_false_iff not_true

instance {α} [Inhabited α] : Alternative (Except α) where
  failure := .error default
  orElse a f := match a with
                | .ok x => .ok x
                | _ => f ()

def _root_.Option.toExcept {α ε} (s : ε) (o : Option α) : Except ε α :=
  match o with
  | .some a => .ok a
  | .none => .error s

deriving instance DecidableEq for Except

class FromString (α : Type _) where
  fromString? : String → Except String α

instance : FromString String where
  fromString? a := pure a

section SimpProc

open Lean Meta Simp

meta def fromExpr? (e : Expr) : SimpM (Option Nat) :=
  getNatValue? e

meta def fromExpr?' (e : Expr) : SimpM (Option (Array Char)) :=
  getListLitOf? e getCharValue?

def ofOption {ε α σ} (e : ε) : Option α → EStateM ε σ α
| some o => pure o
| none => throw e

def ofOption' {ε α} (e : ε) : Option α → Except ε α
| some o => pure o
| none => throw e

/--
Reduce `toString 5` to `"5"`
-/
@[inline] meta def reduceToStringImp (e : Expr) : SimpM Simp.DStep := do
  let some n ← fromExpr? e.appArg! | return .continue
  return .done <| .lit <| .strVal <| toString n

dsimproc [simp, seval, drcompute] reduceToString (toString (_ : Nat)) := reduceToStringImp

/--
Reduce `toString 5` to `"5"`
-/
@[inline] meta def reduceNatReprImp (e : Expr) : SimpM Simp.DStep := do
  let some n ← fromExpr? e.appArg! | return .continue
  return .done <| .lit <| .strVal <| toString n

dsimproc [simp, seval, drcompute] reduceNatRepr (Nat.repr _) := reduceNatReprImp

/--
Reduce `toString 5` to `"5"`
-/
@[inline] meta def reduceStringmkImp (e : Expr) : SimpM Simp.DStep := do
  let some n ← fromExpr?' e.appArg! | return .continue
  return .done <| .lit <| .strVal <| String.mk n.toList

-- #print Char

-- example : ∀ y : String -> Prop, y (String.mk ['a', 'b']) := by
--   intros; reduce
--   dsimp

dsimproc [simp, seval, drcompute] reduceStringmk (String.mk _) := reduceStringmkImp

end SimpProc

end Graphiti
