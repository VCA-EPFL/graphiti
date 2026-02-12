/-
Copyright (c) 2024-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean

public import Graphiti.Core.AssocList.Basic
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
  AssocList.cons_append
  AssocList.nil_append List.foldl_nil
  and_self decide_false Bool.false_eq_true not_false_eq_true List.find?_cons_of_neg
  decide_true List.find?_cons_of_pos Option.isSome_some Bool.and_self
  List.filter_cons_of_pos List.filter_nil Function.comp_apply
  List.filter_cons_of_neg Option.get_some decide_not
  Bool.not_eq_eq_eq_not Bool.not_true decide_eq_false_iff_not ite_not AssocList.foldl_eq
  Batteries.AssocList.toList List.foldl_cons and_true
  and_false List.foldl_nil AssocList.cons_append
  AssocList.nil_append beq_iff_eq not_false_eq_true
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

/--
An instance may refer to an internal instance by name, or it may refer to the
current (top-level) module.
-/
inductive InstIdent (Ident : Type _) where
| top : InstIdent Ident
| internal : Ident → InstIdent Ident
deriving Inhabited, Ord, Hashable, Repr, DecidableEq

instance {Ident} [ToString Ident] : ToString (InstIdent Ident) where
  toString
  | .top => "io"
  | .internal i => toString i

namespace InstIdent

def elem {Ident} [BEq Ident] (instances : List Ident) : InstIdent Ident → Bool
| .top => false
| .internal i => instances.contains i

def isTop {Ident} : InstIdent Ident → Bool
| .top => true
| _ => false

def isInternal {Ident} : InstIdent Ident → Bool
| .internal .. => true
| _ => false

end InstIdent

/--
Internal port parametrised by the `Ident` identifier type.  A port consist of an
instance `inst` it belongs to and a port `name` of that instance.
-/
structure InternalPort (Ident : Type _) where
  inst : InstIdent Ident
  name : Ident
deriving Repr, Hashable, Ord, Inhabited, DecidableEq

attribute [drcompute] InternalPort.mk.injEq

@[drcomponents]
def InternalPort.map {α β} (f : α → β) : InternalPort α → InternalPort β
| ⟨ .top, a ⟩ => ⟨ .top, f a ⟩
| ⟨ .internal b, a ⟩ => ⟨ .internal (f b), f a ⟩

instance {Ident} [ToString Ident] : ToString (InternalPort Ident) where
  toString | ⟨.internal a, b⟩ => toString a ++ " " ++ toString b
           | ⟨.top, b⟩ => toString b

/--
If only an identifier is provided, it can be coerced into an `InternalPort
Ident` by using `InstIdent.top` as the instance name, creating a port for the
top-level module.
-/
instance {Ident} [Inhabited Ident] : Coe Ident (InternalPort Ident) where
  coe a := ⟨InstIdent.top, a⟩

abbrev IdentMap Ident α := AssocList Ident α

namespace IdentMap

def replace_env {Ident α} [BEq Ident] (ε : IdentMap Ident α) {ident mod}
  (h : ε.mem ident mod) mod' :=
  (ε.replace ident mod')

notation:25 "{" ε " | " h " := " mod' "}" => replace_env ε h mod'

end IdentMap

/--
Mapping from `Ident` to any type `α`.  This was chosen to be an AssocList
because it seems like it is the simplest data-structure for performing
reduction.  `RBMap` currently does not work for `whnf` reduction due to
exponential reduction behaviour in `Meta.whnf`.
-/
abbrev PortMap Ident α := AssocList (InternalPort Ident) α

namespace PortMap

variable {Ident}

/--
Get an IO port using external IO ports, i.e. `InternalPort Ident` with the
instance set to `top`.
-/
@[drunfold] def getIO.{u₁, u₂} {S : Type u₁}
    [BEq (InternalPort Ident)]
    (l : PortMap Ident (Σ T : Type u₂, (S → T → S → Prop)))
    (n : InternalPort Ident)
    : Σ T : Type u₂, (S → T → S → Prop) :=
  l.find? n |>.getD (⟨ PUnit, λ _ _ _ => False ⟩)

end PortMap

deriving instance Hashable for AssocList

structure PortMapping (Ident) where
  input : PortMap Ident (InternalPort Ident)
  output : PortMap Ident (InternalPort Ident)
deriving Repr, Inhabited, DecidableEq, Hashable

instance (Ident) [Repr Ident] : ToString (InternalPort Ident) where
  toString i := repr i |>.pretty

instance (Ident) [Repr Ident] : ToString (PortMapping Ident) where
  toString i := repr i |>.pretty

namespace PortMapping

variable {Ident}

instance : EmptyCollection (PortMapping Ident) := ⟨⟨∅, ∅⟩⟩

def append (a b : PortMapping Ident) :=
  PortMapping.mk (a.input ++ b.input) (a.output ++ b.output)

instance : Append (PortMapping Ident) := ⟨append⟩

@[simp, drcompute] theorem empty_append {α} (as : PortMapping α) : ∅ ++ as = as := rfl
@[simp, drcompute] theorem append_elements {α} (a b c d : PortMap α (InternalPort α))
        : PortMapping.mk a b ++ ⟨c, d⟩ = ⟨a ++ c, b ++ d⟩ := rfl
@[simp, drcompute] theorem lift_append {α} (as bs : PortMapping α) : as.append bs = as ++ bs := rfl

-- TODO: Why do we have to canonicalise? When are the port names actually being reordered?
def canonPortMapping [LE Ident] [DecidableLE Ident] (i : PortMapping Ident) : PortMapping Ident :=
  ⟨ (List.mergeSort (le := fun a b => a.1.2 ≤ b.1.2) i.input.toList).toAssocList
  , (List.mergeSort (le := fun a b => a.1.2 ≤ b.1.2) i.output.toList).toAssocList
  ⟩

def hashPortMapping [Hashable Ident] [LE Ident] [DecidableLE Ident] (i : PortMapping Ident) : String :=
  hash (canonPortMapping i) |>.toBitVec |>.toHex |>.take 8 |>.copy

def generateRenamingPortMap [DecidableEq Ident] (p1 p2 : PortMap Ident (InternalPort Ident))
    : Option (PortMap Ident (InternalPort Ident)) :=
  p1.foldlM (λ pm k v => do
    let v' ← p2.find? k
    pm.cons v v'
  ) ∅

def generateRenamingPortMapping [DecidableEq Ident] (p1 p2 : PortMapping Ident) : Option (PortMapping Ident) := do
  let inp ← generateRenamingPortMap p1.input p2.input
  let out ← generateRenamingPortMap p1.output p2.output
  .some ⟨inp, out⟩

def combinePortMapping [Append Ident] (p : List (PortMapping Ident)) : PortMapping Ident := p.foldl (· ++ ·) ∅

def filter (f : InternalPort Ident → InternalPort Ident → Bool) (a : PortMapping Ident) :=
  PortMapping.mk (a.input.filter f) (a.output.filter f)

def ofPortMapping [DecidableEq Ident] (p : PortMapping Ident) : Option Ident :=
  match p.input with
  | .cons ⟨.top, _⟩ ⟨.internal i, _⟩ _ =>
    if p.input.all (λ | ⟨.top, a⟩, ⟨.internal i', b⟩ => a = b && i = i'
                      | _, _ => false)
       && p.output.all (λ | ⟨.top, a⟩, ⟨.internal i', b⟩ => a = b && i = i'
                          | _, _ => false)
    then some i
    else none
  | _ => none

def map {α β} (f : α → β) : PortMapping α → PortMapping β
| ⟨ a, b ⟩ => ⟨a.mapKey (λ k => k.map f) |>.mapVal (λ _ v => v.map f)
              , b.mapKey (λ k => k.map f ) |>.mapVal (λ _ v => v.map f)⟩

def mapPM {α β} (fI fO : PortMap α (InternalPort α) → PortMap β (InternalPort β)) : PortMapping α → PortMapping β
| ⟨ a, b ⟩ => ⟨fI a, fO b⟩

def mapPM1 {α β} (f : PortMap α (InternalPort α) → PortMap β (InternalPort β)) : PortMapping α → PortMapping β
| ⟨ a, b ⟩ => ⟨f a, f b⟩

def mapPairs (f : InternalPort Ident → InternalPort Ident → InternalPort Ident) : PortMapping Ident → PortMapping Ident
| ⟨ a, b ⟩ => ⟨a.mapVal f, b.mapVal f⟩

def mapKeys (f : InternalPort Ident → InternalPort Ident → InternalPort Ident) : PortMapping Ident → PortMapping Ident
| ⟨ a, b ⟩ => ⟨a.mapKey' f, b.mapKey' f⟩

def inverse (p : PortMapping Ident) :=
  {p with input := p.input.inverse, output := p.output.inverse}

variable [DecidableEq Ident]

def squash (a b : PortMapping Ident) :=
  PortMapping.mk (a.input.squash b.input) (a.output.squash b.output)

def filterId (p : PortMapping Ident) : PortMapping Ident :=
  ⟨p.input.filterId, p.output.filterId⟩

def EqExt (a b : PortMapping Ident) : Prop :=
  a.input.EqExt b.input ∧ a.output.EqExt b.output

def wf (a : PortMapping Ident) : Prop := a.input.wf ∧ a.output.wf

end PortMapping

structure Interface (Ident) where
  input : List (InternalPort Ident)
  output : List (InternalPort Ident)
deriving Repr

namespace Interface

variable {Ident}

def allInst (f : InstIdent Ident → Bool) (i : Interface Ident) : Bool :=
  i.input.all (·.inst |> f) && i.output.all (·.inst |> f)

def isBaseModule (i : Interface Ident) : Bool := i.allInst (·.isTop)

def toIdentityPortMapping (i : Interface Ident) : PortMapping Ident :=
  ⟨(i.input.map (λ a => (a, a))).toAssocList,
   (i.output.map (λ a => (a, a))).toAssocList⟩

/--
Need to be careful with the renaming now.
-/
def toIdentityPortMapping' (i : Interface String) : PortMapping String :=
  ⟨(i.input.map (λ a => (⟨.top, s!"{a.name}"⟩, a))).toAssocList,
   (i.output.map (λ a => (⟨.top, s!"{a.name}"⟩, a))).toAssocList⟩

def toIdentityPortMapping'' (ident : Ident) (i : Interface Ident) : PortMapping Ident :=
  ⟨(i.input.map (λ a => (⟨.internal ident, a.name⟩, a))).toAssocList,
   (i.output.map (λ a => (⟨.internal ident, a.name⟩, a))).toAssocList⟩

def toPortMapping (i : Interface Ident) (ident : Ident) : PortMapping Ident :=
  if i.isBaseModule
  then ⟨(i.input.map (λ a => (a, InternalPort.mk (.internal ident) a.name))).toAssocList,
        (i.output.map (λ a => (a, InternalPort.mk (.internal ident) a.name))).toAssocList⟩
  else i.toIdentityPortMapping

end Interface

def PortMapping.toInterface {Ident} (p : PortMapping Ident) : Interface Ident :=
  ⟨p.input.keysList, p.output.keysList⟩

def PortMapping.toInterface' {Ident} (p : PortMapping Ident) : Interface Ident :=
  ⟨p.input.toList.map Prod.snd, p.output.toList.map Prod.snd⟩

theorem reverse_cases {α} l : l = [] ∨ ∃ (l' : List α) (a : α), l = l'.concat a := by
  induction l
  · simp
  · rename_i head tail htail
    cases htail
    · subst_vars
      right; exists [], head
    · rename_i h
      obtain ⟨l', a, ht⟩ := h
      subst_vars
      right; exists (head :: l'), a

noncomputable def _root_.List.concat_induction {α : Sort _}
  {motive : List α → Prop}
  (l : List α)
  (empty : motive [])
  (step : ∀ a l, motive l → motive (l.concat a))
  : motive l := by
  cases reverse_cases l <;> subst_vars
  case inl => assumption
  case inr h =>
    rcases h with ⟨l', a', h⟩
    subst_vars
    apply step
    apply List.concat_induction; assumption; assumption
termination_by l.length
decreasing_by
  subst l; rw [List.length_concat]; simp

end Graphiti
