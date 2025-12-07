/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean
public import Graphiti.Core.ExprLow
public import Graphiti.Core.Environment
public import Batteries.Data.UnionFind

@[expose] public section

namespace Graphiti

structure ModuleInterface (Ident) where
  inputs : PortMap Ident Type
  outputs : PortMap Ident Type

def Module.toModuleInterface {S Ident} (m : Module Ident S) : ModuleInterface Ident :=
  ⟨m.inputs.mapVal (λ k v => v.1), m.outputs.mapVal (λ k v => v.1)⟩

namespace ExprLow

section BuildModule

universe i t
variable {Ident : Type i}
variable {Typ : Type t}
variable [DecidableEq Ident]
-- variable [DecidableEq Typ]

variable (ε : Env Ident Typ)

def build_module_interface : ExprLow Ident Typ → Option (ModuleInterface Ident)
| .base i e =>
  (ε e).map (λ mod => (mod.2.renamePorts i).toModuleInterface)
| .connect c e =>
  e.build_module_interface >>= λ mi =>
  pure ⟨mi.inputs.eraseAll c.input, mi.outputs.eraseAll c.output⟩
| product e₁ e₂ =>
  e₁.build_module_interface >>= λ m₁ =>
  e₂.build_module_interface >>= λ m₂ =>
  pure ⟨m₁.inputs ++ m₂.inputs, m₁.outputs ++ m₂.outputs⟩

def build_module_interface' : ExprLow Ident Typ → Option (ModuleInterface Ident)
| .base i e =>
  (ε e).map (λ mod => (mod.2.renamePorts i).toModuleInterface)
| .connect c e =>
  e.build_module_interface'
| product e₁ e₂ =>
  e₁.build_module_interface' >>= λ m₁ =>
  e₂.build_module_interface' >>= λ m₂ =>
  pure ⟨m₁.inputs ++ m₂.inputs, m₁.outputs ++ m₂.outputs⟩

def well_typed : ExprLow Ident Typ → Prop
| .base i e => True
| .connect c e =>
  e.well_typed
  ∧ ∃ mi T,
      e.build_module_interface ε = .some mi
      ∧ mi.inputs.find? c.input = .some T
      ∧ mi.outputs.find? c.output = .some T
| product e₁ e₂ => e₁.well_typed ∧ e₂.well_typed

def well_typed'' (m : ModuleInterface Ident) : ExprLow Ident Typ → Prop
| .base i e => True
| .connect c e =>
  e.well_typed'' m
  ∧ ∃ T,
      m.inputs.find? c.input = .some T
      ∧ m.outputs.find? c.output = .some T
| product e₁ e₂ => e₁.well_typed'' m ∧ e₂.well_typed'' m

def well_typed' e :=
  ∃ mi, e.build_module_interface' ε = some mi ∧ well_typed'' mi e

def valsList : ExprLow Ident Typ → List (InternalPort Ident) × List (InternalPort Ident)
| base inst typ => (inst.input.valsList, inst.output.valsList)
| product e1 e2 => let e1' := e1.valsList; let e2' := e2.valsList; (e1'.1 ++ e2'.1, e1'.2 ++ e2'.2)
| connect c e => e.valsList

def unique_valsList (e : ExprLow Ident Typ) := e.valsList.1.Nodup ∧ e.valsList.2.Nodup

variable {ε}

theorem build_module_interface_product {e1 e2 : ExprLow Ident Typ} {m} :
  (e1.product e2).build_module_interface ε = some m →
  ∃ m1 m2, e1.build_module_interface ε = some m1 ∧ e2.build_module_interface ε = some m2
           ∧ m.inputs = m1.inputs ++ m2.inputs ∧ m.outputs = m1.outputs ++ m2.outputs := by
  dsimp [build_module_interface]; grind [Option.bind_eq_some_iff]

theorem build_module_interface_connect {e : ExprLow Ident Typ} {c} {m} :
  (e.connect c).build_module_interface ε = some m →
  ∃ m', e.build_module_interface ε = some m'
        ∧ m.inputs = m'.inputs.eraseAll c.input ∧ m.outputs = m'.outputs.eraseAll c.output := by
  dsimp [build_module_interface]; grind [Option.bind_eq_some_iff]

theorem build_module_interface'_product {e1 e2 : ExprLow Ident Typ} {m} :
  (e1.product e2).build_module_interface' ε = some m →
  ∃ m1 m2, e1.build_module_interface' ε = some m1 ∧ e2.build_module_interface' ε = some m2
           ∧ m.inputs = m1.inputs ++ m2.inputs ∧ m.outputs = m1.outputs ++ m2.outputs := by
  dsimp [build_module_interface']; grind [Option.bind_eq_some_iff]

theorem build_module_interface'_connect {e : ExprLow Ident Typ} {c} {m} :
  (e.connect c).build_module_interface' ε = some m →
  e.build_module_interface' ε = some m := by
  dsimp [build_module_interface']; grind [Option.bind_eq_some_iff]

theorem well_typed_prod_symm {e1 e2 : ExprLow Ident Typ} :
  (e1.product e2).well_typed ε →
  (e2.product e1).well_typed ε := by
  intro ⟨wt1, wt2⟩; constructor <;> assumption

inductive Constraint (α) where
| eq : α → α → Constraint α
deriving DecidableEq

theorem build_module_interface_build_module_interface'' {e : ExprLow Ident Typ} {mi} :
  e.build_module_interface ε = some mi →
  ∃ mi', e.build_module_interface' ε = some mi' := by
  induction e generalizing mi with
  | base inst typ => dsimp [build_module_interface, build_module_interface']; grind
  | connect c e ih =>
    intro hbuild
    dsimp [build_module_interface, build_module_interface'] at *
    rw [] at hbuild
    obtain ⟨mi'', h1, h2⟩ := Option.bind_eq_some_iff.mp hbuild
    cases h2
    rw [h1] at hbuild; dsimp at hbuild; cases hbuild
    solve_by_elim
  | product e1 e2 he1 he2 =>
    intro h1
    have h1_2 := build_module_interface_product h1
    obtain ⟨m1, m2, h1', h2', h3', h4'⟩ := h1_2
    dsimp [build_module_interface', build_module_interface] at *
    rw [h1'] at h1
    rw [h2'] at h1; dsimp at h1; cases h1; cases h3'; cases h4'
    grind

end BuildModule

end ExprLow

inductive TypeExpr' where
| nat
| bool
| tag
| unit
| var (n : Nat)
| pair (left right : Nat)
deriving Repr, DecidableEq, Inhabited, Hashable

inductive TypeConstraint where
| concr : TypeExpr' → TypeConstraint
| var : Nat → TypeConstraint
| uninterp : String → TypeConstraint → TypeConstraint
deriving DecidableEq, Hashable, Repr

def TypeConstraint.isConcr? (c : TypeConstraint) : Bool :=
  match c with | .concr _ => true | _ => false

structure TypeUF where
  typeMap : Std.HashMap TypeConstraint Nat
  ufMap : Batteries.UnionFind

namespace TypeUF

def insert (t : TypeUF) (c : TypeConstraint) : (Nat × TypeUF) :=
  match t.typeMap.getThenInsertIfNew? c t.ufMap.arr.size with
  | (some v, _) => (v, t)
  | (none, t') => (t.ufMap.arr.size, {typeMap := t', ufMap := t.ufMap.push})

def union (t : TypeUF) (t1 t2 : TypeConstraint) : TypeUF :=
  let (v1, t') := t.insert t1
  let (v2, t'') := t'.insert t2
  {t'' with ufMap := t''.ufMap.union! v1 v2}

def findConcrTE'' (t : TypeUF) (c : Nat) : Option TypeExpr' := do
  let (.concr n1Concr, _) :=
      t.typeMap.toList.filter (fun val => t.ufMap.root! val.2 == t.ufMap.root! c && val.1.isConcr?)
      |>.head?
      |>.getD (.concr (.var (t.ufMap.root! c)), 0)
    | failure
  return n1Concr

def findConcrTE' (t : TypeUF) (c : TypeConstraint) : Option TypeExpr' := findConcrTE'' t (t.insert c).1

def toTypeExpr' (t : TypeUF) (e : TypeExpr') : Nat → Option TypeExpr
| 0 => none
| n+1 =>
  match e with
  | .nat => .some .nat
  | .bool => .some .bool
  | .tag => .some .tag
  | .unit => .some .unit
  | .var n => .some (.var n)
  | .pair n1 n2 => do
    let n1Concr ← findConcrTE'' t n1 >>= fun x => toTypeExpr' t x n
    let n2Concr ← findConcrTE'' t n2 >>= fun x => toTypeExpr' t x n
    .some <| .pair n1Concr n2Concr

def toTypeExpr (t : TypeUF) (e : TypeExpr') : Option TypeExpr := toTypeExpr' t e 1000

def findConcr' (t : TypeUF) (c : Nat) : Option TypeExpr := t.findConcrTE'' c >>= t.toTypeExpr
def findConcr (t : TypeUF) (c : TypeConstraint) : Option TypeExpr := t.findConcrTE' c >>= t.toTypeExpr

end TypeUF

/--
Generates the type constraint that corresponds to the type of the port in the module.
-/
def toTypeConstraint (sn : String × Nat) (i : String) : Except String TypeConstraint :=
  match sn.1 with
  | "mux" =>
    match i with
    | "in1" => .ok (.concr .bool)
    | "in2" | "in3" | "out1" => .ok (.var sn.2)
    | _ => .error s!"could not find port: {sn}/{i}"
  | "branch" =>
    match i with
    | "in2" => .ok (.concr .bool)
    | "in1" | "out1" | "out2" => .ok (.var sn.2)
    | _ => .error s!"could not find port: {sn}/{i}"
  | "split" =>
    match i with
    | "in1" => .ok (.var sn.2)
    | "out1" => .ok (.uninterp "fst" (.var sn.2))
    | "out2" => .ok (.uninterp "snd" (.var sn.2))
    | _ => .error s!"could not find port: {sn}/{i}"
  | "join" =>
    match i with
    | "out1" => .ok (.var sn.2)
    | "in1" => .ok (.uninterp "fst" (.var sn.2))
    | "in2" => .ok (.uninterp "snd" (.var sn.2))
    | _ => .error s!"could not find port: {sn}/{i}"
  | "operator1"
  | "operator2"
  | "operator3"
  | "operator4"
  | "operator5"
  | "pure" =>
    match i with
    | "in1" => .ok (.uninterp "dom1" (.var sn.2))
    | "in2" => .ok (.uninterp "dom2" (.var sn.2))
    | "in3" => .ok (.uninterp "dom3" (.var sn.2))
    | "in4" => .ok (.uninterp "dom4" (.var sn.2))
    | "in5" => .ok (.uninterp "dom5" (.var sn.2))
    | "out1" => .ok (.uninterp "codom" (.var sn.2))
    | _ => .error s!"could not find port: {sn}/{i}"
  | "tag_untagger_val" =>
    match i with
    | "in2" | "out2" => .ok (.uninterp "snd" (.var sn.2))
    | "in1" | "out1" => .ok (.var sn.2)
    | _ => .error s!"could not find port: {sn}/{i}"
  | "fork2"
  | "fork3"
  | "fork4"
  | "fork5"
  | "fork6"
  | "fork7"
  | "fork8"
  | "fork9"
  | "fork10"
  | "fork"
  | "merge"
  | "merge2"
  | "sink"
  | "queue" => .ok (.var sn.2)
  | "output"
  | "constantNat"
  | "load"
  | "input" => .ok (.concr .nat)
  | "initBool"
  | "constantBool" => .ok (.concr .bool)
  | s =>
    -- If we don't know the type of the node, then we just return an uninterpreted function per port.
    if "_graphiti_".isPrefixOf s then
      .ok (.uninterp i (.var sn.2))
    else
      .error s!"could not find node: {sn}/{i}"

/--
Generates additional typing constraints for type inference for each of the types.
-/
def additionalConstraints (sn : String × Nat) (t : TypeUF) : TypeUF :=
  match sn.1 with
  | "split" =>
    let (vfst, t1) := t.insert (.uninterp "fst" (.var sn.2))
    let (vsnd, t2) := t1.insert (.uninterp "snd" (.var sn.2))
    t2.union (.var sn.2) (.concr (.pair vfst vsnd))
  | "join" =>
    let (vfst, t1) := t.insert (.uninterp "fst" (.var sn.2))
    let (vsnd, t2) := t1.insert (.uninterp "snd" (.var sn.2))
    t2.union (.var sn.2) (.concr (.pair vfst vsnd))
  | "operator"
  | "pure" => t.insert (.var sn.2) |>.snd
  | "tagger_untagger_val" =>
    let (_, t) := t.insert (.var sn.2)
    let (_, t) := t.insert (.uninterp "snd" (.var sn.2))
    t.union (.uninterp "fst" (.var sn.2)) (.concr .tag)
  | "output"
  | "constantNat"
  | "input" => t.union (.var sn.2) (.concr .nat)
  | "initBool"
  | "constantBool" => t.union (.var sn.2) (.concr .bool)
  | _ => t

namespace ExprLow

def infer_equalities (e : ExprLow String (String × Nat)) (t : TypeUF) : Except String TypeUF :=
  match e with
  | .base i e => .ok t
  | .connect c e =>
    match findInputInst c.input e, findOutputInst c.output e, e.infer_equalities t with
    | some inp, some out, .ok t =>
      match inp.1.input.inverse.find? c.input, out.1.output.inverse.find? c.output with
      | some ⟨_, inpV⟩, some ⟨_, outV⟩ => do
        let tinp ← toTypeConstraint inp.2 inpV
        let tout ← toTypeConstraint out.2 outV
        .ok (additionalConstraints inp.2 t |> additionalConstraints out.2 |>.union tinp tout)
      | _, _ => .error s!"could not find I/O in portmap {c.input}/{c.output}"
    | none, _, _ => .error s!"findInputInst failed on inp: {c.input}"
    | _, none, _ => .error s!"findOutputInst failed on inp: {c.output}"
    | _, _, .error s => .error s
  | .product e1 e2 => e1.infer_equalities t >>= e2.infer_equalities

def infer_types (e : ExprLow String (String × Nat)) : Except String (ExprLow String (String × TypeExpr)) := do
  let eqs ← e.infer_equalities ⟨∅, Batteries.UnionFind.mkEmpty 100⟩
  go eqs e
  where
    go (t : TypeUF) : ExprLow String (String × Nat) → Except String (ExprLow String (String × TypeExpr))
    | .base inst typ =>
      match t.findConcr (.var typ.2) with
      | some concr => .ok (.base inst (typ.1, concr))
      | none => .error s!"could not find concrete type for {typ}"
    | .connect c e => .connect c <$> go t e
    | .product e1 e2 => do
      let e1' ← go t e1
      let e2' ← go t e2
      return .product e1' e2'

end ExprLow

namespace ExprHigh

section WellTyped

variable {Ident Typ}
variable [DecidableEq Ident]
variable [DecidableEq Typ]

variable (ε : Env Ident Typ)

def well_typed (h : ExprHigh Ident Typ) : Prop :=
  ∃ hl, h.lower = some hl ∧ hl.well_typed ε

end WellTyped

def infer_equalities (e : ExprHigh String (String × Nat)) (t : TypeUF) : Except String TypeUF := do
  let e ← ofOption' "lowering failed" e.lower_TR
  e.infer_equalities t

def infer_types' (e : ExprHigh String (String × Nat)) : Except String (ExprHigh String (String × TypeExpr) × TypeUF) := do
  let eqs ← e.infer_equalities ⟨∅, Batteries.UnionFind.mkEmpty 100⟩
  let res ← e.modules.foldlM (λ s k typ =>
      match eqs.findConcr (.var typ.2.2) with
      | some concr => .ok (s.cons k (typ.1, (typ.2.1, concr)))
      | none => .error s!"could not find concrete type for {typ}"
    ) ∅
  return ({e with modules := res}, eqs)

def infer_types e := Prod.fst <$> infer_types' e

end ExprHigh

end Graphiti
