/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean
public import Batteries.Data.UnionFind
public import Graphiti.Core.Graph.Environment
public import Graphiti.Core.Graph.ExprLow
public import Graphiti.Core.Dataflow.TypeExpr

@[expose] public section

namespace Graphiti

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
      t.typeMap.toList.find? (fun val => val.1.isConcr? && t.ufMap.root! val.2 == t.ufMap.root! c)
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

-- Egraphs would be better...

def toEqMap (x : TypeUF) :=
  x.typeMap.fold (λ m t i =>
        m.alter (x.ufMap.root! i) (λ | none => [(i, t)] | some ts => (i, t) :: ts)
      ) (∅ : Std.HashMap Nat (List (Nat × TypeConstraint)))

instance : ToString TypeUF where
  toString x := toString <| repr <| x.toEqMap

def find_reverse {α β} [BEq α] [Hashable α] [BEq β] (s : Std.HashMap α β) (b : β) : Option α :=
  s.toList.find? (λ x => x.2 == b) |>.map Prod.fst

def addPairConstraints.once (t : TypeUF) : (TypeUF × Bool) :=
  (t.toEqMap.fold (λ s k v =>
    match v.find? (λ | (_, .concr (.pair _ _)) => true | _ => false) with
    | some (_, (.concr (.pair v1 v2))) =>
      v.foldl (λ s el =>
       match el with
       | (_, .concr (.pair v1' v2')) =>
         if v1 == v1' && v2 == v2'
         then s
         else
           let new_ufMap := s.1.ufMap.union! v1 v1' |>.union! v2 v2'
           let new_typeMap := s.1.typeMap.erase (.concr (.pair v1' v2'))
           (⟨new_typeMap, new_ufMap⟩, true)
       | _ => s) s
    | _ => s
  ) (t, false))

def fix_point.struct {α} (f : α → α × Bool) (e : α): Nat → α
| 0 => e
| n+1 => let e' := f e; if e'.2 then fix_point.struct f e'.1 n else e

def fix_point {α} (f : α → α × Bool) (e : α) := fix_point.struct f e 1000

def addPairConstraints (t : TypeUF) : TypeUF := fix_point addPairConstraints.once t

def similarTypes (t1 t2 : TypeConstraint) : Bool :=
  match t1, t2 with
  | .concr (.nat), .concr (.nat) => true
  | .concr (.bool), .concr (.bool) => true
  | .concr (.unit), .concr (.unit) => true
  | .concr (.tag), .concr (.tag) => true
  /- | .concr (.var _), .concr (.var _) => true -/
  | .concr (.pair _ _), .concr (.pair _ _) => true
  | .concr _, .concr _ => false
  | _, _ => true

def check (t : TypeUF) : Bool :=
  t.toEqMap.all (λ _ tc =>
    match tc.filter (λ | (_, .concr _) => true | _ => false) with
    | x :: y => y.map Prod.snd |>.all (similarTypes x.2)
    | _ => true
  )

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
  | "cond_operator1"
  | "cond_operator2"
  | "cond_operator3"
  | "cond_operator4"
  | "cond_operator5" =>
    match i with
    | "out1" => .ok (.concr .bool)
    | _ => .ok (.concr .nat)
  | "constantNat" =>
    match i with
    | "in1" => .ok (.concr .unit)
    | _ => .ok (.concr .nat)
  | "constantBool" =>
    match i with
    | "in1" => .ok (.concr .unit)
    | _ => .ok (.concr .bool)
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
  | "mc"
  | "load"
  | "inputNat"
  | "outputNat0"
  | "outputNat1"
  | "outputNat2"
  | "outputNat3"
  | "outputNat4"
  | "operator1"
  | "operator2"
  | "operator3"
  | "operator4"
  | "operator5"
  | "outputNat5" => .ok (.concr .nat)
  | "initBool"
  | "outputBool0"
  | "outputBool1"
  | "outputBool2"
  | "outputBool3"
  | "outputBool4"
  | "outputBool5" => .ok (.concr .bool)
  | "input"
  | "output0"
  | "output1"
  | "output2"
  | "output3"
  | "output4"
  | "output5" => .ok (.concr .unit)
  | s =>
    -- If we don't know the type of the node, then we just return an uninterpreted function per port.
    if "_graphiti_".isPrefixOf s then
      .ok (.uninterp i (.var sn.2))
    else
      .error s!"could not find node: {sn}/{i}"

def TypeUF.inferTypeInPortMap (t : TypeUF) (p : PortMap String (InternalPort String)) (sn : String × Nat) : Except String (PortMap String TypeExpr) :=
  p.foldlM (λ st k v => do
      let tc ← toTypeConstraint sn k.name
      let concr ← ofOption' s!"could not find type of {sn}/{k.name}" <| t.findConcr tc -- |>.getD (.var 1000) -- TODO: better handling of not finding a concretization
      if concr.containsVar? then throw s!"var in type {sn}/{k.name}: {concr}"
      return st.concat k concr
    ) ∅

def TypeUF.inferTypeInPortMapping (t : TypeUF) (p : PortMapping String) (sn : String × Nat) : Except String (PortMap String TypeExpr × PortMap String TypeExpr) := do
  let inp ← inferTypeInPortMap t p.input sn
  let out ← inferTypeInPortMap t p.output sn
  return (inp, out)

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
  | "tag_untagger_val" =>
    let (_, t) := t.insert (.var sn.2)
    let (vfst, t) := t.insert (.uninterp "fst" (.var sn.2))
    let (vsnd, t) := t.insert (.uninterp "snd" (.var sn.2))
    let t := t.union (.var sn.2) (.concr (.pair vfst vsnd))
    t.union (.uninterp "fst" (.var sn.2)) (.concr .tag)
  /- | "constantNat"
   - | "load"
   - | "mc"
   - | "inputNat"
   - | "outputNat" => t.union (.var sn.2) (.concr .nat)
   - | "initBool"
   - | "constantBool" => t.union (.var sn.2) (.concr .bool) -/
  /- | "output"
   - | "input" -/
  | _ => t

def addPortConstraint (sn : String × Nat) (s : String) (constr : TypeConstraint) (t : TypeUF) : TypeUF :=
  t.union constr (.uninterp s (.var sn.2))

namespace ExprLow

def infer_equalities (e : ExprLow String (String × Nat)) (t : TypeUF) : Except String TypeUF :=
  match e with
  | .base i e => .ok t
  | .connect c e =>
    match findInputInst c.input e, findOutputInst c.output e with
    | some inp, some out =>
      match inp.1.input.inverse.find? c.input, out.1.output.inverse.find? c.output with
      | some ⟨_, inpV⟩, some ⟨_, outV⟩ => do
        let tinp ← toTypeConstraint inp.2 inpV
        let tout ← toTypeConstraint out.2 outV
        let eq := additionalConstraints inp.2 t
          |> additionalConstraints out.2
          /- |> addPortConstraint inp.2 inpV tinp
           - |> addPortConstraint out.2 outV tout -/
          |>.union tinp tout
        if eq.check then
          e.infer_equalities eq
        else
          .error s!"type check failed for: {out.2}/{c.output} --> {inp.2}/{c.input}\n{eq}"
      | _, _ => .error s!"could not find I/O in portmap {c.input}/{c.output}"
    | none, _ => .error s!"findInputInst failed on inp: {c.input}"
    | _, none => .error s!"findOutputInst failed on inp: {c.output}"
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

def infer_equalities (e : ExprHigh String (String × Nat)) (t : TypeUF) : Except String TypeUF := do
  let e ← ofOption' "lowering failed" e.lower_TR
  e.infer_equalities t |>.map TypeUF.addPairConstraints

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
