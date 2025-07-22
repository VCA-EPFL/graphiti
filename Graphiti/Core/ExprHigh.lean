/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Graphiti.Core.ExprLow

namespace Graphiti

/--
Graph description of a cicruit.  Note that currently one cannot describe an
input that connects directly to the output.  Instead, these always have to pass
by an internal module.
-/
structure ExprHigh (Ident : Type _) where
  modules     : IdentMap Ident (PortMapping Ident × Ident)
  connections : List (Connection Ident)
deriving Repr, DecidableEq, Inhabited

structure NamedExprHigh (Ident : Type _) where
  graph       : ExprHigh Ident
  inPorts     : IdentMap Ident (InternalPort Ident)
  outPorts    : IdentMap Ident (InternalPort Ident)

structure NextNode (Ident) where
  inst : Ident
  inputPort : Ident
  outputPort : Ident
  portMap : PortMapping Ident
  typ : Ident
  connection : Connection Ident
deriving Repr, Inhabited

namespace ExprHigh

universe i
variable {Ident : Type i}
variable [DecidableEq Ident]

def findInputPort (p : InternalPort Ident) (i : IdentMap Ident (PortMapping Ident × Ident)) : Option Ident :=
  i.foldl (λ a k v =>
      match a with | some a' => a | none => do
        let _ ← if (v.fst.input.filter (λ k' v' => p = v')).length > 0 then pure PUnit.unit else failure
        return k
    ) none

def findInputPort' (p : InternalPort Ident) (i : IdentMap Ident (PortMapping Ident × Ident)) : Option (Ident × Ident) :=
  i.foldl (λ a k v =>
      match a with | some a' => a | none => do
        let l ← v.fst.input.findEntryP? (λ k' v' => p = v')
        return (k, l.fst.name)
    ) none

def findOutputPort (p : InternalPort Ident) (i : IdentMap Ident (PortMapping Ident × Ident)) : Option Ident :=
  i.foldl (λ a k v =>
      match a with | some a' => a | none => do
        let _ ← if (v.fst.output.filter (λ k' v' => p = v')).length > 0 then pure PUnit.unit else failure
        return k
    ) none

def findOutputPort' (p : InternalPort Ident) (i : IdentMap Ident (PortMapping Ident × Ident)) : Option (Ident × Ident) :=
  i.foldl (λ a k v =>
      match a with | some a' => a | none => do
        let l ← v.fst.output.findEntryP? (λ k' v' => p = v')
        return (k, l.fst.name)
    ) none

def inputNodes (g : ExprHigh Ident) : List Ident :=
  g.modules.foldl (λ inodes k v =>
      if v.fst.input.any (λ _ k => k.inst.isTop)
      then k :: inodes
      else inodes
    ) ∅

def inputPorts (g : ExprHigh Ident) : List Ident :=
  g.modules.foldl (λ inodes k v =>
      inodes ++ (v.fst.input.filter (λ _ k => k.inst.isTop) |>.toList |>.map (λ (_, ⟨_, k⟩) => k))
    ) ∅

def outputPorts (g : ExprHigh Ident) : List Ident :=
  g.modules.foldl (λ inodes k v =>
      inodes ++ (v.fst.output.filter (λ _ k => k.inst.isTop) |>.toList |>.map (λ (_, ⟨_, k⟩) => k))
    ) ∅

def outputNodes (g : ExprHigh Ident) : List Ident :=
  g.modules.foldl (λ inodes k v =>
      if v.fst.output.any (λ _ k => k.inst.isTop)
      then k :: inodes
      else inodes
    ) ∅

def getPortMaps (g : ExprHigh String) : List (PortMapping String) :=
  g.modules.toList.map (λ (x, (y, z)) => y)

def invert (g : ExprHigh Ident) : ExprHigh Ident :=
  let mods := g.modules.mapVal
    (λ k v => ({v.fst with input := v.fst.output, output := v.fst.input}, v.snd))
  let conns := g.connections.map (λ a => ⟨a.input, a.output⟩)
  ⟨mods, conns⟩

@[inline] def uncurry {α β γ} (f : α → β → γ) (v : α × β): γ :=
  f v.fst v.snd

@[inline] def generate_product := (fun (val : Ident × PortMapping Ident × Ident) expr =>
  match expr with
  | none => some (ExprHigh.uncurry ExprLow.base val.2)
  | some expr' => some ((ExprHigh.uncurry ExprLow.base val.2).product expr'))

@[drunfold] def lower' (el : ExprLow Ident) (e : ExprHigh Ident) : ExprLow Ident :=
  let prod_expr :=
    match e.modules.toList.foldr generate_product none with
    | none => el
    | some el' => el.product el'
  e.connections.foldr (λ conn expr => .connect conn expr) prod_expr

def lower'_prod_TR (e : IdentMap Ident (PortMapping Ident × Ident)) (el : ExprLow Ident) : ExprLow Ident :=
  e.toList.foldl (λ expr val => .product (uncurry .base val.snd) expr) el

def lower'_conn_TR (e : List (Connection Ident)) (el : ExprLow Ident) : ExprLow Ident :=
  e.foldl (λ expr conn => .connect conn expr) el

@[drunfold] def lower (e : ExprHigh Ident) : Option (ExprLow Ident) :=
  match e.modules.toList with
  | x :: xs => some <| {e with modules := xs.toAssocList}.lower' (uncurry .base x.snd)
  | _ => none

def lower_TR (e : ExprHigh Ident) : Option (ExprLow Ident) :=
  match e.modules.toList with
  | x :: xs => some <| lower'_conn_TR e.connections <| lower'_prod_TR xs.toAssocList (uncurry .base x.snd)
  | _ => none

end ExprHigh

class FreshIdent (Ident : Type _) where
  next : Nat → Ident

instance : FreshIdent String where
  next n := "type" ++ toString n

instance : FreshIdent Nat where
  next := id

namespace ExprLow

variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

def higher' [FreshIdent Ident] (fresh : Nat) : ExprLow Ident → (ExprHigh Ident × Nat)
| .base a b =>
  (ExprHigh.mk [(a.ofPortMapping.getD (FreshIdent.next fresh), (a, b))].toAssocList ∅, fresh + 1)
| .connect c e =>
  let (e', fresh') := e.higher' fresh
  ({ e' with connections := e'.connections.cons c }, fresh')
| .product e₁ e₂ =>
  let (e₁', fresh₁) := e₁.higher' fresh
  let (e₂', fresh₂) := e₂.higher' fresh₁
  (⟨ e₁'.1.append e₂'.1, e₁'.2.append e₂'.2 ⟩, fresh₂)

def higher [Inhabited Ident] [FreshIdent Ident] (e: ExprLow Ident) : ExprHigh Ident :=
  e.higher' default |>.fst

def higherS' (fresh : Nat) (fresh_prefix : String) : ExprLow String → (ExprHigh String × Nat)
| .base a b =>
  (ExprHigh.mk [(fresh_prefix ++ toString fresh, (a, b))].toAssocList ∅, fresh + 1)
| .connect c e =>
  let (e', fresh') := e.higherS' fresh fresh_prefix
  ( {e' with connections := e'.connections.cons c }, fresh')
| .product e₁ e₂ =>
  let (e₁', fresh₁) := e₁.higherS' fresh fresh_prefix
  let (e₂', fresh₂) := e₂.higherS' fresh₁ fresh_prefix
  (⟨ e₁'.1.append e₂'.1, e₁'.2.append e₂'.2 ⟩, fresh₂)

def higherS (fresh_prefix : String) (e: ExprLow String) : ExprHigh String :=
  e.higherS' 0 fresh_prefix |>.fst

def _root_.Graphiti.PortMap.getInstanceName' (a : PortMap Ident (InternalPort Ident)) (i : Option Ident) : Option Ident :=
  match a with
  | .cons _ ⟨.top, n⟩ xs => getInstanceName' xs (match i with | .some _ => i | _ => .some n)
  | .cons _ ⟨.internal a, _⟩ _ => .some a
  | .nil => i

def _root_.Graphiti.PortMap.getInstanceName (a : PortMap Ident (InternalPort Ident)) : Option Ident := a.getInstanceName' .none

def _root_.Graphiti.PortMapping.getInstanceName (a : PortMapping Ident) : Option Ident :=
  a.output.getInstanceName' a.input.getInstanceName

def higherSS : ExprLow String → Option (ExprHigh String)
| .base a b => do
  return ExprHigh.mk [(← a.getInstanceName, (a, b))].toAssocList ∅
| .connect c e => do
  let e' ← e.higherSS
  return { e' with connections := e'.connections.cons c }
| .product e₁ e₂ => do
  let e₁' ← e₁.higherSS
  let e₂' ← e₂.higherSS
  return ⟨ e₁'.1.append e₂'.1, e₁'.2.append e₂'.2 ⟩

def _root_.Graphiti.InternalPort.toName : InternalPort String → String
| ⟨.top, a⟩ => a
| ⟨.internal a, b⟩ => s!"{a}.{b}"

def _root_.Graphiti.PortMap.toName (p : PortMap String (InternalPort String)) : String :=
  ":".intercalate <| p.toList.map (λ (x, y) => y.toName)

/--
Translates a PortMapping into a String, so that it can represent a key in the ExprHigh representation.  Ideally, this
would be a hashing algorithm.
-/
def _root_.Graphiti.PortMapping.toName (p : PortMapping String) : String :=
  s!"i={p.input.toName}|o={p.output.toName}"

section LowerToHigher

variable (compute_hash : PortMapping Ident → Ident)

def higher_correct_products : ExprLow Ident → Option (Batteries.AssocList Ident (PortMapping Ident × Ident))
| product (base inst typ) e => do
  let e' ← e.higher_correct_products
  return e'.cons (compute_hash inst) (inst, typ)
| base inst typ => do
  return .nil |>.cons (compute_hash inst) (inst, typ)
| _ => failure

def higher_correct_connections : ExprLow Ident → Option (ExprHigh Ident)
| connect c e => do
  let e' ← e.higher_correct_connections
  return { e' with connections := e'.connections.cons c }
| e => do
  let e' ← e.higher_correct_products compute_hash
  return { modules := e', connections := [] }

def get_all_products : ExprLow Ident → List (PortMapping Ident × Ident)
| base inst typ => [(inst, typ)]
| connect c e => get_all_products e
| product e₁ e₂ => get_all_products e₁ ++ get_all_products e₂

def higher_correct (e : ExprLow Ident) : Option (ExprHigh Ident) :=
  higher_correct_connections compute_hash (comm_bases (get_all_products e) e)

end LowerToHigher

end ExprLow

namespace ExprHigh

variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

@[drunfold] def reorder (g : ExprHigh Ident) (sub : List Ident) : ExprHigh Ident :=
  let m1 := g.modules.filter (λ k v => k ∈ sub)
  let m2 := g.modules.filter (λ k v => k ∉ sub)
  {g with modules := m1 ++ m2}

@[drunfold, drunfold_defs] def extract (g : ExprHigh Ident) (sub : List Ident)
    : Option (ExprHigh Ident × ExprHigh Ident) := do
  let modules : IdentMap Ident (PortMapping Ident × Ident) ← sub.foldlM (λ a b => do
      let l ← g.modules.find? b
      return a.cons b l
    ) ∅
  let mergedPortMapping : PortMapping Ident :=
    modules.foldl (λ pmap k v => pmap.append v.fst) ∅
  let connections := g.connections.partition
    (λ x => (mergedPortMapping.output.findEntryP? (λ _ k => k = x.output)).isSome
            && (mergedPortMapping.input.findEntryP? (λ _ k => k = x.input)).isSome)
  return (⟨ modules.toList.reverse.toAssocList, connections.fst ⟩, ⟨ g.modules.filter (λ k _ => k ∉ sub), connections.snd ⟩)

-- @[drunfold] def replace [FreshIdent Ident]
--   (g : ExprHigh Ident) (sub : List Ident) (g' : ExprHigh Ident)
--   : Option (ExprHigh Ident) := do
--   let e_sub ← (← g.extract sub) |>.lower
--   let g_lower := g.rest sub |>.lower' e_sub
--   let g'_lower ← g'.lower
--   g_lower.replace e_sub g'_lower |>.higher

@[drunfold]
def rename [FreshIdent Ident]
    (typ : Ident) (p : PortMapping Ident) (g : ExprHigh Ident) : Option (ExprHigh Ident) := do
  let g_lower ← g.lower
  g_lower.rename typ p |>.higher

def renamePorts f (g : ExprHigh Ident) (p : PortMapping Ident) := do
  let g_lower ← g.lower
  g_lower.renamePorts p >>= ExprLow.higher_correct f

def normaliseNames (e : ExprHigh String) : Option (ExprHigh String) :=
  let renameMap := e.modules.toList.map (λ (x, (inst, typ)) =>
    inst.mapKeys (λ keyPort bodyPort => if bodyPort.inst.isTop then bodyPort else ⟨.internal x, keyPort.name⟩))
      |> PortMapping.combinePortMapping
  e.renamePorts (λ x => PortMapping.getInstanceName x |>.getD default) renameMap

def renameModules (e : ExprHigh String) (map : Batteries.AssocList String String) :=
  let newModules := e.modules.mapKey (λ k => map.find? k |>.getD k)
  {e with modules := newModules}.normaliseNames

instance : ToString (ExprHigh String) where
  toString a :=
    -- let instances :=
    --   a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
    match a.normaliseNames with
    | some a =>
      let (io_decl, io_conn) := a.modules.foldl (λ (sdecl, sio) inst (pmap, typ) =>
        let sdecl := (pmap.input ++ pmap.output).foldl (λ sdecl k v =>
          if v.inst.isTop
          then sdecl ++ s!"\n  \"{v.name}\" [type = \"io\", label = \"{v.name}: io\"];"
          else sdecl) sdecl
        let sio := pmap.input.foldl (λ io_conn k v =>
          if v.inst.isTop
          then io_conn ++ s!"\n  \"{v.name}\" -> \"{inst}\" [to = \"{k.name}\", headlabel = \"{k.name}\"];"
          else io_conn) sio
        let sio := pmap.output.foldl (λ io_conn k v =>
          if v.inst.isTop
          then io_conn ++ s!"\n \"{inst}\" -> \"{v.name}\" [from = \"{k.name}\", taillabel = \"{k.name}\"];"
          else io_conn) sio
        (sdecl, sio)
      ) ("", "")
      let modules :=
        a.modules.foldl
          (λ s k v =>
            s ++ s!"  \"{k}\" [type = \"{v.snd}\", label = \"{k}: {v.snd}\"];\n"
            ) ""
      let connections :=
        a.connections.foldl
          (λ s => λ | ⟨ oport, iport ⟩ =>
                      s ++ s!"\n  \"{oport.inst}\" -> \"{iport.inst}\" "
                        ++ s!"[from = \"{oport.name}\","
                        ++ s!" to = \"{iport.name}\","
                        ++ s!" taillabel = \"{oport.name}\","
                        ++ s!" headlabel = \"{iport.name}\","
                        ++ "];") ""
      s!"digraph \{
{io_decl}
{modules}
{io_conn}
{connections}
}"
    | none => repr a |>.pretty

end ExprHigh

def updatePortMappingInput {α} [Inhabited α] (s : Std.HashMap String (PortMapping String × α))
  (inCluster : Bool)
  (inPort : InternalPort String)
  : Bool → InternalPort String → Std.HashMap String (PortMapping String × α)
| _, co@⟨.top, n⟩ =>
  match (inCluster, inPort) with
  | (true, ci@⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with output := a.output.cons ci co}, b)
  | (false, ⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with output := a.output.cons ⟨.top, y⟩ co}, b)
  | _ => s
| false, c@⟨.internal i, x⟩ =>
  let (a, b) := s[i]!
  s.insert i ({a with input := a.input.cons ⟨.top, x⟩ c}, b)
| true, ⟨.internal _, _⟩ => s

def updatePortMappingOutput {α} [Inhabited α] (s : Std.HashMap String (PortMapping String × α))
  (inCluster : Bool)
  (inPort : InternalPort String)
  : Bool → InternalPort String → Std.HashMap String (PortMapping String × α)
| _, co@⟨.top, n⟩ =>
  match (inCluster, inPort) with
  | (true, ci@⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with input := a.input.cons ci co}, b)
  | (false, ⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with input := a.input.cons ⟨.top, y⟩ co}, b)
  | _ => s
| false, c@⟨.internal i, x⟩ =>
  let (a, b) := s[i]!
  s.insert i ({a with output := a.output.cons ⟨.top, x⟩ c}, b)
| true, ⟨.internal _, _⟩ => s

def parseInternalPort (s : String) : Option (InternalPort String) :=
  match s.splitOn "." with
  | [single] => some ⟨.top, single⟩
  | [first, second] => some ⟨.internal first, second⟩
  | _ => none

structure InstMaps where
  instMap : Std.HashMap String (InstIdent String × Bool)
  instTypeMap : Std.HashMap String (PortMapping String × String)

def updateNodeMaps (maps : InstMaps) (inst typ : String) (cluster : Bool := false) : Except String InstMaps := do
  let mut instMap := maps.instMap
  let mut instTypeMap := maps.instTypeMap
  let mut modInst : InstIdent String := .top
  unless typ == "io" do modInst := .internal inst
  let (b, map') := instMap.containsThenInsertIfNew inst (modInst, cluster)
  if !b then
    instMap := map'
    -- IO "modules" are not added to the instTypeMap.
    unless typ == "io" do instTypeMap := instTypeMap.insert inst (∅, typ)
  else
    throw s!"Multiple references to {inst} found"
  return ⟨instMap, instTypeMap⟩

inductive ConnError where
| outInstError (s : String)
| inInstError (s : String)
| portError (s : String)

def ConnError.toString : ConnError → String
| .outInstError s => s
| .inInstError s => s
| .portError s => s

instance : ToString ConnError where
  toString c := c.toString

def updateConnMaps (maps : InstMaps) (conns : List (Connection String))
    (outInst inInst : String) (outP inP : Option String)
    : Except ConnError (InstMaps × List (Connection String)) := do
  let mut out := outP
  let mut inp := inP
  let some aInst := maps.instMap[outInst]? | throw (.outInstError s!"Instance has not been declared: {outInst}")
  let some bInst := maps.instMap[inInst]? | throw (.inInstError s!"Instance has not been declared: {inInst}")
  if aInst.fst = .top && bInst.fst = .top then
    throw <| .outInstError s!"Both the output \"{outInst}\" and input \"{inInst}\" are IO ports"
  -- If no port name is provided and the port is a top-level port, then use
  -- the instance name as the port name.
  if out.isNone && aInst.fst.isTop then out := some outInst
  if inp.isNone && bInst.fst.isTop then inp := some inInst
  let some out' := out | throw <| .portError s!"No output found for: {aInst}"
  let some inp' := inp | throw <| .portError s!"No input found for: {bInst}"
  let some outPort := parseInternalPort out'
    | throw <| .portError s!"Output port format incorrect: {out'}"
  let some inPort := parseInternalPort inp'
    | throw <| .portError s!"Input port format incorrect: {inp'}"
  -- If the instance is a cluster do not modify the name, otherwise as the
  -- instance as a prefix.
  let outPort' := if aInst.snd then outPort else ⟨aInst.fst, outPort.name⟩
  let inPort' := if bInst.snd then inPort else ⟨bInst.fst, inPort.name⟩
  -- If one of the end points is an external port then do not add a
  -- connection into the graph.
  let mut conns := conns
  let mut instTypeMap := maps.instTypeMap
  unless aInst.fst = .top || bInst.fst = .top do
    conns := ⟨ outPort', inPort' ⟩ :: conns
    instTypeMap := updatePortMappingOutput instTypeMap bInst.snd inPort' aInst.snd outPort'
    instTypeMap := updatePortMappingInput instTypeMap aInst.snd outPort' bInst.snd inPort'
  if aInst.fst = .top then
    instTypeMap := updatePortMappingOutput instTypeMap bInst.snd inPort' aInst.snd outPort'
  if bInst.fst = .top then
    instTypeMap := updatePortMappingInput instTypeMap aInst.snd outPort' bInst.snd inPort'
  return (⟨maps.instMap, instTypeMap⟩, conns)

end Graphiti
