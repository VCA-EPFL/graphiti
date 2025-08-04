/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Simp
import Graphiti.Core.Basic
import Graphiti.Core.AssocList

namespace Graphiti

structure Connection (Ident : Type _) where
  output : InternalPort Ident
  input  : InternalPort Ident
deriving Repr, Hashable, DecidableEq, Ord, Inhabited

/--
ExprLow is an inductive definition of a circuit, inspired by a definition by
Tony Law [?].  The main difference is the addition of input and output
constructors that essentially just rename a port to a top-level IO port.

An alternative definition of IO ports was considered, in that they could just be
a `base` module.  This has advantages because it makes the definition more
uniform, however, when building a `Module` from an `ExprLow`, one would have
additional state to be able to communicate from an input to the input for the
module.
-/
inductive ExprLow (Ident Typ : Type _) : Type _ where
| base (map : PortMapping Ident) (typ : Typ)
| product (l r : ExprLow Ident Typ)
| connect (c : Connection Ident) (e : ExprLow Ident Typ)
deriving Repr, Inhabited, DecidableEq

inductive NamedExprLow Ident Typ where
| input : InternalPort Ident → Ident → NamedExprLow Ident Typ → NamedExprLow Ident Typ
| output : InternalPort Ident → Ident → NamedExprLow Ident Typ → NamedExprLow Ident Typ
| base : ExprLow Ident Typ → NamedExprLow Ident Typ
deriving Repr, Inhabited, DecidableEq

inductive PosTree Ident where
| here (i : InternalPort Ident)
| left (l : PosTree Ident)
| right (r : PosTree Ident)
| both (l r : PosTree Ident)

inductive SExprLow Ident Typ where
| base (typ : Ident)
| product (l r : ExprLow Ident Typ)
| connect (e : ExprLow Ident Typ)

inductive NamelessPort (Ident : Type _) where
| bound (name : Nat)
| top (name : Ident)
deriving Repr, Hashable, Ord, Inhabited, DecidableEq

structure NamelessMapping (Ident) where
  input : PortMap Ident (NamelessPort Ident)
  output : PortMap Ident (NamelessPort Ident)
deriving Repr, Inhabited, DecidableEq

namespace ExprLow

variable {Ident Typ}
variable [DecidableEq Ident]
variable [DecidableEq Typ]

def ofOption {α ε} (e : ε) : Option α → Except ε α
| some o => .ok o
| none => .error e

@[drunfold] def build_mapping [Repr Ident] (map map' : PortMapping Ident) : Except String (PortMapping Ident) := do
  unless map.input.keysList.isPerm map'.input.keysList do
    throw s!"build_mapping error: input {map.input.keysList} is not a permutation of {map'.input.keysList}"
  unless map.output.keysList.isPerm map'.output.keysList do
    throw s!"build_mapping error: output {map.output.keysList} is not a permutation of {map'.output.keysList}"
  let inputMap ← map.input.foldlM
    (λ (a : PortMap Ident (InternalPort Ident)) k v => do
      let v' ← ofOption s!"build_mapping error: input: could not find {k} in {map'}" <| map'.input.find? k
      return a.cons v v'
    ) ∅
  let outputMap ← map.output.foldlM
    (λ (a : PortMap Ident (InternalPort Ident)) k v => do
      let v' ← ofOption s!"build_mapping error: output could not find {k} in {map'}" <| map'.output.find? k
      return a.cons v v'
    ) ∅
  return ⟨inputMap, outputMap⟩

@[drunfold] def beq [Repr Ident] [Repr Typ] : (e e' : ExprLow Ident Typ) → Except String (PortMapping Ident × PortMapping Ident)
| .base map typ, .base map' typ' => do
  unless typ = typ' do throw s!"beq error: types are not equal: {repr typ} vs {repr typ'}"
  build_mapping map map' |>.map (Prod.mk · ∅)
| .connect c e, .connect c' e' => do
  let (map, int_map) ← e.beq e'
  let o_in_map ← ofOption "beq error: could not find output in map" <| map.output.find? c.output
  let i_in_map ← ofOption "beq error: could not find input in map" <| map.input.find? c.input
  unless o_in_map = c'.output do throw s!"beq error: o_in_map ({o_in_map}) ≠ c'.output ({c'.output})"
  unless i_in_map = c'.input do throw s!"beq error: i_in_map ({i_in_map}) ≠ c'.input ({c'.input})"
  return ( {map with input := map.input.eraseAll c.input, output := map.output.eraseAll c.output}
         , {int_map with input := int_map.input.cons c.input c'.input, output := int_map.output.cons c.output c'.output}
         )
| .product e₁ e₂, .product e₁' e₂' => do
  let (map₁, int_map₁) ← e₁.beq e₁'
  let (map₂, int_map₂) ← e₂.beq e₂'
  unless map₁.input.disjoint_keys map₂.input do throw "beq error: map₁.input not disjoint from map₂.input"
  unless map₁.output.disjoint_keys map₂.output do throw "beq error: map₁.output not disjoint from map₂.output"
  unless int_map₁.input.disjoint_keys int_map₂.input do throw "beq error: int_map₁.input not disjoint from int_map₂.input"
  unless int_map₁.output.disjoint_keys int_map₂.output do do throw "beq error: int_map₁.output not disjoint from int_map₂.output"
  return ( ⟨map₁.input.append map₂.input, map₁.output.append map₂.output⟩
         , ⟨int_map₁.input.append int_map₂.input, int_map₁.output.append int_map₂.output⟩
         )
| _, _ => throw "beq error: expressions are structurally not similar"

@[drunfold] def weak_beq [Repr Ident] [Repr Typ] : (e e' : ExprLow Ident Typ) → Except String (PortMapping Ident × PortMapping Ident)
| .base map typ, .base map' typ' => do
  unless typ = typ' do throw s!"beq error: types are not equal: {repr typ} vs {repr typ'}"
  build_mapping map map' |>.map (Prod.mk · ∅)
| .connect c e, .connect c' e' => do
  let (map, int_map) ← e.weak_beq e'
  let o_in_map ← ofOption "beq error: could not find output in map" <| map.output.find? c.output
  let i_in_map ← ofOption "beq error: could not find input in map" <| map.input.find? c.input
  -- unless o_in_map = o' do throw s!"beq error: o_in_map ({o_in_map}) ≠ o' ({o'})"
  -- unless i_in_map = i' do throw s!"beq error: i_in_map ({i_in_map}) ≠ i' ({i'})"
  return ( {map with input := map.input.eraseAll c.input, output := map.output.eraseAll c.output}
         , {int_map with input := int_map.input.cons c.input i_in_map, output := int_map.output.cons c.output o_in_map}
         )
| .product e₁ e₂, .product e₁' e₂' => do
  let (map₁, int_map₁) ← e₁.weak_beq e₁'
  let (map₂, int_map₂) ← e₂.weak_beq e₂'
  unless map₁.input.disjoint_keys map₂.input do throw "beq error: map₁.input not disjoint from map₂.input"
  unless map₁.output.disjoint_keys map₂.output do throw "beq error: map₁.output not disjoint from map₂.output"
  unless int_map₁.input.disjoint_keys int_map₂.input do throw "beq error: int_map₁.input not disjoint from int_map₂.input"
  unless int_map₁.output.disjoint_keys int_map₂.output do do throw "beq error: int_map₁.output not disjoint from int_map₂.output"
  return ( ⟨map₁.input.append map₂.input, map₁.output.append map₂.output⟩
         , ⟨int_map₁.input.append int_map₂.input, int_map₁.output.append int_map₂.output⟩
         )
| _, _ => throw "beq error: expressions are structurally not similar"

@[drunfold] def build_interface : ExprLow Ident Typ → Interface Ident
| .base map typ => map.toInterface'
| .connect c e =>
  let int := e.build_interface
  ⟨int.input.erase c.input, int.output.erase c.output⟩
| product e₁ e₂ =>
  let int₁ := e₁.build_interface
  let int₂ := e₂.build_interface
  ⟨int₁.input ++ int₂.input, int₁.output ++ int₂.output⟩

@[drunfold] def allVars : ExprLow Ident Typ → (List (InternalPort Ident) × List (InternalPort Ident))
| .base map typ =>
  (map.input.toList.map Prod.snd, map.output.toList.map Prod.snd)
| .connect _ e => e.allVars
| .product e₁ e₂ =>
  let (e₁i, e₁o) := e₁.allVars
  let (e₂i, e₂o) := e₂.allVars
  (e₁i ++ e₂i, e₁o ++ e₂o)

@[drunfold] def modify (i i' : Typ) : ExprLow Ident Typ → ExprLow Ident Typ
| .base inst typ => if typ = i then .base inst i' else .base inst typ
| .connect c e' => modify i i' e' |> .connect c
| .product e₁ e₂ =>
  let e₁' := e₁.modify i i'
  let e₂' := e₂.modify i i'
  .product e₁' e₂'

/--
Check that two expressions are equal, assuming that the port assignments are
fully specified and therefore symmetric in both expressions.
-/
@[drunfold] def check_eq : ExprLow Ident Typ → ExprLow Ident Typ → Bool
| .base inst typ, .base inst' typ' =>
  -- let inst_i := inst.input.filterId
  -- let inst_o := inst.output.filterId
  -- let inst'_i := inst'.input.filterId
  -- let inst'_o := inst'.output.filterId
  typ = typ'
  ∧ inst'.input.EqExt inst.input ∧ inst'.output.EqExt inst.output
  ∧ inst'.input.keysList.Nodup ∧ inst.output.keysList.Nodup
  ∧ inst'.output.keysList.Nodup ∧ inst.input.keysList.Nodup
  -- ∧ inst'_i.EqExt inst_i ∧ inst'_o.EqExt inst_o
  -- ∧ inst'_i.keysList.Nodup ∧ inst_i.keysList.Nodup
  -- ∧ inst'_o.keysList.Nodup ∧ inst_o.keysList.Nodup
| .connect c e, .connect c' e' => c = c' ∧ e.check_eq e'
| .product e₁ e₂, .product e₁' e₂' => e₁.check_eq e₁' ∧ e₂.check_eq e₂'
| _, _ => false

@[drunfold] def replace (e e_sub e_new : ExprLow Ident Typ) : ExprLow Ident Typ :=
  if e.check_eq e_sub then e_new else
  match e with
  | .base inst typ => e
  | .connect c e_sub' => .connect c (e_sub'.replace e_sub e_new)
  | .product e_sub₁ e_sub₂ =>
    .product (e_sub₁.replace e_sub e_new) (e_sub₂.replace e_sub e_new)

@[drunfold] def force_replace (e e_sub e_new : ExprLow Ident Typ) : (ExprLow Ident Typ × Bool) :=
  if e.check_eq e_sub then (e_new, true) else
  match e with
  | .base inst typ => (e, false)
  | .connect c e_sub' =>
    let rep := e_sub'.force_replace e_sub e_new
    (.connect c rep.1, rep.2)
  | .product e_sub₁ e_sub₂ =>
    let e_sub₁_rep := e_sub₁.force_replace e_sub e_new
    let e_sub₂_rep := e_sub₂.force_replace e_sub e_new
    (.product e_sub₁_rep.1 e_sub₂_rep.1, e_sub₁_rep.2 || e_sub₂_rep.2)

@[drunfold]
def abstract (e e_sub : ExprLow Ident Typ) (i_inst : PortMapping Ident) (i_typ : Typ) : ExprLow Ident Typ :=
  .base i_inst i_typ |> e.replace e_sub

@[drunfold]
def force_abstract (e e_sub : ExprLow Ident Typ) (i_inst : PortMapping Ident) (i_typ : Typ) : ExprLow Ident Typ × Bool :=
  .base i_inst i_typ |> e.force_replace e_sub

@[drunfold]
def concretise (e e_sub : ExprLow Ident Typ) (i_inst : PortMapping Ident) (i_typ : Typ) : ExprLow Ident Typ :=
  .base i_inst i_typ |> (e.replace · e_sub)

@[drunfold]
def force_concretise (e e_sub : ExprLow Ident Typ) (i_inst : PortMapping Ident) (i_typ : Typ) : ExprLow Ident Typ × Bool :=
  .base i_inst i_typ |> (e.force_replace · e_sub)

@[drunfold]
def normalisedNamesMap' (pref : String) (count : Nat) : ExprLow String String → (PortMapping String × Nat)
| .base port typ' =>
  let p := port.inverse.mapPairs
    (λ | ⟨.top, n⟩, v => ⟨.top, n⟩
       | ⟨.internal _, _⟩, ⟨_, n⟩ => ⟨.internal <| pref ++ toString count, n⟩)
    |>.filter (λ | ⟨.top, _⟩, _ => false | _, _ => true)
  (p, count + 1)
| .connect _ e => normalisedNamesMap' pref count e
| .product e₁ e₂ =>
  let (p₁, count₁) := normalisedNamesMap' pref count e₁
  let (p₂, count₂) := normalisedNamesMap' pref count₁ e₂
  (p₁.append p₂, count₂)

@[drunfold]
def normalisedNamesMap (pref : String) (e : ExprLow String String) : PortMapping String :=
  normalisedNamesMap' pref 0 e |>.fst

def findBase (typ : Typ) : ExprLow Ident Typ → Option (PortMapping Ident)
| .base port typ' => if typ = typ' then some port else none
| .connect _ e => e.findBase typ
| .product e₁ e₂ =>
  match e₁.findBase typ with
  | some port => port
  | none => e₂.findBase typ

@[drunfold]
def mapInputPorts (f : InternalPort Ident → InternalPort Ident) : ExprLow Ident Typ → Option (ExprLow Ident Typ)
| .base map typ' => do
  let res := map.input |>.mapVal (fun _ => f)
  guard res.invertible
  return .base ⟨res, map.output⟩ typ'
| .connect c e => do
  let mapped ← e.mapInputPorts f
  return .connect { c with input := f c.input } mapped
| .product e₁ e₂ => do
  let e₁_mapped ← e₁.mapInputPorts f
  let e₂_mapped ← e₂.mapInputPorts f
  return .product e₁_mapped e₂_mapped

@[drunfold]
def mapOutputPorts (f : InternalPort Ident → InternalPort Ident) : ExprLow Ident Typ → Option (ExprLow Ident Typ)
| .base map typ' => do
  let res := map.output |>.mapVal (fun _ => f)
  guard res.invertible
  return .base ⟨map.input, res⟩ typ'
| .connect c e => do
  let e_mapped ← e.mapOutputPorts f
  return .connect { c with output := f c.output } e_mapped
| .product e₁ e₂ => do
  let e₁_mapped ← e₁.mapOutputPorts f
  let e₂_mapped ← e₂.mapOutputPorts f
  return .product e₁_mapped e₂_mapped

@[drunfold]
def mapPorts2 (f g : InternalPort Ident → InternalPort Ident) (e : ExprLow Ident Typ) : Option (ExprLow Ident Typ) :=
  e.mapInputPorts f >>= mapOutputPorts g

@[drunfold]
def renamePorts (m : ExprLow Ident Typ) (p : PortMapping Ident) : Option (ExprLow Ident Typ) :=
  m.mapPorts2 p.input.bijectivePortRenaming p.output.bijectivePortRenaming

def mapInputPorts' (f : InternalPort Ident → InternalPort Ident) : ExprLow Ident Typ → ExprLow Ident Typ
| .base map typ' => .base ⟨map.input.mapVal (λ _ => f), map.output⟩ typ'
| .connect c e => e.mapInputPorts' f |> .connect { c with input := f c.input }
| .product e₁ e₂ => .product (e₁.mapInputPorts' f) (e₂.mapInputPorts' f)

def mapOutputPorts' (f : InternalPort Ident → InternalPort Ident) : ExprLow Ident Typ → ExprLow Ident Typ
| .base map typ' => .base ⟨map.input, map.output.mapVal (λ _ => f)⟩ typ'
| .connect c e => e.mapOutputPorts' f |> .connect { c with output := f c.output }
| .product e₁ e₂ => .product (e₁.mapOutputPorts' f) (e₂.mapOutputPorts' f)

def mapPorts2' [Inhabited Ident] (f g : InternalPort Ident → InternalPort Ident) (e : ExprLow Ident Typ) : ExprLow Ident Typ :=
  e.mapInputPorts' f |>.mapOutputPorts' g

def renamePorts' [Inhabited Ident] (m : ExprLow Ident Typ) (p : PortMapping Ident) : ExprLow Ident Typ :=
  m.mapPorts2' p.input.bijectivePortRenaming p.output.bijectivePortRenaming

/--
Assume that the input is currently not mapped.
-/
@[drunfold]
def renameUnmappedInput (typ : Typ) (a b : InternalPort Ident) : ExprLow Ident Typ → ExprLow Ident Typ
| .base map typ' =>
  if typ = typ' && (map.input.find? a).isNone then
    .base {map with input := map.input |>.cons a b} typ
  else
    .base map typ'
| .connect c e =>
  let e' := e.renameUnmappedInput typ a b
  if c.input = a then .connect { c with input := b } e' else .connect c e'
| .product e₁ e₂ =>
  .product (e₁.renameUnmappedInput typ a b) (e₂.renameUnmappedInput typ a b)

/--
Assume that the input is mapped.
-/
@[drunfold]
def renameMappedInput (a b : InternalPort Ident) : ExprLow Ident Typ → ExprLow Ident Typ
| .base map typ =>
  .base {map with input := map.input.mapVal (λ k v => if v = a then b else v)} typ
| .connect c e =>
  let e' := e.renameMappedInput a b
  if c.input = a then .connect { c with input := b } e' else .connect c e'
| .product e₁ e₂ =>
  .product (e₁.renameMappedInput a b) (e₂.renameMappedInput a b)

@[drunfold]
def calc_mapping : ExprLow Ident Typ → PortMapping Ident
| .base inst typ => inst
| .connect _ e => e.calc_mapping
| .product e₁ e₂ => e₁.calc_mapping ++ e₂.calc_mapping

def all (P : Typ → Bool) : ExprLow Ident Typ → Bool
| base f typ => P typ
| connect _ e => e.all P
| product e₁ e₂ => e₁.all P && e₂.all P

def all' (P : PortMapping Ident → Typ → Bool) : ExprLow Ident Typ → Bool
| base f typ => P f typ
| connect _ e => e.all' P
| product e₁ e₂ => e₁.all' P && e₂.all' P

def any (P : Typ → Bool) : ExprLow Ident Typ → Bool
| base f typ => P typ
| connect _ e => e.any P
| product e₁ e₂ => e₁.any P || e₂.any P

def excludes (ident : Typ) : ExprLow Ident Typ → Bool := all (· ≠ ident)

def _root_.List.eraseAll {α} [DecidableEq α] : List α → α → List α
| [],    _ => []
| a::as, b => match a == b with
  | true  => List.eraseAll as b
  | false => a :: List.eraseAll as b

def findAllInputs : ExprLow Ident Typ → List (InternalPort Ident)
| .base inst _typ => inst.input.valsList
| .product e₁ e₂ => e₁.findAllInputs ++ e₂.findAllInputs
| .connect c e => e.findAllInputs.eraseAll c.input

def findAllOutputs : ExprLow Ident Typ → List (InternalPort Ident)
| .base inst _typ => inst.input.valsList
| .product e₁ e₂ => e₁.findAllOutputs ++ e₂.findAllOutputs
| .connect c e => e.findAllOutputs.eraseAll c.input

/--
Find input and find output imply that build_module will contain that key
-/
def findInput (i : InternalPort Ident) : ExprLow Ident Typ → Bool
| .base inst _typ => inst.input.any (λ _ a => a = i)
| .product e₁ e₂ => findInput i e₁ ∨ findInput i e₂
| .connect c e => c.input ≠ i ∧ findInput i e

def findOutput (o : InternalPort Ident) : ExprLow Ident Typ → Bool
| .base inst _typ => inst.output.any (λ _ a => a = o)
| .product e₁ e₂ => findOutput o e₁ ∨ findOutput o e₂
| .connect c e => c.output ≠ o ∧ findOutput o e

def ensureIOUnmodified' (p : PortMapping Ident) (e : ExprLow Ident Typ) : Bool :=
  e.findAllInputs.all (λ x => (p.input.find? x).isNone)
  ∧ e.findAllOutputs.all (λ x => (p.output.find? x).isNone)

def ensureIOUnmodified_efficient [DecidableEq Ident] (p : PortMapping Ident) (e : ExprLow Ident Typ) : Bool := true

-- @[implemented_by ensureIOUnmodified_efficient]
def ensureIOUnmodified (p : PortMapping Ident) (e : ExprLow Ident Typ) : Bool :=
  p.input.keysList.all (e.findInput · == false)
  ∧ p.input.valsList.all (e.findInput · == false)
  ∧ p.output.keysList.all (e.findOutput · == false)
  ∧ p.output.valsList.all (e.findOutput · == false)

def fix_point (f : ExprLow Ident Typ → ExprLow Ident Typ) (e : ExprLow Ident Typ): Nat → ExprLow Ident Typ
| 0 => e
| n+1 => let e' := f e; if e' = e then e else fix_point f e' n

def fix_point_opt (f : ExprLow Ident Typ → Option (ExprLow Ident Typ)) (e : ExprLow Ident Typ): Nat → ExprLow Ident Typ
| 0 => e
| n+1 =>
  match f e with
  | .some e' => fix_point_opt f e' n
  | .none => e

def inst_disjoint (inst inst' : PortMapping Ident) : Bool :=
  inst'.input.disjoint_vals inst.input ∧ inst'.output.disjoint_vals inst.output

def comm_connection'_ (conn : Connection Ident) : ExprLow Ident Typ → Option (ExprLow Ident Typ)
| .connect c e =>
  if c.output = conn.output ∧ c.input = conn.input then
    match e with
    | .connect c' e' =>
      if c.output ≠ c'.output ∧ c.input ≠ c'.input then
        .some (.connect c' (.connect c e'))
      else .none
    | .product e₁ e₂ =>
      let a := e₁.findInput c.input
      let b := e₁.findOutput c.output
      if a ∧ b then
        -- .product (comm_connection' conn <| .connect o i e₁) e₂
        -- We actually don't want to commute (assuming we are left associative)
        .none
      else if ¬ a ∧ ¬ b ∧ e₂.findInput c.input ∧ e₂.findOutput c.output then
        .some (.product e₁ (.connect c e₂))
      else .none
    | _ => .none
  else .connect c <$> comm_connection'_ conn e
| .product e₁ e₂ =>
  match (comm_connection'_ conn e₁), (comm_connection'_ conn e₂) with
  | .some e₁, .some e₂ | .some e₁, .none | .none, .some e₂ => .some <| .product e₁ e₂
  | .none, .none => .none
| e => .none

def comm_connection' (conn : Connection Ident) (e : ExprLow Ident Typ) := fix_point_opt (comm_connection'_ conn) e 10000

def comm_connection_ (conn : Connection Ident) : ExprLow Ident Typ → ExprLow Ident Typ
| orig@(.connect c e) =>
  if c.output = conn.output ∧ c.input = conn.input then
    match e with
    | .connect c' e' =>
      if c.output ≠ c'.output ∧ c.input ≠ c'.input then
        .connect c' (.connect c e')
      else orig
    | _ => orig
  else .connect c <| comm_connection_ conn e
| .product e₁ e₂ =>
  .product (comm_connection_ conn e₁) (comm_connection_ conn e₂)
| e => e

def comm_connection (conn : Connection Ident) (e : ExprLow Ident Typ) := fix_point (comm_connection_ conn) e 10000

/- Assuming a left-associative expression. -/
def comm_base_ {Ident} [DecidableEq Ident] (binst : PortMapping Ident) (btyp : Typ) : ExprLow Ident Typ → Option (ExprLow Ident Typ)
| .product e₁ e₂ =>
  if e₁ = .base binst btyp then
    match e₂ with
    | .product (.base binst' btyp') e₂' =>
      if inst_disjoint binst' binst then
        .some <| .product (.base binst' btyp') (.product e₁ e₂')
      else .none
    | .connect c e =>
      if c.output ∉ binst.output.valsList ∧ c.input ∉ binst.input.valsList then
        .some <| .connect c (.product e₁ e)
      else .none
    | .base binst' btyp' =>
      if inst_disjoint binst' binst then .some <| .product e₂ e₁ else .none
    | _ => .none
  else .product e₁ <$> comm_base_ binst btyp e₂
| .connect c e => .connect c <$> comm_base_ binst btyp e
| e => .none

def comm_connection_inv_ : ExprLow Ident Typ → Option (ExprLow Ident Typ)
| .connect c e =>
  .connect c <$> comm_connection_inv_ e
| .product e₁ e₂ =>
  match e₂ with
  | .connect c e₂ =>
    if ¬ e₁.findInput c.input ∧ ¬ e₁.findOutput c.output then
      .some <| .connect c (.product e₁ e₂)
    else
      .none
  | _ => .product e₁ <$> comm_connection_inv_ e₂
| _ => .none

def comm_connection_inv (e : ExprLow Ident Typ) := fix_point_opt comm_connection_inv_ e 10000

def comm_base (binst : PortMapping Ident) (btyp : Typ) e := fix_point_opt (comm_base_ binst btyp) e 10000

def comm_connections' {Ident} [DecidableEq Ident] (conn : List (Connection Ident)) (e : ExprLow Ident Typ): ExprLow Ident Typ :=
  conn.foldr comm_connection' e

def comm_connections {Ident} [DecidableEq Ident] (conn : List (Connection Ident)) (e : ExprLow Ident Typ): ExprLow Ident Typ :=
  conn.foldr comm_connection e

def comm_bases {Ident} [DecidableEq Ident] (bases : List (PortMapping Ident × Typ)) (e : ExprLow Ident Typ): ExprLow Ident Typ :=
  bases.foldr (Function.uncurry ExprLow.comm_base) e

def getPortMaps : ExprLow String String → List (PortMapping String)
| .base inst typ => [inst]
| .connect c e => getPortMaps e
| .product e₁ e₂ => getPortMaps e₁ ++ getPortMaps e₂

end ExprLow
end Graphiti
