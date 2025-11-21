/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Qq

import Graphiti.Core.ExprHigh
import Graphiti.Core.Component

namespace Graphiti

declare_syntax_cat dot_value
declare_syntax_cat dot_stmnt
declare_syntax_cat dot_attr_list
declare_syntax_cat dot_attr

scoped syntax str : dot_value
scoped syntax num : dot_value
scoped syntax ident : dot_value
scoped syntax (name := dot_value_term) "$(" term ")" : dot_value
scoped syntax "from" : dot_value
scoped syntax "to" : dot_value

scoped syntax dot_value " = " dot_value : dot_attr
scoped syntax (dot_attr),* : dot_attr_list

scoped syntax ident (" [" dot_attr_list "]")? : dot_stmnt
scoped syntax ident " -> " ident (" [" dot_attr_list "]")? : dot_stmnt

syntax dot_stmnt_list := (dot_stmnt "; ")*

syntax dot_input_list := ("(" ident ", " num ")"),*

scoped syntax (name := dot_graph) "[graph| " dot_stmnt_list " ]" : term
scoped syntax (name := dot_graphEnv) "[graphEnv| " dot_stmnt_list " ]" : term

open Lean.Meta Lean.Elab Term Lean.Syntax

open Lean in
def isFrom : Syntax -> Bool
| `(dot_value| from) => true
| _ => false

open Lean in
def isTo : Syntax -> Bool
| `(dot_value| to) => true
| _ => false

open Lean in
def checkName (n : Name) (s : Syntax) : Bool :=
  s[0].getId == n || (isFrom s && n == `from) || (isTo s && n == `to)

open Lean in
def findStx (n : Name) (stx : Array Syntax) : Option Nat := do
  let mut out := none
  for pair in stx do
    if checkName n pair[0] then
      out := some (TSyntax.mk pair[2][0]).getNat
  out

open Lean Qq in
@[term_elab dot_value_term]
def dotValueTermElab : TermElab
| `(dot_value| $( $a:term )), t => elabTerm a t
| _, _ => throwError "Could not match syntax"

open Lean in
def hasStxElement (n : Name) (stx : Array Syntax) : Bool := Id.run do
  let mut out := false
  for pair in stx do
    if checkName n pair[0] then
      out := true
  out

open Lean in
def getListElement (n : Name) (stx : Array Syntax) : MetaM Syntax := do
  let mut out : Option Syntax := .none
  for pair in stx do
    if checkName n pair[0] then
      out := .some pair
  return out.getD (← getRef)

open Lean in
def findStxBool (n : Name) (stx : Array Syntax) : Option Bool := do
  let mut out := none
  for pair in stx do
    if checkName n pair[0] then
      out := match pair[2] with
             | `(dot_value| true) => .some true
             | `(dot_value| false) => .some false
             | _ => .none
  out

open Lean in
def findStxStr (n : Name) (stx : Array Syntax) : MetaM (Option String) := do
  let mut out := none
  for pair in stx do
    if checkName n pair[0] then
      let some out' := pair[2][0].isStrLit?
        | throwErrorAt pair[2][0] "`type` attribute is not a string"
      out := some out'
  return out

open Lean Qq in
def findStxStr' (n : Name) (stx : Array Syntax) : TermElabM (Option Q(String)) := do
  let mut out := none
  for pair in stx do
    if checkName n pair[0] then
      match pair[2][0].isStrLit? with
      | .some out' => out := .some <| .lit <| .strVal out'
      | .none =>
        let term ← elabTermEnsuringType pair[2] <| .some q(String)
        out := some term
  return out

open Lean Qq in
def findStxNat' (n : Name) (stx : Array Syntax) : TermElabM (Option Q(Nat)) := do
  let mut out := none
  for pair in stx do
    if checkName n pair[0] then
      match pair[2][0].isNatLit? with
      | .some out' => out := .some <| .lit <| .natVal out'
      | .none =>
        let term ← elabTermEnsuringType pair[2] <| .some q(Nat)
        out := some term
  return out

open Lean Qq in
def findStxTerm (n : Name) (stx : Array Syntax) : TermElabM (Option (Expr × String)) := do
  let mut out := none
  for pair in stx do
    if checkName n pair[0] ∧ pair[2][0].isStrLit?.isNone then
    -- let content : TSyntax `term := ⟨pair[2][1]⟩
    -- let depPair ← `(term| Sigma.mk _ $content)
    let term ← elabTermEnsuringType pair[2] <| .some q(TModule1 String)
    let str ← ppTerm {env := ← getEnv } ⟨pair[2][1]⟩
    out := some (term, Format.pretty str)
  return out

def toInstIdent {α} [Inhabited α] (n : String) (h : Std.HashMap String α) : InstIdent α :=
  match n with
  | "io" => .top
  | s => .internal h[s]!

open Lean Qq in
def reifyInternalPort : InternalPort String → Q(InternalPort String)
| ⟨ .top, s ⟩ =>
  let s' : Q(String) := .lit (.strVal s)
  q(InternalPort.mk .top $s')
| ⟨ .internal a, b ⟩ =>
  let a' : Q(String) := .lit (.strVal a)
  let b' : Q(String) := .lit (.strVal b)
  q(InternalPort.mk (.internal $a') $b')

open Lean Qq in
def reifyInternalPort' {u : Level} {α : Q(Type $u)} : InternalPort Q($α) → Q(InternalPort $α)
| ⟨ .top, s ⟩ => q(InternalPort.mk .top $s)
| ⟨ .internal a, b ⟩ => q(InternalPort.mk (.internal $a) $b)

-- open Lean Qq in
-- def reifyPortMapping (p : PortMapping String) : Q(PortMapping String) :=
--   q(@PortMapping.mk String )

open Lean Qq in
def mkAssocListExpr {u : Level} {α β : Q(Type $u)}
  : Batteries.AssocList Q($α) Q($β) → Q(Batteries.AssocList $α $β)
| .cons a b r => let r' := mkAssocListExpr r; q(.cons $a $b $r')
| .nil => q(.nil)

open Lean Qq in
def mkPortMapping {u : Level} {α : Q(Type $u)} : PortMapping Q($α) → Q(PortMapping $α)
| ⟨ a, b ⟩ =>
  let a' := a.mapKey reifyInternalPort' |>.mapVal (λ _ => reifyInternalPort') |> mkAssocListExpr
  let b' := b.mapKey reifyInternalPort' |>.mapVal (λ _ => reifyInternalPort') |> mkAssocListExpr
  q(@PortMapping.mk $α $a' $b')

open Lean Qq in
def isIO (i : Q(String)) : Bool := i == .lit (.strVal "io")

#check Lean.Expr

open Lean Qq in
@[term_elab dot_graph]
def dotGraphElab : TermElab := λ stx typ? =>
  match typ? with
  | some a => do
    if ← isDefEq a q(ExprHigh String String) then go stx
    else if ← isDefEq a q(ExprHigh String (String × Nat)) then go'' stx
         else go' stx
  | none => go stx
  where
    go (stx : Syntax) := do
      let mut instMap : Std.HashMap String (InstIdent String × Bool) := ∅
      let mut instTypeMap : Std.HashMap String (PortMapping String × Q(String)) := ∅
      let mut conns : List (Connection String) := []
      for stmnt in stx[1][0].getArgs do
        let low_stmnt := stmnt.getArgs[0]!
        match low_stmnt with
        | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
          let some el := el
            | throwErrorAt i "Element list is not present"
          let some modId ← findStxStr' `type el
            | throwErrorAt i "No `type` attribute found at node"
          let mut modCluster : Bool := findStxBool `cluster el |>.getD false
          match updateNodeMaps ⟨instMap, instTypeMap⟩ i.getId.toString modId (isIO modId) modCluster with
          | .ok ⟨a, b⟩ =>
            instMap := a
            instTypeMap := b
          | .error s =>
            throwErrorAt i s
        | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
          -- Error checking to report it early if the instance is not present in the
          -- hashmap.
          let some el := el
            | throwErrorAt (mkListNode #[a, b]) "No `type` attribute found at node"
          let mut out ← (findStxStr `from el)
          let mut inp ← (findStxStr `to el)
          match updateConnMaps ⟨instMap, instTypeMap⟩ conns a.getId.toString b.getId.toString out inp with
          | .ok (⟨_, b⟩, c) =>
            conns := c
            instTypeMap := b
          | .error (.outInstError s) => throwErrorAt a s
          | .error (.inInstError s) => throwErrorAt b s
          | .error (.portError s) => throwErrorAt (mkListNode el) s
        | _ => pure ()
      let connExpr : Q(List (Connection String)) ←
        mkListLit q(Connection String) (← conns.mapM (λ ⟨ a, b ⟩ => do
          mkAppM ``Connection.mk #[reifyInternalPort a, reifyInternalPort b]))
      let modList : Q(List (String × (PortMapping String × String))) ←
        mkListLit q(String × (PortMapping String × String))
          (instTypeMap.toList.map (fun (a, (p, b)) =>
            let a' : Q(String) := .lit (.strVal a)
            let b' : Q(String) := b
            let p' : Q(PortMapping String) := mkPortMapping <| p.map (.strVal · |> .lit)
            q(($a', ($p', $b')))))
      let modListMap : Q(IdentMap String (PortMapping String × String)) := q(List.toAssocList $modList)
      return q(ExprHigh.mk $modListMap $connExpr)

    go' (stx : Syntax) : TermElabM Expr := do
      let mut instMap : Std.HashMap String (InstIdent String × Bool) := ∅
      let mut instTypeMap : Std.HashMap String (PortMapping String × (Q(String) × Q(String))) := ∅
      let mut conns : List (Connection String) := []
      for stmnt in stx[1][0].getArgs do
        let low_stmnt := stmnt.getArgs[0]!
        match low_stmnt with
        | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
          let some el := el
            | throwErrorAt i "Element list is not present"
          let some modId ← findStxStr' `type el
            | throwErrorAt i "No `type` attribute found at node"
          let mut modCluster : Bool := findStxBool `cluster el |>.getD false
          if isIO modId then
            match updateNodeMaps ⟨instMap, instTypeMap⟩ i.getId.toString (modId, default) (isIO modId) modCluster with
            | .ok ⟨a, b⟩ =>
              instMap := a
              instTypeMap := b
            | .error s =>
              throwErrorAt i s
          else
            let some modIdArgs ← findStxStr' `arg el
              | throwErrorAt i "No `arg` attribute found at node"
            match updateNodeMaps ⟨instMap, instTypeMap⟩ i.getId.toString (modId, modIdArgs) (isIO modId) modCluster with
            | .ok ⟨a, b⟩ =>
              instMap := a
              instTypeMap := b
            | .error s =>
              throwErrorAt i s
        | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
          -- Error checking to report it early if the instance is not present in the
          -- hashmap.
          let some el := el
            | throwErrorAt (mkListNode #[a, b]) "No `type` attribute found at node"
          let mut out ← (findStxStr `from el)
          let mut inp ← (findStxStr `to el)
          match updateConnMaps ⟨instMap, instTypeMap⟩ conns a.getId.toString b.getId.toString out inp with
          | .ok (⟨_, b⟩, c) =>
            conns := c
            instTypeMap := b
          | .error (.outInstError s) => throwErrorAt a s
          | .error (.inInstError s) => throwErrorAt b s
          | .error (.portError s) => throwErrorAt (mkListNode el) s
        | _ => pure ()
      let connExpr : Q(List (Connection String)) ←
        mkListLit q(Connection String) (← conns.mapM (λ ⟨ a, b ⟩ => do
          mkAppM ``Connection.mk #[reifyInternalPort a, reifyInternalPort b]))
      let modList : Q(List (String × (PortMapping String × (String × String)))) ←
        mkListLit q(String × (PortMapping String × (String × String)))
          (instTypeMap.toList.map (fun (a, (p, b)) =>
            let a' : Q(String) := .lit (.strVal a)
            let b' : Q(String) := b.1
            let b'' : Q(String) := b.2
            let p' : Q(PortMapping String) := mkPortMapping <| p.map (.strVal · |> .lit)
            q(($a', ($p', ($b', $b''))))))
      let modListMap : Q(IdentMap String (PortMapping String × (String × String))) := q(List.toAssocList $modList)
      return q(ExprHigh.mk $modListMap $connExpr)

    go'' (stx : Syntax) : TermElabM Expr := do
      let mut instMap : Std.HashMap String (InstIdent String × Bool) := ∅
      let mut instTypeMap : Std.HashMap String (PortMapping String × (Q(String) × Q(Nat))) := ∅
      let mut conns : List (Connection String) := []
      for stmnt in stx[1][0].getArgs do
        let low_stmnt := stmnt.getArgs[0]!
        match low_stmnt with
        | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
          let some el := el
            | throwErrorAt i "Element list is not present"
          let some modId ← findStxStr' `type el
            | throwErrorAt i "No `type` attribute found at node"
          let mut modCluster : Bool := findStxBool `cluster el |>.getD false
          if isIO modId then
            match updateNodeMaps ⟨instMap, instTypeMap⟩ i.getId.toString (modId, default) (isIO modId) modCluster with
            | .ok ⟨a, b⟩ =>
              instMap := a
              instTypeMap := b
            | .error s =>
              throwErrorAt i s
          else
            let some modIdArgs ← findStxNat' `arg el
              | throwErrorAt i "No `arg` attribute found at node"
            match updateNodeMaps ⟨instMap, instTypeMap⟩ i.getId.toString (modId, modIdArgs) (isIO modId) modCluster with
            | .ok ⟨a, b⟩ =>
              instMap := a
              instTypeMap := b
            | .error s =>
              throwErrorAt i s
        | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
          -- Error checking to report it early if the instance is not present in the
          -- hashmap.
          let some el := el
            | throwErrorAt (mkListNode #[a, b]) "No `type` attribute found at node"
          let mut out ← (findStxStr `from el)
          let mut inp ← (findStxStr `to el)
          match updateConnMaps ⟨instMap, instTypeMap⟩ conns a.getId.toString b.getId.toString out inp with
          | .ok (⟨_, b⟩, c) =>
            conns := c
            instTypeMap := b
          | .error (.outInstError s) => throwErrorAt a s
          | .error (.inInstError s) => throwErrorAt b s
          | .error (.portError s) => throwErrorAt (mkListNode el) s
        | _ => pure ()
      let connExpr : Q(List (Connection String)) ←
        mkListLit q(Connection String) (← conns.mapM (λ ⟨ a, b ⟩ => do
          mkAppM ``Connection.mk #[reifyInternalPort a, reifyInternalPort b]))
      let modList : Q(List (String × (PortMapping String × (String × Nat)))) ←
        mkListLit q(String × (PortMapping String × (String × Nat)))
          (instTypeMap.toList.map (fun (a, (p, b)) =>
            let a' : Q(String) := .lit (.strVal a)
            let b' : Q(String) := b.1
            let b'' : Q(Nat) := b.2
            let p' : Q(PortMapping String) := mkPortMapping <| p.map (.strVal · |> .lit)
            q(($a', ($p', ($b', $b''))))))
      let modListMap : Q(IdentMap String (PortMapping String × (String × Nat))) := q(List.toAssocList $modList)
      return q(ExprHigh.mk $modListMap $connExpr)

-- open Qq in
-- instance {α : Q(Type)} : Lean.ToExpr Q($α) where
--   toExpr := id
--   toTypeExpr := α
-- #check Lean.getRef

open Lean Qq in
structure InstMaps' where
  instMap : Std.HashMap String (InstIdent String × Bool)
  instTypeMap : Std.HashMap String (PortMapping String × Q(String))

open Lean Qq in
def updateNodeMaps' (maps : InstMaps') (inst : String) (typ : Q(String)) (cluster : Bool := false) : Except String InstMaps' := do
  let mut instMap := maps.instMap
  let mut instTypeMap := maps.instTypeMap
  let mut modInst : InstIdent String := .top
  unless typ == toExpr "io" do modInst := .internal inst
  let (b, map') := instMap.containsThenInsertIfNew inst (modInst, cluster)
  if !b then
    instMap := map'
    -- IO "modules" are not added to the instTypeMap.
    unless typ == toExpr "io" do instTypeMap := instTypeMap.insert inst (∅, typ)
  else
    throw s!"Multiple references to {inst} found"
  return ⟨instMap, instTypeMap⟩

def updateConnMaps' (maps : InstMaps') (conns : List (Connection String))
    (outInst inInst : String) (outP inP : Option String)
    : Except ConnError (InstMaps' × List (Connection String)) := do
  let mut out := outP
  let mut inp := inP
  let some aInst := maps.instMap[outInst]? | throw (.outInstError "Instance has not been declared")
  let some bInst := maps.instMap[inInst]? | throw (.inInstError "Instance has not been declared")
  if aInst.fst = .top && bInst.fst = .top then
    throw <| .outInstError "Both the input and output are IO ports"
  -- If no port name is provided and the port is a top-level port, then use
  -- the instance name as the port name.
  if out.isNone && aInst.fst.isTop then out := some outInst
  if inp.isNone && bInst.fst.isTop then inp := some inInst
  let some out' := out | throw <| .portError s!"No output found for: {aInst}"
  let some inp' := inp | throw <| .portError s!"No input found for: {bInst}"
  let some outPort := parseInternalPort out'
    | throw <| .portError "Output port format incorrect"
  let some inPort := parseInternalPort inp'
    | throw <| .portError "Input port format incorrect"
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

open Lean Qq in
def checkInputPresent (inInst : Q(TModule1 String)) (inP : Option String)
    : TermElabM Unit := do
  match inP with
  | .some inP =>
    let inputS : Q(Type) := q(($inInst).fst)
    let inputMap : Q(PortMap String (Σ T : Type, ($inputS → T → $inputS → Prop))) := q(($inInst).snd.inputs)
    let expr : Q(Bool) := q(Batteries.AssocList.contains (InternalPort.mk .top $inP) $inputMap)
    unless ← isDefEq expr q(true) do
      throwError "Input not present in Module"
  | .none => return ()

open Lean Qq in
def checkOutputPresent (outInst : Q(TModule1 String)) (outP : Option String)
    : TermElabM Unit := do
  match outP with
  | .some outP =>
    let outputS : Q(Type) := q(($outInst).fst)
    let outputMap : Q(PortMap String (Σ T : Type, ($outputS → T → $outputS → Prop))) := q(($outInst).snd.outputs)
    let expr : Q(Bool) := q(Batteries.AssocList.contains (InternalPort.mk .top $outP) $outputMap)
    unless ← isDefEq expr q(true) do
      throwError "Output not present in Module"
  | .none => return ()

open Lean Qq in
def checkTypeErrors (envMap : Std.HashMap Q(String) Expr) (maps : InstMaps') (conns : List (Connection String))
    (outInst inInst : String) (outP inP : Option String)
    : TermElabM Unit := do
  let `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) ← getRef
    | throwError "Failed to parse reference"
  -- logInfo <| repr <| envMap.toList.map (·.fst)
  let mut outInstExpr : Q(TModule1 String) := default
  let mut inInstExpr : Q(TModule1 String) := default
  if outP.isSome then
    let .some outTypeInfo := maps.instTypeMap[outInst]?
      | throwErrorAt a "Could not find output in type map"
    let .some outInstExpr' := envMap[outTypeInfo.2]?
      | throwErrorAt b "Could not find output in envMap"
    outInstExpr := outInstExpr'
  if inP.isSome then
    let .some inTypeInfo := maps.instTypeMap[inInst]?
      | throwErrorAt b "Could not find output in type map"
    let .some inInstExpr' := envMap[inTypeInfo.2]?
      | throwErrorAt a "Could not find input in envMap"
    inInstExpr := inInstExpr'
  -- The best would be to highlight the actual items in the list instead of the
  -- two sides of the arrow.
  let some el := el | return ()
  withRef (← getListElement `to el) <| checkInputPresent inInstExpr inP
  withRef (← getListElement `from el) <| checkOutputPresent outInstExpr outP

  -- Only check types if we are not assigning an IO port
  let (.some outP, .some inP) := (outP, inP) | return ()

  let outputMap : Q(PortMap String (Σ T : Type, (($outInstExpr).fst → T → ($outInstExpr).fst → Prop))) := q(($outInstExpr).snd.outputs)
  let inputMap : Q(PortMap String (Σ T : Type, (($inInstExpr).fst → T → ($inInstExpr).fst → Prop))) := q(($inInstExpr).snd.inputs)

  let inputType : Q(Type) := q(($inputMap).getIO (InternalPort.mk .top $inP) |>.fst)
  let outputType : Q(Type) := q(($outputMap).getIO (InternalPort.mk .top $outP) |>.fst)

  unless ← isDefEq inputType outputType do
    throwError "Types of input and output port do not match (output ≠ input):\n  {← whnf outputType} ≠ {← whnf inputType}"
  return ()

open Lean Qq in
@[term_elab dot_graphEnv]
def dotGraphElab' : TermElab := λ stx _typ? => do
  let mut instMap : Std.HashMap String (InstIdent String × Bool) := ∅
  let mut instTypeMap : Std.HashMap String (PortMapping String × Q(String)) := ∅
  let mut conns : List (Connection String) := []
  let mut envMap : Std.HashMap Q(String) Expr := ∅
  for stmnt in stx[1][0].getArgs do
    let low_stmnt := stmnt.getArgs[0]!
    match low_stmnt with
    | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
      let some el := el
        | throwErrorAt i "Element list is not present"
      let mut modId : Q(String) := toExpr ""
      match ← findStxTerm `typeImp el with
      | .some modIdImp =>
        modId := toExpr modIdImp.snd
        match ← findStxStr' `type el with
        | .some modId' => modId := modId'
        | .none => pure ()
        envMap := envMap.insert modId modIdImp.fst
      | .none =>
        let some modId' ← findStxStr `type el
          | throwErrorAt i "No `type` attribute found at node"
        modId := toExpr modId'
      let mut modCluster : Bool := findStxBool `cluster el |>.getD false
      match updateNodeMaps' ⟨instMap, instTypeMap⟩ i.getId.toString modId modCluster with
      | .ok ⟨a, b⟩ =>
        instMap := a
        instTypeMap := b
      | .error s =>
        throwErrorAt i s
    | ref@`(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
      -- Error checking to report it early if the instance is not present in the
      -- hashmap.
      let some el := el
        | throwErrorAt (mkListNode #[a, b]) "No `type` attribute found at node"
      let mut out ← (findStxStr `from el)
      let mut inp ← (findStxStr `to el)
      withRef ref <|
        checkTypeErrors envMap ⟨instMap, instTypeMap⟩ conns a.getId.toString b.getId.toString out inp
      match updateConnMaps' ⟨instMap, instTypeMap⟩ conns a.getId.toString b.getId.toString out inp with
      | .ok (⟨_, b⟩, c) =>
        conns := c
        instTypeMap := b
      | .error (.outInstError s) => throwErrorAt a s
      | .error (.inInstError s) => throwErrorAt b s
      | .error (.portError s) => throwErrorAt (mkListNode el) s
    | _ => pure ()
  let connExpr : Q(List (Connection String)) ←
    mkListLit q(Connection String) (← conns.mapM (λ ⟨ a, b ⟩ => do
      mkAppM ``Connection.mk #[reifyInternalPort a, reifyInternalPort b]))
  let modList : Q(List (String × (PortMapping String × String))) ←
    mkListLit q(String × (PortMapping String × String))
      (instTypeMap.toList.map (fun (a, (p, b)) =>
        let a' : Q(String) := .lit (.strVal a)
        let b' : Q(String) := b
        let p' : Q(PortMapping String) := mkPortMapping <| p.map (.strVal · |> .lit)
        q(($a', ($p', $b')))))
  let envList : Q(List (String × TModule1 String)) ←
    mkListLit q(String × TModule1 String)
      (envMap.toList.map (fun (a, m) =>
        let m' : Q(TModule1 String) := m
        let a' : Q(String) := a
        q(($a', $m'))
      ))
  let modListMap : Q(IdentMap String (PortMapping String × String)) := q(List.toAssocList $modList)
  return q(Prod.mk (ExprHigh.mk $modListMap $connExpr) (List.toAssocList $envList))

-- open Lean.PrettyPrinter Delaborator SubExpr

namespace mergemod

-- open StringModule in
-- def mergeHigh (T : Type _) : ExprHigh String × (IdentMap String (TModule1 String)) :=
--   ([graph|
--     src0 [type="io"];
--     snk0 [type="io"];

--     fork1 [type="sten"];

--     fork1 -> snk0 [from=""];
--   ], [("⟨_, fork T 2⟩", ⟨List T, fork T 2⟩)].toAssocList)

-- open StringModule in
-- def mergeHigh2 (T : Type _) : ExprHigh String × (IdentMap String (TModule1 String)) :=
--   [graphEnv|
--     src0 [type="io"];
--     snk0 [type="io"];

--     fork1 [typeImp=$(⟨_, fork T 2⟩), type=$("hllo" ++ "Y")];
--     fork2 [typeImp=$(⟨_, fork T 3⟩)];
--   ]

end mergemod

end Graphiti
