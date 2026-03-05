/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Dataflow.Rewrites
public import Graphiti.Core.Graph.ExprHigh

public section

open Std.Internal (Parsec)
open Std.Internal.Parsec String

open Batteries (AssocList)

namespace Graphiti

inductive JSLang where
| join : String → JSLang → JSLang → JSLang
| split1 : String → JSLang → JSLang
| split2 : String → JSLang → JSLang
| pure : String → JSLang → JSLang
| I : JSLang
deriving DecidableEq, Repr, Inhabited

inductive SExpr (Atom : Type _) : Type _ where
| atom : Atom → SExpr Atom
| list : List (SExpr Atom) → SExpr Atom
deriving Repr, Inhabited

def SExpr.toString {Atom} [ToString Atom] : SExpr Atom → String
| .atom a => ToString.toString a
| .list l => s!"({l.map toString |>.intersperse " " |>.foldl (fun st s => st ++ s) ""})"

instance {Atom} [ToString Atom] : ToString (SExpr Atom) := ⟨SExpr.toString⟩

inductive JSAtom where
| str (s : String)
| sym (s : String)
deriving Repr, Inhabited, DecidableEq

def JSAtom.toString : JSAtom → String
| .str s => s!"\"{s}\""
| .sym s => s

instance : ToString JSAtom := ⟨JSAtom.toString⟩

@[simp] abbrev JSSExpr := SExpr JSAtom

def JSLang.toSExpr : JSLang → JSSExpr
| .join s l1 l2 => .list [.atom (.sym "join"), .atom (.str s), toSExpr l1, toSExpr l2]
| .split1 s l => .list [.atom (.sym "split1"), .atom (.str s), toSExpr l]
| .split2 s l => .list [.atom (.sym "split2"), .atom (.str s), toSExpr l]
| .pure s l => .list [.atom (.sym "pure"), .atom (.str s), toSExpr l]
| .I => .atom (.sym "I")

structure JSLang.Info Typ where
  inst : String
  typ : Typ
  inPort : String
  outPort : String

def JSLang.Info.ofNextNode {Typ} (a : NextNode String Typ) : JSLang.Info Typ :=
  ⟨a.inst, a.typ, a.inputPort, a.outputPort⟩

def JSLang.ofNNHashMap {Typ} (a : Std.HashMap String (Array (NextNode String Typ))): Std.HashMap String (Array (JSLang.Info Typ)) :=
  a.map (fun _ v => v.map JSLang.Info.ofNextNode)

class JSType (Typ : Type _) where
  isSplit : Typ → Bool
  isJoin : Typ → Bool
  isPure : Typ → Bool

instance : JSType (String × Nat) where
  isSplit | ("split", _) => true | _ => false
  isJoin  | ("join", _) =>  true | _ => false
  isPure  | ("pure", _) =>  true | _ => false

def JSLang.construct {Typ : Type _} [JSType Typ] (term : Nat)
    (succ : Std.HashMap String (Array (JSLang.Info Typ))) (endN : String) (startN : JSLang.Info Typ) : Option JSLang :=
  if startN.inst = endN then .some .I else
  match term with
  | 0 => .none
  | term'+1 =>
    match succ[startN.inst]?.map (·.toList) with
    | .some [a, b] => do -- join node
      let jsA ← construct term' succ endN a
      let jsB ← construct term' succ endN b
      if a.outPort = "in1" then
        return .join startN.inst jsA jsB
      else
        return .join startN.inst jsB jsA
    | .some [a] => do -- split node
      let js ← construct term' succ endN a
      if JSType.isPure startN.typ then
        return pure startN.inst js
      if JSType.isSplit startN.typ && startN.inPort = "out1" then
        return split1 startN.inst js
      else
        return split2 startN.inst js
    | _ => .none -- error

inductive JSLangRewrite where
| assocL (s : String) (dir : Bool)
| assocR (s : String) (dir : Bool)
| comm (s : String)
| elim (s : String)
deriving Repr

def parseRewrites (s : String) : Except String (List JSLangRewrite) := do
  match ← Lean.Json.parse s with
  | .arr a =>
    a.foldrM (λ jObj l => do
        let rw ← jObj.getObjVal? "rw" >>= (·.getStr?)
        let args ← jObj.getObjVal? "args"
        let arg0 ← args.getArrVal? 0 >>= (·.getStr?)
        let dir ← jObj.getObjVal? "dir" >>= (·.getBool?)
        match rw with
        | "L" =>
          return JSLangRewrite.assocL arg0 dir :: l
        | "R" =>
          return JSLangRewrite.assocR arg0 dir :: l
        | "E" =>
          return JSLangRewrite.elim arg0 :: l
        | "C" =>
          return JSLangRewrite.comm arg0 :: l
        | _ => throw s!"rewrite '{rw}' not recognised"
      ) []
  | j => throw s!"top-level JSON object is not an array: {j}"

def JSLangRewrite.mapToRewrite : JSLangRewrite → Rewrite String (String × Nat)
| .assocL s true
| .assocR s false => JoinAssocL.targetedRewrite s
| .assocR s true
| .assocL s false => JoinAssocR.targetedRewrite s
| .comm s => JoinComm.targetedRewrite s
| .elim s => JoinSplitElim.targetedRewrite s

open IO.Process in
/--
Run process to completion and capture output.
The process does not inherit the standard input of the caller.
-/
def runCommandWithStdin (cmd : String) (args : Array String) (stdin : String) : IO Output := do
  let child ← spawn {
    cmd := cmd,
    args := args,
    stdin := Stdio.piped,
    stdout := Stdio.piped,
    stderr := Stdio.piped
  }

  let (stdinHandle, newChild) ← child.takeStdin
  stdinHandle.putStrLn stdin

  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← newChild.wait
  let stdout ← IO.ofExcept stdout.get
  pure { exitCode := exitCode, stdout := stdout, stderr := stderr }

def rewriteWithEgg {n} (eggCmd := "graphiti_oracle")
    (p : Pattern String (String × Nat) n) (rewrittenExprHigh : ExprHigh String (String × Nat))
    : IO (List JSLangRewrite) := do
  let .some succ := calcSucc rewrittenExprHigh.invert | throw (.userError s!"{decl_name%}: could not calculate succ")
  let .ok ([first, last], _) := p rewrittenExprHigh
    | return [] -- throw (.userError s!"{decl_name%}: first/last not found")
  let .some constructed := JSLang.construct 10000 (JSLang.ofNNHashMap succ) first ⟨last, default, default, default⟩
    | throw (.userError s!"{decl_name%}: could not construct")

  /- IO.eprintln (toSExpr constructed) -/
  let out ← runCommandWithStdin eggCmd #[] (toString constructed.toSExpr)
  IO.ofExcept <| parseRewrites out.stdout

def JSLang.upd1 {Typ} (m : AssocList String (Option String)) : JSLangRewrite → RewriteResult String Typ JSLangRewrite
| .assocL s dir => do
  let (.some s') := (m.find? s).getD s
    | throw <| .error s!"{decl_name%}: assocL: '{s}' deleted in map"
  return .assocL s' dir
| .assocR s dir => do
  let (.some s') := (m.find? s).getD s
    | throw <| .error s!"{decl_name%}: assocR: '{s}' deleted in map"
  return .assocR s' dir
| .comm s => do
  let (.some s') := (m.find? s).getD s
    | throw <| .error s!"{decl_name%}: comm: '{s}' deleted in map"
  return .comm s'
| .elim s => do
  let (.some s') := (m.find? s).getD s
    | throw <| .error s!"{decl_name%}: elim: '{s}' deleted in map"
  return .elim s'

def JSLang.upd {Typ} (m : AssocList String (Option String)) (j : List JSLangRewrite) : RewriteResult String Typ (List JSLangRewrite) :=
  j.mapM (JSLang.upd1 m)

def JSLang.elimPure : JSLang → JSLang
| .pure s l => l
| .join s l1 l2 => .join s (elimPure l1) (elimPure l2)
| .split1 s l => .split1 s (elimPure l)
| .split2 s l => .split2 s (elimPure l)
| .I => .I

end Graphiti
