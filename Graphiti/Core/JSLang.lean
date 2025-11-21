/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.ExprHigh
import Graphiti.Core.Rewrites

open Std.Internal (Parsec)
open Std.Internal.Parsec String

open Batteries (AssocList)

namespace Graphiti

inductive JSLang where
| join : String → JSLang → JSLang → JSLang
| split1 : String → JSLang → JSLang
| split2 : String → JSLang → JSLang
| pure : String -> JSLang -> JSLang
| I : JSLang
deriving DecidableEq, Repr

def toSExpr : JSLang → String
| .join s l1 l2 =>
  s!"(join \"{s}\" {toSExpr l1} {toSExpr l2})"
| .split1 s l =>
  s!"(split1 \"{s}\" {toSExpr l})"
| .split2 s l =>
  s!"(split2 \"{s}\" {toSExpr l})"
| .pure s l =>
  s!"(pure \"{s}\" {toSExpr l})"
| .I => "I"

structure JSLang.Info where
  inst : String
  typ : String × Nat
  inPort : String
  outPort : String

instance : Coe (NextNode String (String × Nat)) (JSLang.Info) where
  coe a := ⟨a.inst, a.typ, a.inputPort, a.outputPort⟩

instance : Coe (Std.HashMap String (Array (NextNode String (String × Nat)))) (Std.HashMap String (Array JSLang.Info)) where
  coe a := a.map (fun _ v => v.map Coe.coe)

def JSLang.construct (term : Nat) (succ : Std.HashMap String (Array JSLang.Info)) (endN : String) (startN : JSLang.Info) : Option JSLang :=
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
      if "pure" == startN.typ.1 then
        return pure startN.inst js
      if "split" == startN.typ.1 && startN.inPort = "out1" then
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

def rewriteWithEgg {n} (eggCmd := "graphiti_oracle") (p : Pattern String (String × Nat) n) (rewrittenExprHigh : ExprHigh String (String × Nat))
    : IO (List JSLangRewrite) := do
  let .some succ := calcSucc rewrittenExprHigh.invert | throw (.userError s!"{decl_name%}: could not calculate succ")
  let .ok ([first, last], _) := p rewrittenExprHigh
    | return [] -- throw (.userError s!"{decl_name%}: first/last not found")
  let .some constructed := JSLang.construct 10000 succ first (⟨last, default, default, default⟩)
    | throw (.userError s!"{decl_name%}: could not construct")

  IO.eprintln (toSExpr constructed)
  let out ← runCommandWithStdin eggCmd #[] (toSExpr constructed)
  IO.ofExcept <| parseRewrites out.stdout

def JSLang.upd1 (m : AssocList String (Option String)) : JSLangRewrite → RewriteResult JSLangRewrite
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

def JSLang.upd (m : AssocList String (Option String)) (j : List JSLangRewrite) : RewriteResult (List JSLangRewrite) :=
  j.mapM (JSLang.upd1 m)

end Graphiti
