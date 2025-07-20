/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Graphiti.Core.ExprHigh

open Std.Internal (Parsec)
open Std.Internal.Parsec String
open Batteries (AssocList)

namespace Graphiti

inductive TypeExpr where
| nat
| bool
| tag
| unit
| pair (left right : TypeExpr)
deriving Repr, DecidableEq, Inhabited

noncomputable def TypeExpr.denote : TypeExpr → Type
| nat => Nat
| tag => Unit
| bool => Bool
| unit => Unit
| pair t1 t2 => t1.denote × t2.denote

inductive ValExpr where
| nat (n : Nat)
| bool (b : Bool)
| unit
| pair (left right : ValExpr)
deriving Repr, DecidableEq

def ValExpr.type : ValExpr → TypeExpr
| nat _ => .nat
| bool _ => .bool
| unit => .unit
| pair l r => .pair l.type r.type

def ValExpr.denote : (t : ValExpr) → t.type.denote
| nat n => n
| bool b => b
| unit => ()
| pair t1 t2 => (t1.denote, t2.denote)

inductive FuncName where
| getelementptr_op
| zext_op
| fmul_op
| fadd_op
| add_op
| icmp_ult_op
| mc_store_op
| mc_load_op
| ret_op

inductive FuncExpr where
| typ (t : TypeExpr)
| val (v : ValExpr)
| var
| left (f : FuncExpr)
| right (f : FuncExpr)
| app (n : FuncName) (n : FuncExpr)

namespace TypeExpr.Parser

@[inline] def skipStringWs (s : String) := skipString s <* ws

partial def parseTypeExpr' : Parser TypeExpr :=
    ws *> ( skipStringWs "Nat" *> pure .nat
            <|> skipStringWs "TagT" *> pure .unit
            <|> skipStringWs "T" *> pure .nat
            <|> skipStringWs "Bool" *> pure .bool
            <|> skipStringWs "Unit" *> pure .unit
            <|> (do skipStringWs "("
                    let t ← parseTypeExpr'
                    skipStringWs "×"
                    let t' ← parseTypeExpr'
                    skipStringWs ")"
                    return .pair t t'
                ))

def parseTypeExpr (s : String): Option TypeExpr :=
  match parseTypeExpr' |>.run s with
  | .ok r => .some r
  | .error _ => .none

noncomputable def parseType (s : String): Option Type :=
  parseTypeExpr s |>.map TypeExpr.denote

def toString' : TypeExpr → String
  | TypeExpr.nat => "T"
  | TypeExpr.tag => "TagT" -- Unclear how we want to display TagT at the end?
  | TypeExpr.bool => "Bool"
  | TypeExpr.unit => "Unit"
  | TypeExpr.pair left right =>
    let leftStr := toString' left
    let rightStr :=  toString' right
    s!"({leftStr} × {rightStr})"

def getSize: TypeExpr → Int
  | TypeExpr.nat => 32
  | TypeExpr.tag => 0
  | TypeExpr.bool => 1
  | TypeExpr.unit => 0
  | TypeExpr.pair left right =>
    let l := getSize left
    let r :=  getSize right
    l + r

instance : ToString TypeExpr where
  toString := toString'

def parserId : Parser String := do
  let chars ← many1 (satisfy (fun c => !c.isWhitespace))
  return String.mk chars.toList

def parserNode : Parser (String × List TypeExpr) := do
  ws
  let name ← parserId
  let ts ← many1 parseTypeExpr' <* ws
  return (name, ts.toList)


def parseNode (s : String): Option (String × List TypeExpr) :=
  match parserNode |>.run s with
  | .ok r => .some r
  | .error _ => .none

def flatten_type (t : TypeExpr) : List TypeExpr :=
  match t with
  | TypeExpr.nat => [t]
  | TypeExpr.tag => [t]
  | TypeExpr.bool => [t]
  | TypeExpr.unit => [t]
  | TypeExpr.pair left right =>
    flatten_type left ++ flatten_type right

end TypeExpr.Parser
end Graphiti
