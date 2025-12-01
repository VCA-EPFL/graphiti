/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean
public import Batteries.Data.AssocList

@[expose] public section

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
deriving Repr, DecidableEq, Inhabited, Hashable

namespace TypeExpr

def toBlueSpec : TypeExpr → String
| .nat => "Bit#(32)"
| .tag => "Token"
| .bool => "Bool"
| .unit => "Void"
| .pair left right =>
  s!"Tuple2#({toBlueSpec left}, {toBlueSpec right})"

end TypeExpr

inductive ValExpr where
| nat (n : Nat)
| bool (b : Bool)
| unit
| pair (left right : ValExpr)
deriving Repr, DecidableEq

namespace ValExpr

def toBlueSpec : ValExpr → String
| .nat n => s!"{n}"
| .bool b => s!"{b}"
| .unit => "?"
| .pair left right =>
  s!"tuple2({left.toBlueSpec}, {right.toBlueSpec})"

end ValExpr

inductive Argument where
| type_arg (t : TypeExpr)
| val_arg (t : ValExpr)
deriving Inhabited, Repr, DecidableEq

namespace Argument

def toBlueSpec (n : Nat) : Argument → String
| .type_arg t => s!"targ{n} = \"{t.toBlueSpec}\""
| .val_arg t => s!"varg{n} = \"{t.toBlueSpec}\""

def getType! : Argument → TypeExpr
| .type_arg t => t
| _ => panic "Error: could not get type"

end Argument

noncomputable def TypeExpr.denote : TypeExpr → Type
| nat => Nat
| tag => Unit
| bool => Bool
| unit => Unit
| pair t1 t2 => t1.denote × t2.denote

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

partial def parseTypeExpr' : Nat → Parser TypeExpr
| 0 => failure
| n+1 =>
  ws *> ( skipStringWs "Nat" *> pure .nat
          <|> skipStringWs "TagT" *> pure .unit
          <|> skipStringWs "T" *> pure .nat
          <|> skipStringWs "Bool" *> pure .bool
          <|> skipStringWs "Unit" *> pure .unit
          <|> (do skipStringWs "("
                  let t ← parseTypeExpr' n
                  skipStringWs "×"
                  let t' ← parseTypeExpr' n
                  skipStringWs ")"
                  return .pair t t'
              ))

def parseValExpr' : Nat → Parser ValExpr
| 0 => failure
| n+1 =>
  ws *> ( ValExpr.nat <$> (Lean.Json.Parser.nat <* ws)
          <|> skipStringWs "true" *> pure (.bool true)
          <|> skipStringWs "false" *> pure (.bool false)
          <|> skipStringWs "unit" *> pure .unit
          <|> (do skipStringWs "("
                  let t ← parseValExpr' n
                  skipStringWs ","
                  let t' ← parseValExpr' n
                  skipStringWs ")"
                  return .pair t t'
              ))

def parseTypeExpr (s : String): Option TypeExpr :=
  match parseTypeExpr' s.length |>.run s with
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

def parseArgument (fuel : Nat) : Parser Argument :=
  .type_arg <$> parseTypeExpr' fuel
  <|> .val_arg <$> parseValExpr' fuel

def parserNode (fuel : Nat) : Parser (String × List Argument) := do
  ws
  let name ← parserId
  let ts ← many1 (parseArgument fuel) <* ws
  return (name, ts.toList)

def parseNode (s : String): Option (String × List Argument) :=
  match parserNode s.length |>.run s with
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
