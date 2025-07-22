/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Graphiti.Core.ExprHigh

open Std.Internal (Parsec)
open Std.Internal.Parsec String
open Batteries (AssocList)

namespace Graphiti
namespace Parser

structure DotAttr where
  key : String
  value : String
deriving Inhabited, Repr

structure DotGraph where
  nodes : List (String × List DotAttr)
  edges : List (String × String × List DotAttr)
deriving Inhabited, Repr

instance : EmptyCollection DotGraph := ⟨∅, ∅⟩

def hexChar : Parser Nat := do
  let c ← any
  if '0' <= c && c <= '9' then
    pure $ (c.val - '0'.val).toNat
  else if 'a' <= c && c <= 'f' then
    pure $ (c.val - 'a'.val + 10).toNat
  else if 'A' <= c && c <= 'F' then
    pure $ (c.val - 'A'.val + 10).toNat
  else
    fail "invalid hex character"

def escapedChar : Parser Char := do
  let c ← any
  match c with
  | '\\' => return '\\'
  | '"'  => return '"'
  | '/'  => return '/'
  | 'b'  => return '\x08'
  | 'f'  => return '\x0c'
  | 'n'  => return '\n'
  | 'r'  => return '\x0d'
  | 't'  => return '\t'
  | 'u'  =>
    let u1 ← hexChar; let u2 ← hexChar; let u3 ← hexChar; let u4 ← hexChar
    return Char.ofNat $ 4096*u1 + 256*u2 + 16*u3 + u4
  | _ => fail "illegal \\u escape"

partial def strCore (acc : String) : Parser String := do
  let c ← peek!
  if c == '"' then -- "
    skip
    return acc
  else
    let c ← any
    if c == '\\' then
      strCore (acc.push (← escapedChar))
    -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
    -- the JSON standard is not definite: both directly printing the character
    -- and encoding it with multiple \u is allowed. we choose the former.
    else if 0x0020 <= c.val && c.val <= 0x10ffff then
      strCore (acc.push c)
    else
      fail "unexpected character in string"

@[inline]
def lookahead (p : Char → Prop) (desc : String) [DecidablePred p] : Parser Unit := do
  let c ← peek!
  if p c then
    return ()
  else
    fail <| "expected " ++ desc

@[inline] def str : Parser String := do
  lookahead (fun c => c == '"') "\""; skip; -- "
  strCore ""

@[inline] def strWs : Parser String := str <* ws

def strDigits : Parser String := do
  let l ← Lean.Json.Parser.num
  return toString l

def hexParser' : Parser Nat :=
  Lean.Xml.Parser.digitsToNat 16 <$> many1 (hexChar)

def hexParser : Parser Nat :=
  skipString "0x" *> hexParser'

def strDigitsWs : Parser String := strDigits <* ws

@[inline]
def nonNumericIdentifier : Parser Char := attempt do
  let c ← any
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ (c = '_') ∨ ('\u0200' ≤ c ∧ c ≤ '\u0377')
  then return c else fail s!"ASCII letter expected"

def identifier : Parser String := do
  let c ← nonNumericIdentifier
  let cs ← manyChars (nonNumericIdentifier <|> digit)
  return c.toString ++ cs

def identifierWs := identifier <* ws

def parseId := identifierWs <|> strWs <|> strDigitsWs

def skipStringWs (s : String) := skipString s <* ws
def pstringWs (s : String) := pstring s <* ws
def digitsWs := digits <* ws

def around {α} (delimL delimR : String) (p : Parser α) : Parser α := do
  skipStringWs delimL
  let l ← p
  skipStringWs delimR
  return l

def braces {α} : Parser α → Parser α := around "{" "}"
def brackets {α} : Parser α → Parser α := around "[" "]"
def parens {α} : Parser α → Parser α := around "(" ")"

def delimited' {α} (delim : String) (p : Parser α) : Parser (Array α) := do
  let l ← p
  let l' ← many (attempt <| skipStringWs delim *> p)
    <* (skipStringWs delim <|> ws)
  return (#[l] ++ l')

def delimited {α} (delim : String) (p : Parser α) : Parser (Array α) :=
  delimited' delim p <|> pure #[]

def tryP {α} (p : Parser α) : Parser (Option α) :=
  (some <$> p) <|> pure none

def tryD {α} (a : α) (p : Parser α) : Parser α :=
  p <|> pure a

def parseBool : Parser Bool :=
  (skipString "true" *> pure true)
  <|> (skipString "false" *> pure false)

def parseAttr : Parser DotAttr := do
  let i ← parseId
  skipStringWs "="
  let i' ← parseId
  return ⟨i, i'⟩

def parseNode : Parser (String × List DotAttr) := do
  let i ← parseId
  let l ← tryD #[] <| brackets <| delimited "," parseAttr
  return (i, l.toList)

def parseNodeDG : Parser DotGraph := do
  let n ← parseNode
  return {nodes := [n], edges := []}

def parseEdge : Parser (String × String × List DotAttr) := do
  let i ← parseId
  skipStringWs "->"
  let i' ← parseId
  let l ← tryD #[] <| brackets <| delimited "," parseAttr
  return (i, i', l.toList)

def parseEdgeDG : Parser DotGraph := do
  let n ← parseEdge
  return {nodes := [], edges := [n]}

def combine (a b : DotGraph) : DotGraph :=
  {nodes := a.nodes ++ b.nodes, edges := a.edges ++ b.edges}

def parseComment : Parser Unit :=
  optional (skipString "//" *> many (satisfy (λ c => c ≠ '\n' && c ≠ '\r'))) *> ws

mutual

partial def parseStmnt : Parser DotGraph :=
  attempt (parseEdgeDG <* skipChar ';')
  <|> attempt (parseNodeDG <* skipChar ';')
  <|> attempt (parseAttr *> pure {nodes := [], edges := []} <* skipChar ';')
  <|> parseSubgraph

partial def parseDotGraph : Parser DotGraph := do
  let l ← many (optional parseComment *> parseStmnt <* ws)
  return l.foldl combine ∅

partial def parseSubgraph : Parser DotGraph := do
  skipStringWs "subgraph" *> tryD "defaultId" parseId *> braces parseDotGraph <* ws

end

def parseDigraph := skipStringWs "digraph" <|> skipStringWs "Digraph"

def dotGraph : Parser DotGraph := do
  ws *> parseDigraph *> optional parseId *> braces parseDotGraph <* eof

end Parser

def keyStartsWith (l : List Parser.DotAttr) key val :=
  (l.find? (·.key = key) |>.map (·.value) |>.getD "" |>.trim |>.startsWith val)

def splitAndSearch (l : List Parser.DotAttr) (key searchStr : String) : Bool :=
  match l.find? (λ x => x.key = key) with
  | some x =>
    -- Split the value of the key found and search for a prefix match
    (x.value.trim.splitOn).find? (λ part => part.startsWith searchStr) |>.isSome
  | none => false

def keyArg (l : List Parser.DotAttr) key :=
  l.find? (·.key = key) |>.map (·.value) |>.getD "" |>.trim

def keyArgNumbers (l : List Parser.DotAttr) key :=
  keyArg l key |>.splitOn |>.length

def parseIOSizes (l : List Parser.DotAttr) (key : String) : List String :=
  keyArg l key |>.splitOn |>.flatMap (λ x => x.splitOn ":" |>.drop 1)

def addArgs (s : String) (l : List Parser.DotAttr) (current_extra_args : AssocList String String) (k : String) : Except String (AssocList String String) := do
  let some el := l.find? (·.key = k)
    | throw s!"{s}: could not find \"{k}\" field in Operation"
  return current_extra_args.cons el.key el.value.trim

def addOptArgs (s : String) (l : List Parser.DotAttr) (current_extra_args : AssocList String String) (k : String) : Except String (AssocList String String) := do
  match l.find? (·.key = k) with
  | some el => return current_extra_args.cons el.key el.value.trim
  | _ => return current_extra_args

def translateSize' : String → Except String String
| "0" => .ok "Unit"
| "1" => .ok "Bool"
| "32" => .ok "T"
| s => .error s!"Could not parse size: {s}"

def translateSize (s : String) : Except String String :=
  translateSize' (s.takeWhile (·.isDigit))

/--
Parse a dot expression that comes from Dynamatic.  It returns the graph
expression, as well as a list of additional attributes that should be bypassed
to the dynamatic printer.
-/
def dotToExprHigh (d : Parser.DotGraph) : Except String (ExprHigh String × AssocList String (AssocList String String)) := do
  let (maps, assoc) ← d.nodes.foldlM (λ (a, assoc) (s, l) => do
      let add := addArgs s l
      let addOpt := addOptArgs s l

      let mut current_extra_args : AssocList String String := ∅

      current_extra_args ← addOpt current_extra_args "bbID"

      let some typ := l.find? (·.key = "type")
        | throw s!"{s}: could not find instance type"

      current_extra_args ← addOpt current_extra_args "in"
      current_extra_args ← addOpt current_extra_args "out"

      let mut typVal := typ.value.trim

      if typVal != "MC" && typVal != "Sink" && typVal != "Exit" then
        current_extra_args ← addOpt current_extra_args "tagged"
        current_extra_args ← addOpt current_extra_args "taggers_num"
        current_extra_args ← addOpt current_extra_args "tagger_id"

      -- Different bitwidths matter so we distinguish them with types: Unit vs. Bool vs. T
      if typVal = "Branch" then
        if keyStartsWith l "in" "in1:0" then
          typVal := "branch Unit"
        else if keyStartsWith l "in" "in1:1" then
          typVal := "branch Bool"
        -- Else, if the bitwidth is 32, then:
        else typVal := "branch T"

      -- Different bitwidths matter so we distinguish them with types: Unit vs. Bool vs. T
      if typVal = "Fork" then
        let [sizesIn] ← parseIOSizes l "in" |>.mapM translateSize
          | throw "more that one input in fork"
        typVal := s!"fork {sizesIn} {keyArgNumbers l "out"}"

      if typVal = "Mux" then
        current_extra_args ← addOpt current_extra_args "delay"
        if splitAndSearch l "in" "in2:0" then
          typVal := s!"mux Unit"
        else typVal := s!"mux T"

      if typVal = "Merge" then
        current_extra_args ← addOpt current_extra_args "delay"
        if splitAndSearch l "in" "in0:0" then
          typVal := s!"merge Unit {keyArgNumbers l "in"}"
        else typVal := s!"merge T {keyArgNumbers l "in"}"

      if typVal = "Entry" then
        current_extra_args ← addOpt current_extra_args "control"


      if typVal = "Constant" then
        let constVal ← keyArg l "value" |> Parser.hexParser.run
        typVal := s!"constant {constVal}"
        current_extra_args ← addOpt current_extra_args "value"

      if typVal = "Sink" then
        if splitAndSearch l "in" "in1:0" then
          typVal := s!"sink Unit 1"
        else if splitAndSearch l "in" "in1:1" then
          typVal := s!"sink Bool 1"
        else
          typVal := s!"sink T 1"

      if typVal = "Operator" then
        if splitAndSearch l "op" "mc_store_op" || splitAndSearch l "op" "mc_load_op" then
          current_extra_args ← addOpt current_extra_args "portId"
          current_extra_args ← addOpt current_extra_args "offset"

        current_extra_args ← addOpt current_extra_args "delay"
        current_extra_args ← addOpt current_extra_args "latency"
        current_extra_args ← addOpt current_extra_args "II"
        current_extra_args ← addOpt current_extra_args "constants"
        current_extra_args ← add current_extra_args "op"

        if splitAndSearch l "op" "mc_load_op" then
          typVal := s!"load T T"
        else if splitAndSearch l "op" "cast" then
          typVal := s!"pure T Bool"
        else
          let sizesIn ← parseIOSizes l "in" |>.mapM translateSize
          let sizesOut ← parseIOSizes l "out" |>.mapM translateSize
          typVal := s!"operator{keyArgNumbers l "in"} {" ".intercalate sizesIn} {" ".intercalate sizesOut} {keyArg l "op"}"

       -- portId= 0, offset= 0  -- if mc_store_op and mc_load_op

      if typVal = "MC" then
        let sizesIn ← parseIOSizes l "in" |>.mapM translateSize
        let sizesOut ← parseIOSizes l "out" |>.filter (·.trim.endsWith "*e" |> not) |>.mapM translateSize
        typVal := s!"operator{keyArgNumbers l "in"} {" ".intercalate sizesIn} {" ".intercalate sizesOut} MC"
        current_extra_args ← addOpt current_extra_args "memory"
        current_extra_args ← addOpt current_extra_args "bbcount"
        current_extra_args ← addOpt current_extra_args "ldcount"
        current_extra_args ← addOpt current_extra_args "stcount"

      let cluster := l.find? (·.key = "cluster") |>.getD ⟨"cluster", "false"⟩
      let .ok clusterB := Parser.parseBool.run cluster.value.trim
        | throw s!"{s}: cluster could not be parsed"
      let upd ← updateNodeMaps a s typVal clusterB
      return (upd, assoc.cons s current_extra_args)
    ) (InstMaps.mk ∅ ∅, ∅)

  let (maps', conns) ← d.edges.foldlM (λ a (s1, s2, l) => do
      let inp := l.find? (·.key = "to")
      let out := l.find? (·.key = "from")
      match updateConnMaps a.fst a.snd s1 s2 (out.map (·.value.trim)) (inp.map (·.value.trim)) with
      | .ok v => return v
      | .error s => throw s.toString
    ) (maps, [])

  return (⟨ maps'.instTypeMap.toList.toAssocList, conns ⟩, assoc)

end Graphiti

open Graphiti in
def String.toExprHigh (s : String) : Except String (ExprHigh String × AssocList String (AssocList String String) × AssocList String String) := do
  let l ← Parser.dotGraph.run s
  let (e, attr) ← dotToExprHigh l
  let hashed_names_e := {e with modules := e.modules.mapKey' λ x y => y.1.hashPortMapping}
  let name_mapping := ((hashed_names_e.modules.toList.map Prod.fst).zip (e.modules.toList.map Prod.fst)).toAssocList
  return (hashed_names_e, attr, name_mapping)
