/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.TypeExpr

open Batteries (AssocList)

namespace Graphiti

/--
- This should ideally be linked and generated from the environment definition in
the Component.lean file.

- More precisely, it should define all possible nodes that can be added by any of our rewrites.

- It puts default values for some node attributes, which will then be rewritten by inferring
 the correct values by studying the connections in Dot.
-/

def extra_manual :=
  [
   ("Entry start", (some "Entry start", "in1:0", "out1:0", [("control", "true"), ("bbID", "1"), ("tagged", "false"), ("taggers_num", "0"), ("tagger_id", "-1")]))
  ,("Entry", (some "Entry", "in1:0", "out1:0", [("control", "true"), ("bbID", "1"), ("tagged", "false"), ("taggers_num", "0"), ("tagger_id", "-1")]))
  ,("queue T", (some "Queue", "in1:0", "out1:0", [("control", "true"), ("bbID", "-1"), ("tagged", "false"), ("taggers_num", "0"), ("tagger_id", "-1")]))
  ,("Source", (some "Source", "", "out1:0", [("bbID", "1"), ("tagged", "false"), ("taggers_num", "0"), ("tagger_id", "-1")]))
  ,("init Bool false", (some "init Bool false", "in1:32", "out1:32", [("delay", "0.366"), ("bbID", "-1"), ("tagged", "false"), ("taggers_num", "0"), ("tagger_id", "-1")]))
  ,("fork Bool 2", (some "fork Bool 2", "in1:32", "out1:32 out2:32", [("bbID", "-1"), ("tagged", "false"), ("taggers_num", "0"), ("tagger_id", "-1")]))
  ].toAssocList

def translateTypes  (key : String) : Option String × String × String × List (String × String) :=
   match TypeExpr.Parser.parseNode key with
   | some (name, typeParams) =>
     let l := (if name == "mux" || name == "merge" then [("delay", "0.366")] else []) ++ [ ("bbID", "-1"), ("tagged", "false"), ("taggers_num", "0"), ("tagger_id", "-1")]
     match name with
     | "join" =>
      if typeParams.length < 2 then
      -- Defensive programming, embed the problematic string in the unsupported key
        (some key, "", "", [("unsupported", s!"true #{key}")])
      else
        let s1 := TypeExpr.Parser.getSize typeParams[0]!.getType!
        let s2 := TypeExpr.Parser.getSize typeParams[1]!.getType!
        (some key, s!"in1:{s1} in2:{s2}", s!"out1:{s1+s2}", l)
     | "mux" =>
      if typeParams.length < 1 then
        (some key, "", "", [("unsupported", s!"true #{key}")])
      else
        let s1 := TypeExpr.Parser.getSize typeParams[0]!.getType!
        (some key, s!"in1?:1 in2:{s1} in3:{s1}", s!"out1:{s1}", l)
     | "split" =>
      if typeParams.length < 2 then
        (some key, "", "", [("unsupported", s!"true #{key}")])
      else
        let s1 := TypeExpr.Parser.getSize typeParams[0]!.getType!
        let s2 := TypeExpr.Parser.getSize typeParams[1]!.getType!
        (some key, s!"in1:{s1+s2}", s!"out1:{s1} out2:{s2}", l)
     | "branch" =>
      if typeParams.length < 1 then
        (some key, "", "", [("unsupported", s!"true #{key}")])
      else
        let s1 := TypeExpr.Parser.getSize typeParams[0]!.getType!
        (some key, s!"in1:{s1} in2?:{1}", s!"out1+:{s1} out2-:{s1}", l)

     -- TODO: Following four cases need to be checked carefully
     | "sink" =>
      if typeParams.length < 1 then
        (some key, "", "", [("unsupported", s!"true #{key}")])
      else
        let s1 := TypeExpr.Parser.getSize typeParams[0]!.getType!
        (some key, s!"in1:{s1}", s!"", l)
     | "fork" =>
      if typeParams.length < 1 then
        (some key, "", "", [("unsupported", s!"true #{key}")])
      else
        let s1 := TypeExpr.Parser.getSize typeParams[0]!.getType!
        (some key, s!"in1:{s1}", s!"out1:{s1} out2:{s1}", l)
     | "merge" =>
      if typeParams.length < 1 then
        (some key, "", "", [("unsupported", s!"true #{key}")])
      else
        let s1 := TypeExpr.Parser.getSize typeParams[0]!.getType!
        (some key, s!"in1:{s1} in2:{s1}", s!"out1:{s1}", l)
     | "tagger_untagger_val" =>
      if typeParams.length < 3 then
        (some key, "", "", [("unsupported", s!"true #{key}")])
      else
        let sTag := TypeExpr.Parser.getSize typeParams[0]!.getType!
        let s1 := TypeExpr.Parser.getSize typeParams[1]!.getType!
        let s2 := TypeExpr.Parser.getSize typeParams[2]!.getType!
        (some key, s!"in1:{s1} in2:{s1}", s!"out1:{s2} out2:{s2}", l)

     | _ =>
      -- Parsed correctly like queue T
      extra_manual.find? key |>.getD (some key, "", "", [("unsupported", s!"true #{key}")])
   | _ =>
      -- Weird extra stuff in the constant map above
      extra_manual.find? key |>.getD (some key, "", "", [("unsupported", s!"true #{key}")])


def removeLetter (ch : Char) (s : String) : String :=
  String.mk (s.toList.filter (λ c => c ≠ ch))

def returnNatInstring (s : String) : Option Nat :=
  -- Convert the string to a list of characters
  let chars := s.toList
  let result := List.foldl (λ acc c =>
      if c.isDigit then
        acc * 10 + (Char.toNat c - Char.toNat '0')
      else
        acc) 0 chars
  -- If no non-digit character was encountered, return the result
  -- if result = 0 then
  --   if s.isEmpty then some 0 else none
  -- else
  some result

def incrementDefinitionPortIdx (s direction: String) : String :=
  -- Split the string by spaces into individual parts (like "out0:32")
  let parts := s.splitOn " "
  -- Map over each part, incrementing the number after "out"
  let updatedParts := parts.map (λ part =>
    match part.splitOn ":" with
    | [pref, num] =>
      match (returnNatInstring pref) with
      | some n =>
        -- Increment the number found
        let incremented := n + 1
        -- Reconstruct the string with the incremented number
        direction ++ Nat.repr incremented ++ ":" ++ (num)
      | none => part -- If no number is found, keep the part unchanged
    | _ => part -- If the part doesn't have ":" or a valid number, keep it unchanged
  )
  -- Join the updated parts into a single string with spaces
  String.intercalate " " updatedParts

-- #eval incrementDefinitionPortIdx "out1:32" "out"  --out1:324 out2:32 out3:32" "out"  -- Output: "out1:32 out4:32 out3:32"

-- #eval "out132".splitOn ":"

def incrementConnectionPortIdx (s direction: String) : String :=
   match returnNatInstring s with
  | some n =>
    let incremented := n + 1
    -- Convert incremented number to a string and concatenate with the direction part
    let incrementedStr := Nat.repr incremented
    direction ++ incrementedStr
  | none => s  -- If no number is found, return the original string

-- #eval incrementConnectionPortIdx "out33" "out"

-- Function became messy...
def formatOptions : List (String × String) → String
| x :: l => l.foldl
    (λ s (sl, sr) =>
      let v1 := if sl = "in" then removeLetter 'p' sr else sr
      let v1_ := if sl = "bbID" || sl = "bbcount" || sl = "ldcount" || sl = "stcount" || sl = "II" || sl = "latency" || sl = "delay" || sl = "tagger_id" || sl = "taggers_num" || sl = "tagged" || sl = "offset" || sl = "portId"  then s!"{v1}" else s!"\"{v1}\""
      s ++ s!", {sl} = {v1_}")
    (let v2 := if x.1 = "in" then (removeLetter 'p' x.2) else x.2
     let v2_ := if x.1= "bbID" ||  x.1 = "bbcount" ||  x.1 = "ldcount" ||  x.1 = "stcount" || x.1 = "II" || x.1 = "latency" || x.1 = "delay" || x.1 = "tagger_id" || x.1 = "taggers_num" || x.1 = "tagged" || x.1 = "offset" || x.1 = "portId" then s!"{v2}" else s!"\"{v2}\""
     s!", {x.1} = {v2_}")
| [] => ""

def extractStandardType (s : String) : String :=
  let parts := s.splitOn " "
  parts.get! 0

def capitalizeFirstChar (s : String) : String :=
  match s.get? 0 with
  | none   => s  -- If the string is empty, return it as is
  | some c =>
    let newChar := if 'a' ≤ c ∧ c ≤ 'z' then
                     Char.ofNat (c.toNat - ('a'.toNat - 'A'.toNat))
                   else
                     c
    newChar.toString ++ s.drop 1

-- Join is taken in Dynamatic so rename to Concat
def RenameJoinToConcat (s : String) : String :=
  if String.isPrefixOf "join" s then
    "Concat"
  else
    s  -- Otherwise, return the original string

def fixComponentNames (s : String) : String :=
  String.intercalate "_" (s.splitOn "__")

--fmt.1: Type
--fmt.2.1 and fmt.2.2.1: Input and output attributes
--fmt.2.2.2: Additional options.
def dynamaticString (a: ExprHigh String String) (m : AssocList String (AssocList String String)): Option String := do
  -- let instances :=
  --   a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
  let a ← a.normaliseNames
  let modules ←
    a.modules.foldlM
      (λ s k v => do
        -- search for the type of the passed node in interfaceTypes
        let fmt := translateTypes v.snd
        match m.find? k with
        | some input_fmt =>
          -- If the node is found to be coming from the input,
          -- retrieve its attributes from what we saved and bypass it
          -- without looking for it in interfaceTypes
        return (RenameJoinToConcat s) ++ s!"\"{k}\" [type = \"{capitalizeFirstChar (extractStandardType (fmt.1.getD v.snd))}\"{formatOptions input_fmt.toList}];\n"
        --return s ++ s!"\"{k}\" [type = \"{fmt.1.getD v.snd}\"{formatOptions input_fmt.toList}];\n"
        | none =>
          -- If this is a new node, then we sue `fmt` to correctly add the right
          -- arguments from what is given in interfaceTypes.  We should never be generating constructs like MC, so
          -- this shouldn't be a problem.
        return (RenameJoinToConcat s) ++ s!"\"{k}\" [type = \"{capitalizeFirstChar (extractStandardType (fmt.1.getD v.snd))}\", in = \"{removeLetter 'p' fmt.2.1}\", out = \"{fmt.2.2.1}\"{formatOptions fmt.2.2.2}];\n"
        --return s ++ s!"\"{k}\" [type = \"{fmt.1.getD v.snd}\", in = \"{removeLetter 'p' fmt.2.1}\", out = \" {fmt.2.2.1} \"{formatOptions fmt.2.2.2}];\n"

      ) ""
  let connections :=
    a.connections.foldl
      (λ s => λ | ⟨ oport, iport ⟩ =>
                    s ++ s!"\n  \"{(oport.inst)}\" -> \"{(iport.inst)}\" "
                    ++ s!"[from = \"{oport.name}\","
                    ++ s!" to = \"{removeLetter 'p' iport.name}\" "
                    ++ "];") ""
  s!"Digraph G \{
{modules}
{connections}
}"

end Graphiti
