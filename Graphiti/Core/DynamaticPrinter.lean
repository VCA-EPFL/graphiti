/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Rewriter
public import Graphiti.Core.TypeExpr
public import Graphiti.Core.DynamaticTypes
public import Graphiti.Core.WellTyped

public section

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

def inferTypeInPortMap (t : TypeUF) (p : PortMap String (InternalPort String)) (sn : String × Nat) : Except String (PortMap String TypeExpr) :=
  p.foldlM (λ st k v => do
      let tc ← toTypeConstraint sn k.name
      let concr ← ofOption' "could not find concr" <| t.findConcr tc
      return st.cons k concr
    ) ∅

def inferTypeInPortMapping (t : TypeUF) (p : PortMapping String) (sn : String × Nat) : Except String (PortMap String TypeExpr × PortMap String TypeExpr) := do
  let inp ← inferTypeInPortMap t p.input sn
  let out ← inferTypeInPortMap t p.output sn
  return (inp, out)

def toPortList (typs : PortMap String TypeExpr) : String :=
  typs.foldl (λ s k v => s ++ s!"{removeLetter 'p' k.name}:{TypeExpr.Parser.getSize v} ") ""

--fmt.1: Type
--fmt.2.1 and fmt.2.2.1: Input and output attributes
--fmt.2.2.2: Additional options.
def dynamaticString (a: ExprHigh String (String × Nat)) (t : TypeUF) (m : AssocList String (AssocList String String)): Except String String := do
  let a ← ofOption' "could not normalise names" a.normaliseNames
  let modules ←
    a.modules.foldlM
      (λ s k v => do
        -- search for the type of the passed node in interfaceTypes
        let typeName ← ofOption' s!"could not convert graphiti to dynamatic name for {k}/{v.2.1}" <| graphitiToDynamatic v.2.1
        match m.find? k with
        | some input_fmt =>
          -- If the node is found to be coming from the input,
          -- retrieve its attributes from what we saved and bypass it
          -- without looking for it in interfaceTypes
          return s ++ s!"\"{k}\" [type = \"{typeName}\"{formatOptions input_fmt.toList}];\n"
        | none =>
          let typs ← inferTypeInPortMapping t v.1 v.2
          -- If this is a new node, then we sue `fmt` to correctly add the right
          -- arguments from what is given in interfaceTypes.  We should never be generating constructs like MC, so
          -- this shouldn't be a problem.
          return s ++ s!"\"{k}\" [type = \"{typeName}\", in = \"{toPortList typs.1}\", out = \"{toPortList typs.2}\"];\n"
      ) ""
  let connections :=
    a.connections.foldl
      (λ s => λ | ⟨ oport, iport ⟩ =>
                    s ++ s!"\n  \"{(oport.inst)}\" -> \"{(iport.inst)}\" "
                    ++ s!"[from = \"{oport.name}\","
                    ++ s!" to = \"{removeLetter 'p' iport.name}\" "
                    ++ "];") ""
  .ok s!"Digraph G \{
{modules}
{connections}
}"

end Graphiti
