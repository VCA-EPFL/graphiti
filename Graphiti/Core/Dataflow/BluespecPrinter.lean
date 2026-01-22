/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Dataflow.InferTypes

public section

open Batteries (AssocList)

namespace Graphiti

def escapeQuotes (s : String) : String := s.replace "\"" "\\\"" |>.replace "\n" ""

def ExprHigh.toBlueSpec (a : ExprHigh String (String × Nat)) (t : TypeUF) (m : AssocList String (AssocList String String)): String :=
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
          /- let (typ, args) := TypeExpr.Parser.parseNode (toString v.snd) |>.getD ("unknown", [])
           - let args' := (List.range args.length).zip args |>.map (λ (n, arg) => arg.toBlueSpec n)
           - s ++ s!"  \"{k}\" [type = \"{typ}\", {", ".intercalate args'}, label = \"{k}: {v.snd}\"];\n"
            -/
          let typs := t.inferTypeInPortMapping v.1.canonPortMapping v.2 |>.toOption |>.getD (∅, ∅)

          let object := Lean.Json.mkObj [("inputs", Lean.toJson ((typs.1.mapVal (λ _ x => x.toBlueSpec)).mapKey (λ k => k.name))), ("outputs", Lean.toJson ((typs.2.mapVal (λ _ x => x.toBlueSpec)).mapKey (λ k => k.name)))]
          let m := (m.find? k).getD ∅
          let op := if "op" ∈ m.keysList then s!", op = \"{m.find? "op" |>.get!}\"" else ""
          let val := if "value" ∈ m.keysList then s!", value = \"{m.find? "value" |>.get!}\"" else ""
          s ++ s!"  \"{k}\" [type = \"{v.2.1}\", extra = \"{escapeQuotes (toString (Lean.toJson object))}\"{op}{val}]\n"
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

end Graphiti
