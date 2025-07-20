/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Qq

import Graphiti.Core.ExprHighElaborator

namespace Graphiti

open Lean Meta PrettyPrinter Delaborator SubExpr in
def unexpandStrProdList : Syntax → UnexpandM (TSyntax `Graphiti.dot_stmnt_list)
| `([$[($as:str, $bs:str)],*]) =>
  `(dot_stmnt_list| $[ $(as.map (mkIdent <| ·.getString.toName)):ident [mod=$bs:str] ; ]* )
| _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
def unexpandStrInpList : Syntax → UnexpandM (TSyntax `Graphiti.dot_stmnt_list)
| `([$[($as:str, { inst := $bs:str, name := $cs:str })],*]) =>
  let as' := as.map (mkIdent <| ·.getString.toName)
  let bs' := bs.map (mkIdent <| ·.getString.toName)
  `(dot_stmnt_list| $[ $as':ident -> $bs':ident [inp=$cs:str] ; ]* )
| _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
def unexpandStrOutList : Syntax → UnexpandM (TSyntax `Graphiti.dot_stmnt_list)
| `([$[($as:str, { inst := $bs:str, name := $cs:str })],*]) =>
  let as' := as.map (mkIdent <| ·.getString.toName)
  let bs' := bs.map (mkIdent <| ·.getString.toName)
  `(dot_stmnt_list| $[ $bs':ident -> $as':ident [out = $cs:str] ; ]* )
| _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
def unexpandStrConnsList : Syntax → UnexpandM (TSyntax `Graphiti.dot_stmnt_list)
| `([$[{ output := { inst := $as:str, name := $bs:str }
         , input := { inst := $cs:str, name := $ds:str }}],*]) =>
  let as' := as.map (mkIdent <| ·.getString.toName)
  let cs' := cs.map (mkIdent <| ·.getString.toName)
  `(dot_stmnt_list| $[ $as':ident -> $cs':ident [out = $bs:str, inp = $ds:str] ; ]* )
| _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
def runUnexpander {α} (f : Syntax → UnexpandM α) (s : Syntax) : DelabM α := do
  match f s |>.run (← getRef) |>.run () with
  | EStateM.Result.ok stx _ => return stx
  | _ => failure

open Lean Meta PrettyPrinter Delaborator SubExpr in
def combineDotStmntList (a b : TSyntax `Graphiti.dot_stmnt_list) : DelabM (TSyntax `Graphiti.dot_stmnt_list) :=
  match a, b with
  | `(dot_stmnt_list| $[$a ;]*), `(dot_stmnt_list| $[$b ;]*) =>
    `(dot_stmnt_list| $[$a ;]* $[$b ;]*)
  | _, _ => failure

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.Graphiti.ExprHigh.mk]
def delabExprHigh : Delab := do
  let modList ← withNaryArg 0 <| withNaryArg 2 do
    runUnexpander unexpandStrProdList (← delab)
  let inPorts ← withNaryArg 1 <| withNaryArg 2 do
    runUnexpander unexpandStrInpList (← delab)
  let outPorts ← withNaryArg 2 <| withNaryArg 2 do
    runUnexpander unexpandStrOutList (← delab)
  let conns ← withNaryArg 3 do
    runUnexpander unexpandStrConnsList (← delab)
  let combined ← #[inPorts, outPorts, conns].foldlM combineDotStmntList modList
  `([graph| $combined ])

end Graphiti
