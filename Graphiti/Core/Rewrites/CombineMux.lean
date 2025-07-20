/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.CombineMux

open StringModule

local instance : MonadExcept IO.Error RewriteResult where
  throw e := throw <| .error <| toString e
  tryCatch m h := throw (.error "Cannot catch IO.Error")

-- Return any 2 Muxes fed by the same fork if the fork has the init as a predecessor (directly or through a tree of forks)
-- TODO: Currently, it assumes that the init is either the direct predecessor or is a predecessor of the predecessor. We should make it more general to accommodate any number of forks until the init

def findUpperForkInput (g : ExprHigh String) (nn : NextNode String) : Nat → RewriteResult (NextNode String)
| 0 => MonadExceptOf.throw <| RewriteError.error s!"{decl_name%}: max depth reached"
| n+1 => do
  let (.some nextFork) := followInput g nn.inst "in1" | MonadExceptOf.throw <| RewriteError.error s!"{decl_name%}: could not follow input"
  if "fork".isPrefixOf nextFork.typ then
    findUpperForkInput g nextFork n
  else
    return nextFork

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  -- let .some l ← ofExcept <| unsafe unsafeIO do
  --   -- Create a temporary file which contains the dot graph to match on.
  --   let result ← IO.FS.withTempFile λ handle filePath => do
  --     handle.putStrLn <| toString g
  --     -- Call command with argument `tmpfile`.
  --     let cmd := { cmd := "echo", args := #[filePath.toString] }
  --     let result ← IO.Process.output cmd
  --     -- If exit code of script is 100, then ignore the return string and signal that this rewrite didn't match any
  --     -- pattern anymore.  The top-level runner should move to a new rewrite.
  --     if result.exitCode == 100 then return none
  --     -- If the exit code is non-zero, then throw an error
  --     if result.exitCode != 0 then
  --       throw <| IO.userError <| "process '" ++ cmd.cmd ++ "' exited with code " ++ toString result.exitCode
  --     -- Otherwise return the `stdout` of the command and split up the resulting string based on `, `.
  --     return result.stdout.splitOn ", " |>.map String.trim |> pure
  --   return result
  --   | MonadExceptOf.throw RewriteError.done
  -- -- TODO: The matched things by the script are currently in the `l` variable, but is NOT used in the code below.
  -- let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "fork Bool 2" do return none
      -- let (.some fork_input) := followInput g inst "in1" | return none
      -- let (.some fork_input_input) := followInput g fork_input.inst "in1" | return none
      -- let (.some fork_input_input_input) := followInput g fork_input_input.inst "in1" | return none

      let upperForkInput ← findUpperForkInput g {(default : NextNode String) with inst := inst} 1000
      unless upperForkInput.typ = "init Bool false" do return none

      let (.some mux_nn) := followOutput g inst "out1" | return none
      let (.some mux_nn') := followOutput g inst "out2" | return none

      unless String.isPrefixOf "mux" mux_nn.typ && mux_nn.inputPort = "in1" do return none
      unless String.isPrefixOf "mux" mux_nn'.typ && mux_nn'.inputPort = "in1" do return none
      return some ([mux_nn.inst, mux_nn'.inst, inst], [extractType mux_nn.typ, extractType mux_nn'.typ])
    ) none | MonadExceptOf.throw RewriteError.done
  return list


def lhs (T T' : Type) (Tₛ T'ₛ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    b1_t_i [type = "io"];
    b1_f_i [type = "io"];
    b2_t_i [type = "io"];
    b2_f_i [type = "io"];
    cond_i [type = "io"];
    b1_o [type = "io"];
    b2_o [type = "io"];

    mux1 [typeImp = $(⟨_, mux T⟩), type = $("mux " ++ Tₛ)];
    mux2 [typeImp = $(⟨_, mux T'⟩), type = $("mux " ++ T'ₛ)];
    condFork [typeImp = $(⟨_, fork Bool 2⟩), type = "fork Bool 2"];

    mux1 -> b1_o [from="out1"];
    mux2 -> b2_o [from="out1"];

    cond_i -> condFork [to="in1"];
    b1_t_i -> mux1 [to="in2"];
    b1_f_i -> mux1 [to="in3"];
    b2_t_i -> mux2 [to="in2"];
    b2_f_i -> mux2 [to="in3"];

    condFork -> mux1 [from="out1", to="in1"];
    condFork -> mux2 [from="out2", to="in1"];
  ]

-- #reduce lhs Unit Unit "H" "Y"

def lhs_extract T₁ T₂ := (lhs Unit Unit T₁ T₂).fst.extract ["mux1", "mux2", "condFork"] |>.get rfl

-- #eval IO.print (lhs_extract "T" "T'").fst

theorem lhs_type_independent a b c d T₁ T₂ : (lhs a b T₁ T₂).fst = (lhs c d T₁ T₂).fst := by rfl

theorem double_check_empty_snd T₁ T₂ : (lhs_extract T₁ T₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T₁ T₂ := lhs_extract T₁ T₂ |>.fst.lower.get rfl

def rhs (T T' : Type) (Tₛ Tₛ' : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    b1_t_i [type = "io"];
    b1_f_i [type = "io"];
    b2_t_i [type = "io"];
    b2_f_i [type = "io"];
    cond_i [type = "io"];
    b1_o [type = "io"];
    b2_o [type = "io"];

    joinT [typeImp = $(⟨_, join T T'⟩), type = $("join " ++ Tₛ ++ " " ++ Tₛ')];
    joinF [typeImp = $(⟨_, join T T'⟩), type = $("join " ++ Tₛ ++ " " ++ Tₛ')];
    mux [typeImp = $(⟨_, mux (T×T')⟩), type = $("mux (" ++ Tₛ ++ "×" ++ Tₛ' ++ ")")];
    split [typeImp = $(⟨_, split T T'⟩), type = $("split " ++ Tₛ ++ " " ++ Tₛ')];

    b1_t_i -> joinT [to="in1"];
    b2_t_i -> joinT [to="in2"];
    b1_f_i -> joinF [to="in1"];
    b2_f_i -> joinF [to="in2"];

    cond_i -> mux [to="in1"];

    joinT -> mux [from="out1", to="in2"];
    joinF -> mux [from="out1", to="in3"];
    mux -> split [from="out1", to="in1"];

    split -> b1_o [from="out1"];
    split -> b2_o [from="out2"];
  ]

def rhsLower T₁ T₂ := (rhs Unit Unit T₁ T₂).fst.lower.get rfl

-- #eval IO.print ((rhs Unit Unit "T" "T'").fst)

theorem rhs_type_independent a b c d T₁ T₂ : (rhs a b T₁ T₂).fst = (rhs c d T₁ T₂).fst := by rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ l => do
      let T₁ ← l.get? 0
      let T₂ ← l.get? 1
      return ⟨lhsLower T₁ T₂, rhsLower T₁ T₂⟩
    name := .some "combine-mux"
  }

end Graphiti.CombineMux
