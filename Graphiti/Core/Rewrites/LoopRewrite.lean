/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.ExprHighElaborator

namespace Graphiti.LoopRewrite

open StringModule

def boxLoopBody (g : ExprHigh String) : RewriteResult (List String × List (Connection String)) := do
 let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "init Bool false" do return none

      let (.some mux) := followOutput g inst "out1" | return none
      unless String.isPrefixOf "mux" mux.typ && mux.inputPort = "in1" do return none

      let (.some muxNext) := followOutput g mux.inst "out1" | return none

      let (.some condition_fork) := followInput g inst "in1" | return none
      unless String.isPrefixOf "fork" condition_fork.typ do return none

      let (.some tag_split) := followInput g condition_fork.inst "in1" | return none
      unless String.isPrefixOf "split" tag_split.typ do return none

      let (.some tagPrev) := followInput g tag_split.inst "in1" | return none

      -- as an extra check, the tag_split should be feeding a Branch
      let (.some branch) := followOutput g tag_split.inst "out1" | return none
      unless String.isPrefixOf "branch" branch.typ do return none

      let (.some scc) := findClosedRegion g mux.inst tag_split.inst | return none
      return some (scc.erase mux.inst |>.erase tag_split.inst,
        [ ⟨⟨.internal mux.inst, muxNext.outputPort⟩, ⟨.internal muxNext.inst, muxNext.inputPort⟩⟩
        , ⟨⟨.internal tagPrev.inst, tagPrev.inputPort⟩, ⟨.internal tag_split.inst, tagPrev.outputPort⟩⟩])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def boxLoopBodyOther (g : ExprHigh String) : RewriteResult (List String × List String) := do
 let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "init Bool false" do return none

      let (.some mux) := followOutput g inst "out1" | return none
      unless String.isPrefixOf "mux" mux.typ && mux.inputPort = "in1" do return none

      let (.some condition_fork) := followInput g inst "in1" | return none
      unless String.isPrefixOf "fork" condition_fork.typ do return none

      let (.some tag_split) := followInput g condition_fork.inst "in1" | return none
      unless String.isPrefixOf "split" tag_split.typ do return none

      -- as an extra check, the tag_split should be feeding a Branch
      let (.some branch) := followOutput g tag_split.inst "out1" | return none
      unless String.isPrefixOf "branch" branch.typ do return none

      let (.some first) := followOutput g mux.inst "out1" | return none
      -- let (.some first) := followOutput g first.inst "out1" | return none

      let (.some last') := followInput g tag_split.inst "in1" | return none
      let (.some last) := followInput g last'.inst "in1" | return none

      if last'.inst = first.inst then return none

      return some ([first.inst, last.inst], [])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def boxLoopBodyOther' (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.cons inp _ .nil) := g.modules.filter (λ _ (p, _) => p.input.any (λ a b => b.inst.isTop)) | throw .done
  let (.cons out _ .nil) := g.modules.filter (λ _ (p, _) => p.output.any (λ a b => b.inst.isTop)) | throw .done
  return ([inp, out], [])

def nonPureMatcher : Pattern String := Graphiti.nonPureMatcher <| toPattern boxLoopBody

def nonPureForkMatcher : Pattern String := Graphiti.nonPureForkMatcher <| toPattern boxLoopBody

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless typ = "init Bool false" do return none

       let (.some mux) := followOutput g inst "out1" | return none
       unless String.isPrefixOf "mux" mux.typ do return none

       let (.some mod) := followOutput g mux.inst "out1" | return none
       unless String.isPrefixOf "pure f" mod.typ do return none

       let (.some tag_split) := followOutput g mod.inst "out1" | return none
       unless String.isPrefixOf "split" tag_split.typ do return none

       let (.some condition_fork) := followOutput g tag_split.inst "out2" | return none
       unless String.isPrefixOf "fork" condition_fork.typ do return none

       let (.some branch) := followOutput g tag_split.inst "out1" | return none
       unless String.isPrefixOf "branch" branch.typ do return none

       let (.some queue) := followOutput g branch.inst "out1" | return none
       unless String.isPrefixOf "queue" queue.typ do return none

       return some ([mux.inst, condition_fork.inst, branch.inst, tag_split.inst, mod.inst, inst, queue.inst], [extractType mux.typ])

    ) none | MonadExceptOf.throw RewriteError.done
  return list
-- It can then be tested using the below command
-- #eval (matcher [graph| merge1 [type = "merge"]; merge2 [type = "merge"];
--                merge1 -> merge2 [from = "out1", to = "in1"]; ] /- <--- replace this with the input graph to test with (as an ExprHigh). -/
--        ).run' default

@[drunfold_defs]
def lhs (T : Type) [Inhabited T] (Tₛ : String) (f : T → T × Bool)
      : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [typeImp = $(⟨_, mux T⟩), type = $("mux " ++ Tₛ)];
    condition_fork [typeImp = $(⟨_, fork Bool 2 ⟩), type = "fork Bool 2"];
    branch [typeImp = $(⟨_, branch T⟩), type = $("branch " ++ Tₛ)];
    tag_split [typeImp = $(⟨_, split T Bool⟩), type = $("split " ++ Tₛ ++ " Bool")];
    mod [typeImp = $(⟨_, pure f⟩), type = "pure f"];
    loop_init [typeImp = $(⟨_, init Bool false⟩), type = "init Bool false"];
    queue [typeImp = $(⟨_, queue T⟩), type = $("queue " ++ Tₛ)];
    queue_out [typeImp = $(⟨_, queue T⟩), type = $("queue " ++ Tₛ)];

    i_in -> mux [to="in2"];
    queue_out -> o_out [from="out1"];

    loop_init -> mux [from="out1", to="in1"];
    condition_fork -> loop_init [from="out2", to="in1"];
    condition_fork -> branch [from="out1", to="in2"];
    mod -> tag_split [from="out1", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> condition_fork [from="out2", to="in1"];
    mux -> mod [from="out1", to="in1"];
    branch -> queue [from="out1", to="in1"];
    queue -> mux [from="out1", to="in3"];
    branch -> queue_out [from="out2", to="in1"];
  ]

-- #eval IO.print ((lhs Unit "T" (λ _ => default)).fst)

-- #eval lhs Unit Unit Unit (λ _ _ _ => False) (λ _ _ _ => False) |>.1 |> IO.print

@[drunfold_defs]
def lhs_extract T := lhs Unit T (λ _ => default) |>.1
  |>.extract ["mux", "condition_fork", "branch", "tag_split", "mod", "loop_init", "queue",  "queue_out"]
  |>.get rfl

theorem double_check_empty_snd T: (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

theorem lhs_type_independent a f a₂ f₂ T
        [Inhabited a] [Inhabited a₂]
  : (lhs a T f).fst = (lhs a₂ T f₂).fst := by rfl

@[drunfold_defs]
def lhsLower T := (lhs_extract T).fst.lower_TR.get rfl

abbrev TagT := Nat

@[drunfold_defs]
def liftF {α β γ δ} (f : α -> β × δ) : γ × α -> (γ × β) × δ | (g, a) => ((g, f a |>.fst), f a |>.snd)

@[drunfold_defs]
def rhs (T : Type) [Inhabited T] (Tₛ : String) (f : T → T × Bool)
    : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [typeImp = $(⟨_, tagger_untagger_val TagT T T ⟩), type = $("tagger_untagger_val TagT " ++ Tₛ ++ " " ++ Tₛ)];
    merge [typeImp = $(⟨_, merge (TagT × T) 2⟩), type = $("merge (TagT × " ++ Tₛ ++ ") 2")];
    branch [typeImp = $(⟨_, branch (TagT × T)⟩), type = $("branch (TagT × " ++ Tₛ ++ ")")];
    tag_split [typeImp = $(⟨_, split (TagT × T) Bool⟩), type = $("split (TagT × " ++ Tₛ ++ ") Bool")];
    mod [typeImp = $(⟨_, pure (liftF f)⟩), type = "pure (liftF f)"];

    i_in -> tagger [to="in2"];
    tagger -> o_out [from="out2"];

    tagger -> merge [from="out1",to="in2"];
    merge -> mod [from="out1", to="in1"];
    mod -> tag_split [from="out1", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> branch [from="out2", to="in2"];
    branch -> merge [from="out1", to="in1"];
    branch -> tagger [from="out2", to="in1"];
  ]

@[drunfold_defs]
def rhs_extract T := rhs Unit T (λ _ => default) |>.1
  |>.extract ["tag_split", "tagger", "merge", "branch", "mod"]
  |>.get rfl

@[drunfold_defs]
def rhsLower T := (rhs_extract T |>.1).lower_TR.get rfl

theorem rhs_type_independent b f b₂ f₂ T [Inhabited b] [Inhabited b₂]
  : (rhs b T f).fst = (rhs b₂ T f₂).fst := by rfl

-- #eval IO.print ((rhs Unit "T" (λ _ => default)).fst)

@[drunfold_defs]
def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := unsafe matcher,
    rewrite := λ | [T] => pure ⟨lhsLower T, rhsLower T⟩ | _ => failure
    name := .some "loop-rewrite"
  }

/--
Essentially tagger + join without internal rule
-/
@[drunfold_defs] def NatModule.tagger_untagger_val_ghost (TagT : Type 0) [_i: DecidableEq TagT] (T : Type 0) (name := "tagger_untagger_val_ghost") : NatModule (NatModule.Named name (List (TagT × T) × Batteries.AssocList TagT (T × (Nat × T)) × List (T × (Nat × T)))) :=
  {
    inputs := [
      -- Complete computation
      -- Models the input of the Cal + Untagger (coming from a previously tagged region)
      (0, ⟨ (TagT × T) × (Nat × T), λ (oldOrder, oldMap, oldVal) ((tag,el), r) (newOrder, newMap, newVal) =>
        -- Tag must be used, but no value ready, otherwise block:
        (tag ∈ oldOrder.map Prod.fst ∧ oldMap.find? tag = none) ∧
        newMap = oldMap.cons tag (el, r) ∧ newOrder = oldOrder ∧ newVal = oldVal ⟩),
      -- Enq a value to be tagged
      -- Models the input of the Tagger (coming from outside)
      (1, ⟨ T, λ (oldOrder, oldMap, oldVal) v (newOrder, newMap, newVal) =>
        newMap = oldMap ∧ newOrder = oldOrder ∧ newVal = oldVal.concat (v, 0, v) ⟩)
    ].toAssocList,
    outputs := [
      -- Allocate fresh tag and output with value
      -- Models the output of the Tagger
      (0, ⟨ (TagT × T) × (Nat × T), λ (oldOrder, oldMap, oldVal) ((tag, v), z) (newOrder, newMap, newVal) =>
        -- Tag must be unused otherwise block (alternatively we
        -- could an implication to say undefined behavior):
        (tag ∉ oldOrder.map Prod.fst ∧ oldMap.find? tag = none) ∧
        newMap = oldMap ∧ newOrder = oldOrder.concat (tag, v) ∧ (v, z) :: newVal = oldVal⟩),
      -- Dequeue + free tag
      -- Models the output of the Cal + Untagger
      (1, ⟨ T, λ (oldorder, oldmap, oldVal) el (neworder, newmap, newVal) =>
        -- tag must be used otherwise, but no value brought, undefined behavior:
        ∃ tag r, oldorder = tag :: neworder ∧ oldmap.find? tag.fst = some (el, r) ∧
        newmap = oldmap.eraseAll tag.fst ∧ newVal = oldVal ⟩),
    ].toAssocList,
    init_state := λ s => s = ⟨[], Batteries.AssocList.nil, []⟩,
  }

@[drunfold_defs] def StringModule.tagger_untagger_val_ghost TagT [DecidableEq TagT] T :=
  NatModule.tagger_untagger_val_ghost TagT T |>.stringify

def liftF2 {α β γ δ} (f : α -> β × δ) : α × (Nat × γ) -> (β × (Nat × γ)) × δ
| (a, g) =>
  let b := f a
  ((b.1, (g.1 + 1, g.2)), b.2)

@[drunfold_defs]
def ghost_rhs {Data : Type} (DataS : String) (f : Data → Data × Bool)
    : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [typeImp = $(⟨_, StringModule.tagger_untagger_val_ghost TagT Data ⟩), type = $("tagger_untagger_val_ghost TagT " ++ DataS)];
    merge [typeImp = $(⟨_, merge ((TagT × Data) × (Nat × Data)) 2⟩), type = $("merge ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ") 2")];
    branch [typeImp = $(⟨_, branch ((TagT × Data) × (Nat × Data))⟩), type = $("branch ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ")")];
    tag_split [typeImp = $(⟨_, split ((TagT × Data) × (Nat × Data)) Bool⟩), type = $("split ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ") Bool")];
    mod [typeImp = $(⟨_, pure (liftF2 (liftF f))⟩), type = "pure (liftF2 (liftF f))"];

    i_in -> tagger [to="in2"];
    tagger -> o_out [from="out2"];

    tagger -> merge [from="out1",to="in2"];
    merge -> mod [from="out1", to="in1"];
    mod -> tag_split [from="out1", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> branch [from="out2", to="in2"];
    branch -> merge [from="out1", to="in1"];
    branch -> tagger [from="out2", to="in1"];
  ]

@[drunfold_defs]
def ghost_rhs_extract T := @ghost_rhs Unit T (λ _ => default) |>.1
  |>.extract ["tag_split", "tagger", "merge", "branch", "mod"]
  |>.get rfl

def environmentRhsGhost {Data : Type} (DataS : String) (f : Data → Data × Bool): IdentMap String (TModule1 String) := ghost_rhs DataS f |>.snd

@[drunfold_defs]
def rhsGhostLower (DataS : String):= (@ghost_rhs_extract DataS |>.1).lower_TR.get rfl

theorem rhs_ghost_type_independent b f b₂ f₂ T [Inhabited b] [Inhabited b₂]
  : (@ghost_rhs b T f).fst = (@ghost_rhs b₂ T f₂).fst := by rfl

end Graphiti.LoopRewrite
