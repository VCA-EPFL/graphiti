/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.Dataflow.Component

namespace Graphiti.LoopRewrite

open StringModule

def boxLoopBody (initNode : Option String) (g : ExprHigh String (String × Nat)) : RewriteResultSL (List String × List (Connection String)) := do
 let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless (match initNode with | .some initNode' => inst == initNode' | .none => typ.1 == "initBool") do return none

      let (.some mux) := followOutput g inst "out1" | return none
      unless "mux" == mux.typ.1 && mux.inputPort = "in1" do return none

      let (.some muxNext) := followOutput g mux.inst "out1" | return none

      let (.some condition_fork) := followInput g inst "in1" | return none
      unless "fork2" == condition_fork.typ.1 do return none

      let (.some tag_split) := followInput g condition_fork.inst "in1" | return none
      unless "split" == tag_split.typ.1 do return none

      let (.some tagPrev) := followInput g tag_split.inst "in1" | return none

      -- as an extra check, the tag_split should be feeding a Branch
      let (.some branch) := followOutput g tag_split.inst "out1" | return none
      unless "branch" == branch.typ.1 do return none

      let (.some scc) := findClosedRegion g mux.inst tag_split.inst | return none
      return some (scc.erase mux.inst |>.erase tag_split.inst,
        [ ⟨⟨.internal mux.inst, muxNext.outputPort⟩, ⟨.internal muxNext.inst, muxNext.inputPort⟩⟩
        , ⟨⟨.internal tagPrev.inst, tagPrev.inputPort⟩, ⟨.internal tag_split.inst, tagPrev.outputPort⟩⟩])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def boxLoopBodyOther (initNode : Option String) : Pattern String (String × Nat) 0 := fun g => do
 let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless (match initNode with | .some initNode' => inst == initNode' | .none => typ.1 == "initBool") do return none

      let (.some mux) := followOutput g inst "out1" | return none
      unless "mux" == mux.typ.1 && mux.inputPort = "in1" do return none

      let (.some condition_fork) := followInput g inst "in1" | return none
      unless "fork2" == condition_fork.typ.1 do return none

      let (.some tag_split) := followInput g condition_fork.inst "in1" | return none
      unless "split" == tag_split.typ.1 do return none

      -- as an extra check, the tag_split should be feeding a Branch
      let (.some branch) := followOutput g tag_split.inst "out1" | return none
      unless "branch" == branch.typ.1 do return none

      let (.some first) := followOutput g mux.inst "out1" | return none
      -- let (.some first) := followOutput g first.inst "out1" | return none

      let (.some last') := followInput g tag_split.inst "in1" | return none
      let (.some last) := followInput g last'.inst "in1" | return none

      if last'.inst = first.inst then return none

      return some ([first.inst, last.inst], #v[])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def boxLoopBodyOther' : Pattern String (String × Nat) 0 := fun g => do
  let (.cons inp _ .nil) := g.modules.filter (λ _ (p, _) => p.input.any (λ a b => b.inst.isTop)) | throw .done
  let (.cons out _ .nil) := g.modules.filter (λ _ (p, _) => p.output.any (λ a b => b.inst.isTop)) | throw .done
  return ([inp, out], #v[])

def nonPureMatcher {n} (initNode : String) : Pattern String (String × Nat) n := Graphiti.nonPureMatcher <| toPattern (boxLoopBody initNode)

def nonPureForkMatcher {n} (initNode : String) : Pattern String (String × Nat) n := Graphiti.nonPureForkMatcher <| toPattern (boxLoopBody initNode)

def matcher : Pattern String (String × Nat) 8 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless typ.1 == "initBool" do return none

       let (.some mux) := followOutput g inst "out1" | return none
       unless "mux" == mux.typ.1 do return none

       let (.some mod) := followOutput g mux.inst "out1" | return none
       unless "pure" == mod.typ.1 do return none

       let (.some tag_split) := followOutput g mod.inst "out1" | return none
       unless "split" == tag_split.typ.1 do return none

       let (.some condition_fork) := followOutput g tag_split.inst "out2" | return none
       unless "fork2" == condition_fork.typ.1 do return none

       let (.some branch) := followOutput g tag_split.inst "out1" | return none
       unless "branch" == branch.typ.1 do return none

       let (.some queue) := followOutput g branch.inst "out1" | return none
       unless "queue" == queue.typ.1 do return none

       let (.some queue') := followOutput g branch.inst "out2" | return none
       unless "queue" == queue'.typ.1 do return none

       return some ([mux.inst, condition_fork.inst, branch.inst, tag_split.inst, mod.inst, inst, queue.inst],
           #v[typ.2, mux.typ.2, mod.typ.2, tag_split.typ.2, condition_fork.typ.2, branch.typ.2, queue.typ.2, queue'.typ.2]
         )

    ) none | MonadExceptOf.throw RewriteError.done
  return list

variable (T : Vector Nat 8)
variable (M : Nat)

@[drunfold_defs]
def lhs : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [type = "mux", arg = $(T[0])];
    condition_fork [type = "fork2", arg = $(T[1])];
    branch [type = "branch", arg = $(T[2])];
    tag_split [type = "split", arg = $(T[3])];
    mod [type = "pure", arg = $(T[4])];
    loop_init [type = "initBool", arg = $(T[5])];
    queue [type = "queue", arg = $(T[6])];
    queue_out [type = "queue", arg = $(T[7])];

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

@[drunfold_defs]
def lhs_extract := (lhs T)
  |>.extract ["mux", "condition_fork", "branch", "tag_split", "mod", "loop_init", "queue",  "queue_out"]
  |>.get rfl

theorem double_check_empty_snd T: (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

@[drunfold_defs]
def lhsLower T := (lhs_extract T).fst.lower_TR.get rfl

abbrev TagT := Nat

@[drunfold_defs]
def liftF {α β γ δ} (f : α -> β × δ) : γ × α -> (γ × β) × δ | (g, a) => ((g, f a |>.fst), f a |>.snd)

@[drunfold_defs]
def rhs : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [type = "tagger_untagger_val", arg = $(M+1)];
    merge [type = "merge2", arg = $(M+2)];
    branch [type = "branch", arg = $(M+3)];
    tag_split [type = "split", arg = $(M+4)];
    mod [type = "pure", arg = $(M+5)];

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
def rhs_extract := rhs M
  |>.extract ["tag_split", "tagger", "merge", "branch", "mod"]
  |>.get rfl

@[drunfold_defs]
def rhsLower T := (rhs_extract T |>.1).lower_TR.get rfl

-- #eval IO.print ((rhs Unit "T" (λ _ => default)).fst)

@[drunfold_defs]
def rewrite : Rewrite String (String × Nat) :=
  { abstractions := [],
    params := 8,
    pattern := matcher,
    rewrite := λ l n => ⟨lhsLower l, rhsLower n⟩
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
    : ExprHigh String String × IdentMap String (TModule1 String) := [graphEnv|
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
