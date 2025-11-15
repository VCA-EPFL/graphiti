/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

-- import Graphiti.Core.Rewrites.LoopRewrite
import Graphiti.Core.ExprLowLemmas
import Graphiti.Core.ExprHighElaborator
import Graphiti.Core.Component
import Graphiti.Core.ModuleReduction
import Graphiti.Core.RewriterLemmas

namespace Graphiti.LoopRewrite

open Batteries (AssocList)
open StringModule

open Lean hiding AssocList
open Meta Elab

section Proof

@[drunfold_defs]
def lhs (types : Vector Nat 8) : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [type = "mux", arg = $(types[0])];
    condition_fork [type = "fork2", arg = $(types[1])];
    branch [type = "branch", arg = $(types[2])];
    tag_split [type = "split", arg = $(types[3])];
    mod [type = "pure", arg = $(types[4])];
    loop_init [type = "initBool", arg = $(types[5])];
    queue [type = "queue", arg = $(types[6])];
    queue_out [type = "queue", arg = $(types[7])];

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
def lhs_extract types := (lhs types).extract ["mux", "condition_fork", "branch", "tag_split", "mod", "loop_init", "queue",  "queue_out"] |>.get rfl

@[drunfold_defs]
def lhsLower types := (lhs_extract types).fst.lower_TR.get rfl

theorem lhsLower_locally_wf {types} : (lhsLower types).locally_wf := rfl

@[drunfold_defs]
def liftF {α β γ δ} (f : α -> β × δ) : γ × α -> (γ × β) × δ | (g, a) => ((g, f a |>.fst), f a |>.snd)

@[drunfold_defs]
def rhs (max_type : Nat) : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [type = "tagger_untagger_val", arg = $(max_type+1)];
    merge [type = "merge2", arg = $(max_type+2)];
    branch [type = "branch", arg = $(max_type+3)];
    tag_split [type = "split", arg = $(max_type+4)];
    mod [type = "pure", arg = $(max_type+5)];

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
def rhs_extract max_type := (rhs max_type).extract ["tagger", "merge", "branch", "tag_split", "mod"] |>.get rfl

@[drunfold_defs]
def rhsLower max_type := (rhs_extract max_type).fst.lower_TR.get rfl

variable [e : Environment lhsLower]

instance : BEq (String × Nat) := instBEqOfDecidableEq

-- By the well formedness of the environment
theorem available2 : (∃ T, Batteries.AssocList.find? ("queue", e.types[7]) e.ε = some ⟨_, StringModule.queue T⟩) ∧
      (∃ T, Batteries.AssocList.find? ("queue", e.types[6]) e.ε = some ⟨_, StringModule.queue T⟩) ∧
        (Batteries.AssocList.find? ("initBool", e.types[5]) e.ε = some ⟨_, init Bool false⟩) ∧
          (∃ (T : Σ R, Σ S, R → S), Batteries.AssocList.find? ("pure", e.types[4]) e.ε = some ⟨_, pure T.2.2 ⟩) ∧
            (∃ (A : _ × _), Batteries.AssocList.find? ("split", e.types[3]) e.ε = some ⟨_, split A.1 A.2⟩) ∧
              (∃ A,
                  Batteries.AssocList.find? ("branch", e.types[2]) e.ε = some ⟨_, branch A⟩) ∧
                (∃ A,
                    Batteries.AssocList.find? ("fork2", e.types[1]) e.ε = some ⟨_, fork2 A⟩) ∧
                  ∃ A, Batteries.AssocList.find? ("mux", e.types[0]) e.ε = some ⟨_, mux A⟩ := by
  have h5 := ExprLow.well_formed_wrt_from_well_typed e.6 e.4.1
  dsimp [drunfold_defs, reduceAssocListfind?] at h5
  dsimp [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR, ExprHigh.uncurry] at h5
  dsimp [ExprLow.well_formed_wrt, ExprHigh.uncurry, Env.well_formed'] at h5
  simp only [String.reduceEq, imp_self] at h5
  assumption

-- By the well typedness of the lhs
set_option pp.proofs true in
theorem available3 : available2.2.1.choose = available2.1.choose
  ∧ available2.2.2.2.1.choose.1 = available2.1.choose
  ∧ available2.2.2.2.1.choose.2.1 = (available2.1.choose × Bool)
  ∧ available2.2.2.2.2.1.choose.1 = available2.1.choose
  ∧ available2.2.2.2.2.1.choose.2 = Bool
  ∧ available2.2.2.2.2.2.1.choose = available2.1.choose
  ∧ available2.2.2.2.2.2.2.1.choose = Bool
  ∧ available2.2.2.2.2.2.2.2.choose = available2.1.choose := by
  have h1 := e.5
  dsimp [drunfold_defs, reduceAssocListfind?] at h1
  dsimp [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR, ExprHigh.uncurry] at h1
  have h1' := h1; clear h1
  repeat
    unfold ExprLow.well_typed at h1'
    have ⟨h1'', ⟨mi, T, hwt, h2', h3'⟩⟩ := h1'; clear h1'; have h1' := h1''; clear h1''
    dsimp [ExprLow.build_module_interface, ExprHigh.uncurry] at hwt
    simp only [available2.1.choose_spec, available2.2.1.choose_spec, available2.2.2.1, available2.2.2.2.1.choose_spec,
      available2.2.2.2.2.1.choose_spec, available2.2.2.2.2.2.1.choose_spec, available2.2.2.2.2.2.2.1.choose_spec,
      available2.2.2.2.2.2.2.2.choose_spec] at hwt
    dsimp at hwt
    rw [← ((Option.some.injEq _ _).mp hwt)] at h2' h3'; clear hwt
    dsimp at h2' h3'
    simp -failIfUnchanged (disch := decide) only [AssocList.find?_eraseAll_neq] at h2' h3'
    dsimp [reduceAssocListfind?] at h2' h3'
    dsimp at h2' h3'
  grind

abbrev TagT := Nat
def T := available2.1.choose

noncomputable def cast_f (f : available2.2.2.2.1.choose.1 → available2.2.2.2.1.choose.2.1) : T → T × Bool := by
  rw [available3.2.2.1, available3.2.1] at f; exact f

noncomputable def f : T → T × Bool := cast_f available2.2.2.2.1.choose.2.2

@[drenv] theorem lhs_ε_find1 : e.ε.find? ("queue", e.types[7]) = some ⟨_, StringModule.queue T⟩ := by
  rewrite [available2.1.choose_spec]; rfl
@[drenv] theorem lhs_ε_find2 : e.ε.find? ("queue", e.types[6]) = some ⟨_, StringModule.queue T⟩ := by
  rewrite [available2.2.1.choose_spec, available3.1]; rfl
@[drenv] theorem lhs_ε_find3 : e.ε.find? ("initBool", e.types[5]) = some ⟨_, init Bool false⟩ := by
  rewrite [available2.2.2.1]; rfl
@[drenv] theorem lhs_ε_find4 : e.ε.find? ("pure", e.types[4]) = some ⟨_, pure f⟩ := by
  rewrite [available2.2.2.2.1.choose_spec]
  congr
  · exact available3.2.2.1
  · exact available3.2.1
  · exact available3.2.2.1
  · simp [f, cast_f]
@[drenv] theorem lhs_ε_find5 : e.ε.find? ("split", e.types[3]) = some ⟨_, split T Bool⟩ := by
  rewrite [available2.2.2.2.2.1.choose_spec,available3.2.2.2.1,available3.2.2.2.2.1]; rfl
@[drenv] theorem lhs_ε_find6 : e.ε.find? ("branch", e.types[2]) = some ⟨_, branch T⟩ := by
  rewrite [available2.2.2.2.2.2.1.choose_spec,available3.2.2.2.2.2.1]; rfl
@[drenv] theorem lhs_ε_find7 : e.ε.find? ("fork2", e.types[1]) = some ⟨_, fork2 Bool⟩ := by
  rewrite [available2.2.2.2.2.2.2.1.choose_spec,available3.2.2.2.2.2.2.1]; rfl
@[drenv] theorem lhs_ε_find8 : e.ε.find? ("mux", e.types[0]) = some ⟨_, mux T⟩ := by
  rewrite [available2.2.2.2.2.2.2.2.choose_spec,available3.2.2.2.2.2.2.2]; rfl

noncomputable def ε_rhs : FinEnv String (String × Nat) :=
  ([ (("tagger_untagger_val", e.max_type+1), ⟨_, StringModule.tagger_untagger_val TagT T T⟩)
   , (("merge2", e.max_type+2), ⟨_, merge (TagT × T) 2⟩)
   , (("branch", e.max_type+3), ⟨_, branch (TagT × T)⟩)
   , (("split", e.max_type+4), ⟨_, split (TagT × T) Bool⟩)
   , (("pure", e.max_type+5), ⟨_, StringModule.pure (liftF (γ := TagT) f)⟩)
   ].toAssocList)

@[drenv] theorem rhs_ε_find1 : ε_rhs.find? ("tagger_untagger_val", e.max_type+1) = some ⟨_, StringModule.tagger_untagger_val TagT T T⟩ := by simp [ε_rhs]
@[drenv] theorem rhs_ε_find2 : ε_rhs.find? ("merge2", e.max_type+2) = some ⟨_, merge (TagT × T) 2⟩ := by simp [ε_rhs]
@[drenv] theorem rhs_ε_find3 : ε_rhs.find? ("branch", e.max_type+3) = some ⟨_, branch (TagT × T)⟩ := by simp [ε_rhs]
@[drenv] theorem rhs_ε_find4 : ε_rhs.find? ("split", e.max_type+4) = some ⟨_, split (TagT × T) Bool⟩ := by simp [ε_rhs]
@[drenv] theorem rhs_ε_find5 : ε_rhs.find? ("pure", e.max_type+5) = some ⟨_, StringModule.pure (liftF (γ := TagT) f)⟩ := by simp [ε_rhs]

seal T f in
def_module lhsType : Type :=
  [T| (lhsLower e.types), e.ε.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal T f in
noncomputable def_module lhsEvaled : StringModule lhsType :=
  [e| (lhsLower e.types), e.ε.find? ]
reduction_by
  (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
   dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
   dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
   rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
   dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
   simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
   dsimp [Module.product]
   dsimp -failIfUnchanged
   -- dsimp only [drcomponents, Batteries.AssocList.mapKey, NatModule.stringify_input, InternalPort.map]
   -- dsimp only [reduceAssocListfind?]
   -- set_option pp.explicit true in trace_state

   -- set_option diagnostics true in
   -- dsimp only [reduceModuleconnect'2]
   dsimp only [Module.connect']
   dsimp only [reduceEraseAll]
   dsimp; dsimp [PortMap.getIO, reduceAssocListfind?]
   unfold Module.connect''
   dsimp [Module.liftL, Module.liftR, drcomponents])

seal T f ε_rhs in
def_module rhsModuleType : Type :=
  [T| (rhsLower e.max_type), ε_rhs.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]; dsimp

seal T f ε_rhs in
noncomputable def_module rhsModule : StringModule rhsModuleType :=
  [e| (rhsLower e.max_type), ε_rhs.find? ]
reduction_by
  (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
   dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
   dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
   rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
   dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
   simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
   dsimp [Module.product]
   dsimp -failIfUnchanged
   -- dsimp only [drcomponents, Batteries.AssocList.mapKey, NatModule.stringify_input, InternalPort.map]
   -- dsimp only [reduceAssocListfind?]
   -- set_option pp.explicit true in trace_state

   -- set_option diagnostics true in
   -- dsimp only [reduceModuleconnect'2]
   dsimp only [Module.connect']
   dsimp only [reduceEraseAll]
   dsimp; dsimp [PortMap.getIO, reduceAssocListfind?]
   unfold Module.connect''
   dsimp [Module.liftL, Module.liftR, drcomponents])

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
def ghost_rhs (max_type : Nat)
    : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [type = $("tagger_untagger_val_ghost"), arg = $(max_type+1)];
    merge [type = $("merge2"), arg = $(max_type+2)];
    branch [type = $("branch"), arg = $(max_type+3)];
    tag_split [type = $("split"), arg = $(max_type+4)];
    mod [type = "pure", arg = $(max_type+5)];

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
def ghost_rhs_extract max_type := ghost_rhs max_type
  |>.extract ["tag_split", "tagger", "merge", "branch", "mod"]
  |>.get rfl

noncomputable def ε_rhs_ghost : FinEnv String (String × Nat) :=
  ([ (("tagger_untagger_val_ghost", e.max_type+1), ⟨_, StringModule.tagger_untagger_val_ghost TagT T⟩)
   , (("merge2", e.max_type+2), ⟨_, merge ((TagT × T) × (Nat × T)) 2⟩)
   , (("branch", e.max_type+3), ⟨_, branch ((TagT × T) × (Nat × T))⟩)
   , (("split", e.max_type+4), ⟨_, split ((TagT × T) × (Nat × T)) Bool⟩)
   , (("pure", e.max_type+5), ⟨_, StringModule.pure (liftF2 (γ := T) (liftF (γ := TagT) f))⟩)
   ].toAssocList)

@[drenv] theorem rhs_ghost_ε_find1 : ε_rhs_ghost.find? ("tagger_untagger_val_ghost", e.max_type+1) = some ⟨_, StringModule.tagger_untagger_val_ghost TagT T⟩ := by simp [ε_rhs_ghost]
@[drenv] theorem rhs_ghost_ε_find2 : ε_rhs_ghost.find? ("merge2", e.max_type+2) = some ⟨_, merge ((TagT × T) × (Nat × T)) 2⟩ := by simp [ε_rhs_ghost]
@[drenv] theorem rhs_ghost_ε_find3 : ε_rhs_ghost.find? ("branch", e.max_type+3) = some ⟨_, branch ((TagT × T) × (Nat × T))⟩ := by simp [ε_rhs_ghost]
@[drenv] theorem rhs_ghost_ε_find4 : ε_rhs_ghost.find? ("split", e.max_type+4) = some ⟨_, split ((TagT × T) × (Nat × T)) Bool⟩ := by simp [ε_rhs_ghost]
@[drenv] theorem rhs_ghost_ε_find5 : ε_rhs_ghost.find? ("pure", e.max_type+5) = some ⟨_, StringModule.pure (liftF2 (γ := T) (liftF (γ := TagT) f))⟩ := by simp [ε_rhs_ghost]

@[drunfold_defs]
def rhsGhostLower max_type := (ghost_rhs_extract max_type |>.1).lower_TR.get rfl

seal T f ε_rhs_ghost in
def_module rhsGhostType : Type :=
  [T| (rhsGhostLower e.max_type), ε_rhs_ghost.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]; dsimp

seal T f ε_rhs_ghost in
noncomputable def_module rhsGhostEvaled : StringModule rhsGhostType :=
  [e| (rhsGhostLower e.max_type), ε_rhs_ghost.find? ]
reduction_by
  (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
   dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
   dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
   rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
   dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
   simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
   dsimp [Module.product]
   dsimp -failIfUnchanged
   -- dsimp only [drcomponents, Batteries.AssocList.mapKey, NatModule.stringify_input, InternalPort.map]
   -- dsimp only [reduceAssocListfind?]
   -- set_option pp.explicit true in trace_state

   -- set_option diagnostics true in
   -- dsimp only [reduceModuleconnect'2]
   dsimp only [Module.connect']
   dsimp only [reduceEraseAll]
   dsimp; dsimp [PortMap.getIO, reduceAssocListfind?]
   unfold Module.connect''
   dsimp [Module.liftL, Module.liftR, drcomponents])

omit e in
theorem rw_opaque' {f : Type _ → Type _} {a s s' : Σ T, f T} (heq : s = s') : a = s ↔ a = s' := by
  subst s; rfl

omit e in
theorem rw_opaque'' {f : Type _ → Type _} {a s s' : Σ T, f T} (heq1 : s.fst = s'.fst) (heq2 : s.snd = (congrArg f heq1).mpr s'.snd) : a = s ↔ a = s' := by
  cases s; cases s'
  constructor <;> (intros; subst a; simp_all)
  assumption
  symm; assumption

omit e in
theorem rw_opaque''' {f : Type _ → Type _} {s s' : Σ T, f T} (heq : s = s') : Sigma.mk s.fst s.snd = Sigma.mk s'.fst s'.snd := by grind

seal T f in
theorem lhs_evaled_eq :
  (⟨_, lhsEvaled⟩ : TModule1 String) = ⟨_, [e| (lhsLower e.types), e.ε.find? ]⟩ := by
  (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
   dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
   dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
   rw [rw_opaque''' (by simp only [drenv]; rfl)]; dsimp
   dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
   simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
   dsimp [Module.product]
   dsimp -failIfUnchanged
   -- dsimp only [drcomponents, Batteries.AssocList.mapKey, NatModule.stringify_input, InternalPort.map]
   -- dsimp only [reduceAssocListfind?]
   -- set_option pp.explicit true in trace_state

   -- set_option diagnostics true in
   -- dsimp only [reduceModuleconnect'2]
   dsimp only [Module.connect']
   dsimp only [reduceEraseAll]
   dsimp; dsimp [PortMap.getIO, reduceAssocListfind?]
   unfold Module.connect''
   dsimp [Module.liftL, Module.liftR, drcomponents])
  rfl

seal T f ε_rhs_ghost in
theorem rhs_ghost_evaled_eq :
  (⟨_, rhsGhostEvaled⟩ : TModule1 String) = ⟨_, [e| (rhsGhostLower e.max_type), ε_rhs_ghost.find? ]⟩ := by
  (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
   dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
   dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
   rw [rw_opaque''' (by simp only [drenv]; rfl)]; dsimp
   dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
   simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
   dsimp [Module.product]
   dsimp -failIfUnchanged
   -- dsimp only [drcomponents, Batteries.AssocList.mapKey, NatModule.stringify_input, InternalPort.map]
   -- dsimp only [reduceAssocListfind?]
   -- set_option pp.explicit true in trace_state

   -- set_option diagnostics true in
   -- dsimp only [reduceModuleconnect'2]
   dsimp only [Module.connect']
   dsimp only [reduceEraseAll]
   dsimp; dsimp [PortMap.getIO, reduceAssocListfind?]
   unfold Module.connect''
   dsimp [Module.liftL, Module.liftR, drcomponents])
  rfl

def rewrite : Rewrite String (String × Nat) where
  params := 8
  pattern := default
  rewrite := fun types n => ⟨lhsLower types, rhsGhostLower n⟩
  fresh_types := 5
  name := "loop-rewrite"


  -- ε_ext := ε_rhs
  -- ε_ext_wf := sorry
  -- ε_independent := sorry
  -- rhs_wf := sorry
  -- rhs_wt := sorry
  -- lhs_locally_wf := lhsLower_locally_wf
  -- refinement := by sorry

end Proof

end Graphiti.LoopRewrite
