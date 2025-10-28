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

namespace Graphiti.LoopRewrite

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

section Proof

class Environment (lhs : Vector Nat 8 → ExprLow String (String × Nat)) where
  ε : FinEnv String (String × Nat)
  h_wf : ∀ s, Env.well_formed ε.find? s
  types : Vector Nat 8
  h_wt : (lhs types).well_typed ε.find?
  h_lhs_wf : (lhs types).well_formed ε.find?
  max_type : Nat

@[drunfold_defs]
def lhs (types : Vector Nat 8) : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [type = "mux", arg = $(types[0])];
    condition_fork [type = "fork", arg = $(types[1])];
    branch [type = "branch", arg = $(types[2])];
    tag_split [type = "split", arg = $(types[3])];
    mod [type = "pure", arg = $(types[4])];
    loop_init [type = "init", arg = $(types[5])];
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

variable [e : Environment lhsLower]

@[drunfold_defs]
def liftF {α β γ δ} (f : α -> β × δ) : γ × α -> (γ × β) × δ | (g, a) => ((g, f a |>.fst), f a |>.snd)

@[drunfold_defs]
def rhs (max_type : Nat) : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [type = "tagger_untagger_val", arg = $(max_type+1)];
    merge [type = "merge", arg = $(max_type+2)];
    branch [type = "branch", arg = $(max_type+3)];
    tag_split [type = "split", arg = $(max_type+4)];
    mod [type = "tagger_untagger_val", arg = $(max_type+5)];

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

include e in
theorem available : (∃ a, Batteries.AssocList.find? ("queue", (Environment.types lhsLower)[7]) (Environment.ε lhsLower) = some a) ∧
      (∃ a, Batteries.AssocList.find? ("queue", (Environment.types lhsLower)[6]) (Environment.ε lhsLower) = some a) ∧
        (∃ a, Batteries.AssocList.find? ("init", (Environment.types lhsLower)[5]) (Environment.ε lhsLower) = some a) ∧
          (∃ a, Batteries.AssocList.find? ("pure", (Environment.types lhsLower)[4]) (Environment.ε lhsLower) = some a) ∧
            (∃ a, Batteries.AssocList.find? ("split", (Environment.types lhsLower)[3]) (Environment.ε lhsLower) = some a) ∧
              (∃ a,
                  Batteries.AssocList.find? ("branch", (Environment.types lhsLower)[2]) (Environment.ε lhsLower) = some a) ∧
                (∃ a,
                    Batteries.AssocList.find? ("fork", (Environment.types lhsLower)[1]) (Environment.ε lhsLower) = some a) ∧
                  ∃ a, Batteries.AssocList.find? ("mux", (Environment.types lhsLower)[0]) (Environment.ε lhsLower) = some a := by
  have h_wt' := e.h_wt
  have h_wf' := ExprLow.well_formed_implies_wf e.h_lhs_wf
  have h_wf'' := e.h_wf
  dsimp -failIfUnchanged [drunfold_defs, ExprLow.wf, toString, reduceAssocListfind?, reduceListPartition] at h_wf'
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wf'
  dsimp -failIfUnchanged [ExprHigh.uncurry, reduceExprHighLower, ExprLow.wf, ExprLow.all, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wf'
  simp [-AssocList.find?_eq] at h_wf'
  simp only [Option.isSome_iff_exists] at *
  assumption

noncomputable def queue := Exists.choose available.1

include e in
theorem available2 : (∃ T, Batteries.AssocList.find? ("queue", (Environment.types lhsLower)[7]) (Environment.ε lhsLower) = some ⟨_, StringModule.queue T⟩) ∧
      (∃ T, Batteries.AssocList.find? ("queue", (Environment.types lhsLower)[6]) (Environment.ε lhsLower) = some ⟨_, StringModule.queue T⟩) ∧
        (∃ a, Batteries.AssocList.find? ("init", (Environment.types lhsLower)[5]) (Environment.ε lhsLower) = some a) ∧
          (∃ a, Batteries.AssocList.find? ("pure", (Environment.types lhsLower)[4]) (Environment.ε lhsLower) = some a) ∧
            (∃ a, Batteries.AssocList.find? ("split", (Environment.types lhsLower)[3]) (Environment.ε lhsLower) = some a) ∧
              (∃ a,
                  Batteries.AssocList.find? ("branch", (Environment.types lhsLower)[2]) (Environment.ε lhsLower) = some a) ∧
                (∃ a,
                    Batteries.AssocList.find? ("fork", (Environment.types lhsLower)[1]) (Environment.ε lhsLower) = some a) ∧
                  ∃ a, Batteries.AssocList.find? ("mux", (Environment.types lhsLower)[0]) (Environment.ε lhsLower) = some a := by
  sorry

set_option pp.proofs true in
include e in
theorem types : False := by
  have h_wt' := e.h_wt
  dsimp -failIfUnchanged [drunfold_defs, ExprLow.well_typed, toString, reduceAssocListfind?, reduceListPartition] at h_wt'
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wt'
  dsimp -failIfUnchanged [ExprHigh.uncurry, reduceExprHighLower, ExprLow.well_typed, ExprLow.all, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR] at h_wt'
  repeat with_reducible cases ‹_ ∧ _›
  rename_i ha hb hc hd he hf hg hh hi hj hk hl hm hn ho hp hq hr
  clear hb hc hd he hf hg hh hi hj hk hl hm hn ho hp hq hr
  dsimp [ExprLow.build_module_interface] at ha

  -- dsimp [ExprLow.build_module_interface] at h_wt'
  -- rw [Exists.choose_spec (@available2 e).1] at ha
  obtain ⟨mi, T, ha⟩ := ha
  -- rw [Exists.choose_spec (@available2 e).2.1] at ha
  obtain ⟨ha, hb, hc⟩ := ha
  repeat
    rename (Option.bind _ _ = .some _) => hrewrite
    replace hrewrite := Option.bind_eq_some'.mp hrewrite
    obtain ⟨_, hrewrite', _⟩ := hrewrite
  repeat
    rename (Option.map _ _ = .some _) => hrewrite
    replace hrewrite := Option.map_eq_some'.mp hrewrite
    obtain ⟨_, hrewrite', _⟩ := hrewrite

  -- repeat
  --   cases ‹some _ = some _›

  sorry

abbrev TagT := Nat

def ε_rhs : FinEnv String (String × Nat) :=
  ([ (("tagger_untagger_val", e.ε.max_type+1), ⟨_, StringModule.tagger_untagger_val TagT T T⟩)
   , (("join", ε.max_type+3), ⟨_, join (T1 ε h_wf S1 S2 h_wt).2 (T2 ε h_wf S1 S2 h_wt).2⟩)
   , (("join", ε.max_type+2), ⟨_, join (T1 ε h_wf S1 S2 h_wt).1 ((T1 ε h_wf S1 S2 h_wt).2 × (T2 ε h_wf S1 S2 h_wt).2)⟩)
   ].toAssocList)

@[drunfold_defs] def rewriteLhsRhs := rewrite.rewrite [DataS] |>.get rfl

def environmentLhs : IdentMap String (TModule1 String) := lhs Data DataS f |>.snd

def environmentRhs : IdentMap String (TModule1 String) := rhs Data DataS f |>.snd

open Graphiti.StringModule

@[drenv] theorem find?_bag_data : (Batteries.AssocList.find? ("bag " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, bag Data⟩ := by
  unfold environmentLhs lhs
  simp
  exists "bag " ++ DataS
  sorry
@[drenv] theorem find?_queue_data : (Batteries.AssocList.find? ("queue " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, queue Data⟩ := by sorry


@[drenv] theorem find?_init_data : (Batteries.AssocList.find? ("init Bool false") (environmentLhs DataS f)) = .some ⟨_, init Bool false⟩ := sorry
@[drenv] theorem find?_branch_data : (Batteries.AssocList.find? ("branch " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, branch Data⟩ := sorry
@[drenv] theorem find?_pure_f : (Batteries.AssocList.find? ("pure f") (environmentLhs DataS f)) = .some ⟨_, pure f⟩ := sorry
@[drenv] theorem find?_mux_data : (Batteries.AssocList.find? ("mux " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, mux Data⟩ := sorry
@[drenv] theorem find?_fork_bool : (Batteries.AssocList.find? ("fork Bool 2") (environmentLhs DataS f)) = .some ⟨_, fork2 Bool⟩ := sorry
@[drenv] theorem find?_split_data : (Batteries.AssocList.find? ("split " ++ DataS ++ " Bool") (environmentLhs DataS f)) = .some ⟨_, split Data Bool⟩ := sorry

-- @[drcompute] theorem find?_fork_bool2 : (Batteries.AssocList.find? ("fork2 Bool") (environmentRhs DataS f)) = .some ⟨_, fork2 Bool⟩ := sorry
@[drenv] theorem find?_branch_data2 : (Batteries.AssocList.find? ("branch (TagT × " ++ DataS ++ ")") (environmentRhs DataS f)) = .some ⟨_, branch (TagT × Data)⟩ := sorry
@[drenv] theorem find?_pure_f2 : (Batteries.AssocList.find? ("pure (liftF f)") (environmentRhs DataS f)) = .some ⟨_, pure (liftF (γ := TagT) f)⟩ := sorry
@[drenv] theorem find?_merge_data2 : (Batteries.AssocList.find? ("merge (TagT × " ++ DataS ++ ") 2") (environmentRhs DataS f)) = .some ⟨_, merge (TagT × Data) 2⟩ := sorry
@[drenv] theorem find?_split_data2 : (Batteries.AssocList.find? ("split (TagT × " ++ DataS ++ ") Bool") (environmentRhs DataS f)) = .some ⟨_, split (TagT × Data) Bool⟩ := sorry
@[drenv] theorem find?_tagger_data2 : (Batteries.AssocList.find? ("tagger_untagger_val TagT " ++ DataS ++ " " ++ DataS) (environmentRhs DataS f)) = .some ⟨_, tagger_untagger_val TagT Data Data⟩ := sorry

seal environmentLhs in
def lhsTypeEvaled : Type := by
  precomputeTac ([T| (rewriteLhsRhs DataS).input_expr, (environmentLhs DataS f).find? ]) by
    simp [drunfold,seval,drcompute,drdecide]

#guard_msgs (drop info) in
#eval [e|(Graphiti.ExprLow.base
                      { input := Batteries.AssocList.cons
                                   { inst := Graphiti.InstIdent.top, name := "in1" }
                                   { inst := Graphiti.InstIdent.internal "bag", name := "in1" }
                                   (Batteries.AssocList.nil),
                        output := Batteries.AssocList.cons
                                    { inst := Graphiti.InstIdent.top, name := "out1" }
                                    { inst := Graphiti.InstIdent.top, name := "o_out" }
                                    (Batteries.AssocList.nil) }
                      "bag T"), (environmentLhs "T" (λ _ => ((), true))).find?].outputs.keysList

#guard_msgs (drop info) in
#eval ([e| (rewriteLhsRhs "T").input_expr, (environmentLhs "T" (λ _ => ((), true))).find? ]).outputs.keysList

variable (Data) in
abbrev lhsType := (List Data ×
          List Data ×
            NatModule.Named "init" (List Bool × Bool) ×
              NatModule.Named "pure" (List (Data × Bool)) ×
                NatModule.Named "split" (List Data × List Bool) ×
                  NatModule.Named "branch" (List Data × List Bool) ×
                    NatModule.Named "fork2" (List Bool × List Bool) ×
                      NatModule.Named "mux" (List Data × List Data × List Bool))

seal environmentLhs in
def lhsEvaled : Module String (lhsType Data) := by
  precomputeTac [e| (rewriteLhsRhs DataS).input_expr, (environmentLhs DataS f).find? ] by
    (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
     dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
     dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, toString]
     dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
     rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
     dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
     simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
     dsimp [Module.product]
     -- dsimp only [reduceModuleconnect'2]
     unfold Module.connect'; dsimp
     dsimp only [reduceEraseAll]
     dsimp; dsimp [reduceAssocListfind?]
     )
    unfold PortMap.getIO
    dsimp [reduceAssocListfind?]

variable (Data) in
abbrev rhsType :=
        (NatModule.Named "pure" (List ((TagT × Data) × Bool)) ×
          NatModule.Named "branch" (List (TagT × Data) × List Bool) ×
            NatModule.Named "merge" (List (TagT × Data)) ×
              NatModule.Named "tagger_untagger_val" (List TagT × AssocList TagT Data × List Data) ×
                NatModule.Named "split" (List (TagT × Data) × List Bool))

seal environmentRhs in
def rhsEvaled : Module String (rhsType Data) := by
  precomputeTac [e| (rewriteLhsRhs DataS).output_expr, (environmentRhs DataS f).find? ] by
    (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
     dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
     dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, toString]
     dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
     rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
     dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
     simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
     dsimp [Module.product]
     -- dsimp only [reduceModuleconnect'2]
     unfold Module.connect'; dsimp
     dsimp only [reduceEraseAll]
     dsimp; dsimp [reduceAssocListfind?]

     unfold Module.connect''
     dsimp [Module.liftL, Module.liftR, drcomponents])
    unfold PortMap.getIO
    dsimp [reduceAssocListfind?]

@[drenv] theorem find?_branch_data3 : (Batteries.AssocList.find? ("branch ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ")") (environmentRhsGhost DataS f)) = .some ⟨_, branch ((TagT × Data) × (Nat × Data))⟩ := sorry
@[drenv] theorem find?_pure_f3 : (Batteries.AssocList.find? "pure (liftF2 (liftF f))" (environmentRhsGhost DataS f)) = .some ⟨_, pure (liftF2 (γ := Data) (liftF (γ := TagT) f))⟩ := sorry
@[drenv] theorem find?_merge_data3 : (Batteries.AssocList.find? ("merge ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ") 2") (environmentRhsGhost DataS f)) = .some ⟨_, merge ((TagT × Data) × (Nat × Data)) 2⟩ := sorry
@[drenv] theorem find?_split_data3 : (Batteries.AssocList.find? ("split ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ") Bool") (environmentRhsGhost DataS f)) = .some ⟨_, split ((TagT × Data) × (Nat × Data)) Bool⟩ := sorry
@[drenv] theorem find?_tagger_data3 : (Batteries.AssocList.find? ("tagger_untagger_val_ghost TagT " ++ DataS) (environmentRhsGhost DataS f)) = .some ⟨_, StringModule.tagger_untagger_val_ghost TagT Data ⟩ := sorry

variable (Data) in
abbrev rhsGhostType :=
        (NatModule.Named "pure" (List (((TagT × Data) × ℕ × Data) × Bool)) ×
          NatModule.Named "branch" (List ((TagT × Data) × ℕ × Data) × List Bool) ×
            NatModule.Named "merge" (List ((TagT × Data) × ℕ × Data)) ×
              NatModule.Named "tagger_untagger_val_ghost" (List (TagT × Data) × AssocList TagT (Data × (Nat × Data)) × List (Data × ℕ × Data)) ×
                NatModule.Named "split" (List ((TagT × Data) × ℕ × Data) × List Bool))

seal environmentRhsGhost in
def rhsGhostEvaled : Module String (rhsGhostType Data) := by
  precomputeTac [e| rhsGhostLower DataS, (environmentRhsGhost DataS f).find? ] by
    (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
     dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
     dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, toString]
     dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
     rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
     dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
     simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
     dsimp [Module.product]
     -- dsimp only [reduceModuleconnect'2]
     unfold Module.connect'; dsimp
     dsimp only [reduceEraseAll]
     dsimp; dsimp [reduceAssocListfind?]

     unfold Module.connect''
     dsimp [Module.liftL, Module.liftR, drcomponents])
    unfold PortMap.getIO
    dsimp [reduceAssocListfind?]

end Proof

end Graphiti.LoopRewrite
