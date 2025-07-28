/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewrites.LoopRewrite
import Graphiti.Core.ExprLowLemmas
import Graphiti.Core.ExprHighElaborator
import Graphiti.Core.Component
import Graphiti.Core.ModuleReduction

namespace Graphiti.LoopRewrite

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab



section Proof

variable {Data : Type}
variable (DataS : String)
variable (f : Data → Data × Bool)

variable [Inhabited Data]

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
