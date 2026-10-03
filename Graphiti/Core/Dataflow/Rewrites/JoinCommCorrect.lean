/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Graphiti.Core.Dataflow.Component
import Graphiti.Core.Graph.ExprLowLemmas
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.RewriterLemmas
import Graphiti.Core.Dataflow.Rewrites.JoinComm

open Batteries (AssocList)

namespace Graphiti.JoinComm

variable [e : Environment Env.well_formed lhsLower]

local instance : BEq (String × Nat) := instBEqOfDecidableEq

theorem env_types :
    ∃ (T : _ × _), e.ε.find? ("join", e.types[0]) = some ⟨_, StringModule.join T.1 T.2⟩ := by
  have h5 := ExprLow.well_formed_wrt_from_well_typed e.6 e.4.1
  assumption

def T1 := env_types.choose.1
def T2 := env_types.choose.2

@[drenv] theorem lhs_ε_find1 : e.ε.find? ("join", e.types[0]) = some ⟨_, StringModule.join T1 T2⟩ := by
  rewrite [env_types.choose_spec]; rfl

noncomputable def ε_rhs : FinEnv String (String × Nat) :=
  ([ (("join", e.max_type+1), ⟨_, StringModule.join T2 T1⟩)
   , (("pure", e.max_type+2), ⟨_, @StringModule.pure (T2 × T1) (T1 × T2) λ (x, y) => (y, x) ⟩)
   ].toAssocList)

@[drenv] theorem rhs_ε_find1 : ε_rhs.find? ("join", e.max_type+1) = some ⟨_, StringModule.join T2 T1⟩ := by simp [ε_rhs]
@[drenv] theorem rhs_ε_find2 : ε_rhs.find? ("pure", e.max_type+2) = some ⟨_, @StringModule.pure (T2 × T1) (T1 × T2) λ (x, y) => (y, x)⟩ := by simp [ε_rhs]

seal T1 T2 in
def_module lhsType : Type :=
  [T| (lhsLower e.types), e.ε.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal T1 T2 in
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
   dsimp [drcomponents]
   dsimp -failIfUnchanged [reduceAssocListfind?])

seal T1 T2 ε_rhs in
def_module rhsType : Type :=
  [T| (rhsLower e.max_type), ε_rhs.toEnv ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]; dsimp

seal T1 T2 ε_rhs in
noncomputable def_module rhsEvaled : StringModule rhsType :=
  [e| (rhsLower e.max_type), ε_rhs.toEnv ]
reduction_by
  (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
   dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
   dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
   rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
   dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
   simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
   dsimp [Module.product]
   dsimp -failIfUnchanged
   dsimp only [Module.connect']
   dsimp only [reduceEraseAll]
   dsimp; dsimp [PortMap.getIO, reduceAssocListfind?]
   unfold Module.connect''
   dsimp [drcomponents])

instance : MatchInterface rhsEvaled lhsEvaled := by
  unfold rhsEvaled lhsEvaled
  solve_match_interface

def φ (rhs : rhsType) (lhs : lhsType) : Prop :=
  let ⟨ l1 , l2 ⟩ := lhs
  let ⟨ r3  , r1 , r2 ⟩ := rhs
  r3.map Prod.snd ++ r1  = l2 ∧
  r3.map Prod.fst ++ r2  = l1

def refines' : rhsEvaled ⊑_{φ} lhsEvaled := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident mid_i value transition_i
    by_cases HContains: (rhsEvaled.inputs.contains ident)
    . obtain ⟨r3i , ⟨r1i, r2i ⟩ ⟩ := init_i
      obtain ⟨ l1i , l2i ⟩ := init_s
      obtain ⟨ r3m , ⟨r1m, r2m ⟩ ⟩ := mid_i

      unfold rhsEvaled at HContains; simp at HContains
      rcases HContains with h1 | h0
         <;> subst_vars <;> simp
      . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at transition_i
        dsimp at *
        apply Exists.intro (_, _); apply And.intro
        rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
        dsimp; apply And.intro
        rfl; rfl
        apply Exists.intro (_, _)
        apply And.intro
        apply existSR.done
        apply And.intro

        obtain ⟨⟨_, _⟩, _⟩ := transition_i
        subst_vars
        dsimp [φ] at *
        grind

        grind [φ]
      . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at transition_i
        dsimp at *
        apply Exists.intro (_, _); apply And.intro
        rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
        dsimp; apply And.intro
        rfl; rfl
        apply Exists.intro (_, _)
        apply And.intro
        apply existSR.done
        apply And.intro

        obtain ⟨⟨_, _⟩, _⟩ := transition_i
        subst_vars
        dsimp [φ] at *
        grind

        grind [φ]



    . exfalso; exact (PortMap.getIO_not_contained_false transition_i HContains)
  -- output rules
  . intro ident mid_i val transition_o
    by_cases HContains: (rhsEvaled.outputs.contains ident)
    . obtain ⟨r3i , ⟨r1i, r2i ⟩ ⟩ := init_i
      obtain ⟨ l1i , l2i ⟩ := init_s
      obtain ⟨ r3m , ⟨r1m, r2m ⟩ ⟩ := mid_i

      unfold rhsEvaled at HContains; simp at HContains
      subst_vars
      simp
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at transition_o
      dsimp at *
      obtain ⟨tr_l, tr_r⟩ := transition_o

      apply Exists.intro (_, _)
      apply And.intro
      . -- case pos.left
        dsimp [lhsEvaled]
        apply existSR.done

      . -- case pos.right
        apply Exists.intro (r3m.map Prod.fst ++ r2i, r3m.map Prod.snd ++ r1i)
        apply And.intro
        rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
        dsimp

        obtain ⟨hl2, hl1⟩ := Hφ
        rw[←tr_l ] at hl1 hl2
        apply And.intro
        grind; grind

        dsimp [φ] at *
        apply And.intro
        grind; grind
    . exfalso; exact (PortMap.getIO_not_contained_false transition_o HContains)


  -- internal rules
  . intro rule mid_i  ruleIsinternal step
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . unfold rhsEvaled at ruleIsinternal
      dsimp at ruleIsinternal
      -- cases ruleIsinternal
      cases ruleIsinternal
      . simp [Module.liftR, Module.liftL] at step
        dsimp [φ] at *
        apply And.intro
        grind
        grind
      . contradiction







def refines_init : Module.refines_initial rhsEvaled lhsEvaled fun x y => φ x y := by
  -- initial rules
  unfold Module.refines_initial
  dsimp[rhsEvaled]
  dsimp[lhsEvaled]
  intro i init
  apply Exists.intro ([], [])
  apply And.intro
  grind
  dsimp [φ] at *
  grind

theorem refines : rhsEvaled ⊑ lhsEvaled := ⟨inferInstance, φ, refines', refines_init⟩

end Graphiti.JoinComm
