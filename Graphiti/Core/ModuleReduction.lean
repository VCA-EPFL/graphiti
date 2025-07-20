/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

import Graphiti.Tactic
import Graphiti.Module
import Graphiti.AssocList
import Graphiti.ExprHighLemmas

open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term

open Batteries (AssocList)

namespace Graphiti.Module

variable {Ident : Type _}

def product' {S : Type _} (m1 m2 : Module Ident S) : Module Ident S :=
  {
    inputs := m1.inputs ++ m2.inputs,
    outputs := m1.outputs ++ m2.outputs,
    internals := m1.internals ++ m2.internals,
    init_state := λ s => m1.init_state s ∧ m2.init_state s,
  }

def liftLM {S S' : Type _} (m1 : Module Ident S) : Module Ident (S × S') :=
  {
    inputs := m1.inputs.mapVal (λ _ => Module.liftL)
    outputs := m1.outputs.mapVal (λ _ => Module.liftL)
    internals := m1.internals.map Module.liftL'
    init_state := λ (s1, s2) => m1.init_state s1
  }

def liftRM {S S' : Type _} (m1 : Module Ident S) : Module Ident (S' × S) :=
  {
    inputs := m1.inputs.mapVal (λ _ => Module.liftR)
    outputs := m1.outputs.mapVal (λ _ => Module.liftR)
    internals := m1.internals.map Module.liftR'
    init_state := λ (s1, s2) => m1.init_state s2
  }

def liftRLM {S S' S'' : Type _} (m1 : Module Ident S) := (m1.liftRM (S' := S')).liftLM (S' := S'')

@[drnorm] theorem liftRLM_eq {S S' S'' : Type _} {m1 : Module Ident S} : (m1.liftRM (S' := S')).liftLM (S' := S'') = m1.liftRLM := rfl

def liftRRM {S S' S'' : Type _} (m1 : Module Ident S) := (m1.liftRM (S' := S')).liftRM (S' := S'')

theorem liftRRM_eq {S S' S'' : Type _} {m1 : Module Ident S} : (m1.liftRM (S' := S')).liftRM (S' := S'') = m1.liftRRM := rfl

def liftRRLM {S S1 S2 S3 : Type _} (m1 : Module Ident S) := ((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftLM (S' := S3)

@[drnorm] theorem liftRRLM_eq {S S1 S2 S3 : Type _} {m1 : Module Ident S} : ((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftLM (S' := S3) = m1.liftRRLM := rfl

def liftRRRM {S S1 S2 S3 : Type _} (m1 : Module Ident S) := ((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)

theorem liftRRRM_eq {S S1 S2 S3 : Type _} {m1 : Module Ident S} : ((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3) = m1.liftRRRM := rfl

def liftRRRLM {S S1 S2 S3 S4 : Type _} (m1 : Module Ident S) := (((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)).liftLM (S' := S4)

@[drnorm] theorem liftRRRLM_eq {S S1 S2 S3 S4 : Type _} {m1 : Module Ident S} : (((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)).liftLM (S' := S4) = m1.liftRRRLM := rfl

def liftRRRRM {S S1 S2 S3 S4 : Type _} (m1 : Module Ident S) := (((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)).liftRM (S' := S4)

theorem liftRRRRM_eq {S S1 S2 S3 S4 : Type _} {m1 : Module Ident S} : (((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)).liftRM (S' := S4) = m1.liftRRRRM := rfl

def liftRRRRLM {S S1 S2 S3 S4 S5 : Type _} (m1 : Module Ident S) := ((((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)).liftRM (S' := S4)).liftLM (S' := S5)

@[drnorm] theorem liftRRRRLM_eq {S S1 S2 S3 S4 S5 : Type _} {m1 : Module Ident S} : ((((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)).liftRM (S' := S4)).liftLM (S' := S5) = m1.liftRRRRLM := rfl

def liftRRRRRM {S S1 S2 S3 S4 S5 : Type _} (m1 : Module Ident S) := ((((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)).liftRM (S' := S4)).liftRM (S' := S5)

theorem liftRRRRRM_eq {S S1 S2 S3 S4 S5 : Type _} {m1 : Module Ident S} : ((((m1.liftRM (S' := S1)).liftRM (S' := S2)).liftRM (S' := S3)).liftRM (S' := S4)).liftRM (S' := S5) = m1.liftRRRRRM := rfl

def liftRL {S S' S'' : Type _} m1 := Module.liftL (S' := S'') (Module.liftR (S := S) (S' := S') m1)

@[drnorm] theorem liftRL_eq {S S' S'' : Type _} {m1} : Module.liftL (S' := S'') (Module.liftR (S := S) (S' := S') m1) = Module.liftRL m1 := rfl

def liftRR {S S' S'' : Type _} m1 := Module.liftR (S := S'') (Module.liftR (S := S) (S' := S') m1)

theorem liftRR_eq {S S' S'' : Type _} {m1} : Module.liftR (S := S'') (Module.liftR (S := S) (S' := S') m1) = Module.liftRR m1 := rfl

def liftRRL {S S1 S2 S3 : Type _} m1 := Module.liftL (S' := S3) (Module.liftR (S := S2) (Module.liftR (S := S) (S' := S1) m1))

@[drnorm] theorem liftRRL_eq {S S1 S2 S3 : Type _} {m1} : Module.liftL (S' := S3) (Module.liftR (S := S2) (Module.liftR (S := S) (S' := S1) m1)) = Module.liftRRL m1 := rfl

def liftRRR {S S1 S2 S3 : Type _} m1 := Module.liftR (S := S3) (Module.liftR (S := S2) (Module.liftR (S := S) (S' := S1) m1))

theorem liftRRR_eq {S S1 S2 S3 : Type _} {m1} : Module.liftR (S := S3) (Module.liftR (S := S2) (Module.liftR (S := S) (S' := S1) m1)) = Module.liftRRR m1 := rfl

def cons_internals {S : Type _} (m1 : Module Ident S) (r : S → S → Prop) : Module Ident S :=
  { m1 with internals := r :: m1.internals }

@[drnorm] theorem product_product' {S S' : Type _} {m1 : Module Ident S} {m2 : Module Ident S'} :
  m1.product m2 = m1.liftLM.product' m2.liftRM := rfl

@[drnorm] theorem product_liftLM_comm {S S' : Type _} {m1 m2 : Module Ident S} :
  (m1.product' m2).liftLM (S' := S') = m1.liftLM.product' m2.liftLM := by
  simp only [product', liftLM, AssocList.mapVal_append, List.map_append]

@[drnorm] theorem product_liftRM_comm {S S' : Type _} {m1 m2 : Module Ident S} :
  (m1.product' m2).liftRM (S' := S') = m1.liftRM.product' m2.liftRM := by
  simp only [product', liftRM, AssocList.mapVal_append, List.map_append]

variable [DecidableEq Ident]

def erase_input {S : Type _} (m1 : Module Ident S) (i : InternalPort Ident) : Module Ident S :=
  { m1 with inputs := m1.inputs.eraseAll i }

def erase_output {S : Type _} (m1 : Module Ident S) (o : InternalPort Ident) : Module Ident S :=
  { m1 with outputs := m1.outputs.eraseAll o }

def erase_inputP (m1 : PortMapping Ident) (i : InternalPort Ident) : PortMapping Ident :=
  { m1 with input := m1.input.eraseAllVal i }

def erase_outputP (m1 : PortMapping Ident) (o : InternalPort Ident) : PortMapping Ident :=
  { m1 with output := m1.input.eraseAllVal o }

@[drnorm] theorem renamePorts_liftLM_comm {S S' : Type _} {m1 : Module Ident S} {p} :
  (m1.renamePorts p).liftLM (S' := S') = m1.liftLM.renamePorts p := by
  simp only [renamePorts, liftLM, mapPorts2, mapInputPorts, mapOutputPorts, AssocList.mapVal_mapKey]

@[drnorm] theorem renamePorts_liftRM_comm {S S' : Type _} {m1 : Module Ident S} {p} :
  (m1.renamePorts p).liftRM (S' := S') = m1.liftRM.renamePorts p := by
  simp only [renamePorts, liftRM, mapPorts2, mapInputPorts, mapOutputPorts, AssocList.mapVal_mapKey]

theorem connect'_norm {S : Type _} {m : Module Ident S} {o i} :
  m.connect' o i
  = ((m.erase_output o).erase_input i).cons_internals (connect'' (m.outputs.getIO o).2 (m.inputs.getIO i).2) := rfl

@[drnorm] theorem cons_internals_erase_input {S : Type _} {m : Module Ident S} {i l} :
  (m.cons_internals l).erase_input i = (m.erase_input i).cons_internals l := rfl

@[drnorm] theorem cons_internals_erase_output {S : Type _} {m : Module Ident S} {o l} :
  (m.cons_internals l).erase_output o = (m.erase_output o).cons_internals l := rfl

@[drnorm] theorem erase_input_output {S : Type _} {m : Module Ident S} {o i} :
  (m.erase_input i).erase_output o = (m.erase_output o).erase_input i := rfl

def renameAssocList' {α β γ} [BEq α] (m : AssocList α β) (p : AssocList α γ) : AssocList γ β :=
  match m with
  | .nil => .nil
  | .cons k v xs =>
    match p.find? k with
    | .some k' => renameAssocList' xs p |>.cons k' v
    | .none => renameAssocList' xs p

def renamePorts' {S : Type _} (m : Module Ident S) (p : PortMapping Ident) : Module Ident S :=
  { m with inputs := renameAssocList' m.inputs p.input
           outputs := renameAssocList' m.outputs p.output
  }

def SigmaSnd {a b} := @Sigma.snd a b

@[drnorm] theorem renamePorts_getIO_inputs_neq {S : Type _} {m m' : Module Ident S} {i p} :
  ¬ p.input.containsVal i →
  ((m.renamePorts' p).product' m').inputs.getIO i = m'.inputs.getIO i := sorry

@[drnorm] theorem cons_internals_getIO_inputs {S : Type _} {m : Module Ident S} {i p} :
  (m.cons_internals p).inputs.getIO i = m.inputs.getIO i := rfl

@[drnorm] theorem cons_internals_getIO_outputs {S : Type _} {m : Module Ident S} {i p} :
  (m.cons_internals p).outputs.getIO i = m.outputs.getIO i := rfl

-- @[drnorm] theorem liftLM_getIO_inputs {S S' : Type _} {m : Module Ident S} {i} :
--   (m.liftLM (S' := S')).inputs.getIO i = Module.liftL (m.inputs.getIO i) := sorry

-- @[drnorm] theorem liftRM_getIO_inputs {S S' : Type _} {m : Module Ident S} {i} :
--   (m.liftRM (S' := S')).inputs.getIO i = Module.liftR (m.inputs.getIO i) := sorry

-- @[drnorm] theorem liftLM_getIO_outputs {S S' : Type _} {m : Module Ident S} {i} :
--   (m.liftLM (S' := S')).outputs.getIO i = Module.liftL (m.outputs.getIO i) := sorry

-- @[drnorm] theorem liftRM_getIO_outputs {S S' : Type _} {m : Module Ident S} {i} :
--   (m.liftRM (S' := S')).outputs.getIO i = Module.liftR (m.outputs.getIO i) := sorry

@[drnorm] theorem renamePorts_getIO_outputs_neq {S : Type _} {m m' : Module Ident S} {i p} :
  ¬ p.output.containsVal i →
  ((m.renamePorts' p).product' m').outputs.getIO i = m'.outputs.getIO i := sorry

@[drnorm] theorem renamePorts_getIO_inputs_eq {S : Type _} {m m' : Module Ident S} {i p} :
  p.input.containsVal i →
  ((m.renamePorts' p).product' m').inputs.getIO i = (m.renamePorts' p).inputs.getIO i := sorry

@[drnorm] theorem renamePorts_getIO_outputs_eq {S : Type _} {m m' : Module Ident S} {i p} :
  p.output.containsVal i →
  ((m.renamePorts' p).product' m').outputs.getIO i = (m.renamePorts' p).outputs.getIO i := sorry

@[drnorm] theorem renamePorts_getIO_inputs_eq_base {S : Type _} {m : Module Ident S} {i p} :
  p.input.containsVal i →
  (m.renamePorts' p).inputs.getIO i = m.inputs.getIO i := sorry

@[drnorm] theorem renamePorts_getIO_outputs_eq_base {S : Type _} {m : Module Ident S} {i p} :
  p.input.containsVal i →
  (m.renamePorts' p).outputs.getIO i = m.outputs.getIO i := sorry

@[drnorm] theorem renamePorts_renamePorts' {S : Type _} {m : Module Ident S} {p} :
  m.renamePorts p = m.renamePorts' p := by sorry

@[drnorm] theorem renamePorts'_erase_input_ncontains {S : Type _} {m : Module Ident S} {i p} :
  ¬ p.input.containsVal i →
  (m.renamePorts' p).erase_input i = m.renamePorts' p := by sorry

@[drnorm] theorem renamePorts'_erase_input {S : Type _} {m : Module Ident S} {i p} :
  (m.renamePorts' p).erase_input i = m.renamePorts' (Module.erase_inputP p i) := by sorry

@[drnorm] theorem renamePorts'_erase_output_ncontains {S : Type _} {m : Module Ident S} {o p} :
  ¬ p.output.containsVal o →
  (m.renamePorts' p).erase_output o = m.renamePorts' p := by sorry

@[drnorm] theorem renamePorts'_erase_output {S : Type _} {m : Module Ident S} {o p} :
  (m.renamePorts' p).erase_output o = m.renamePorts' (Module.erase_outputP p o) := by sorry

@[drnorm] theorem erase_output_product {S : Type _} {m m' : Module Ident S} {o} :
  (m.product' m').erase_output o = (m.erase_output o).product' (m'.erase_output o) := by sorry

@[drnorm] theorem erase_input_product {S : Type _} {m m' : Module Ident S} {o} :
  (m.product' m').erase_input o = (m.erase_input o).product' (m'.erase_input o) := by sorry

@[drnorm] theorem renamePorts'_liftLM {S S' : Type _} {m : Module Ident S} {p} :
  (m.renamePorts' p).liftLM (S' := S') = m.liftLM.renamePorts' p := by sorry

@[drnorm] theorem renamePorts'_liftRM {S S' : Type _} {m : Module Ident S} {p} :
  (m.renamePorts' p).liftRM (S' := S') = m.liftRM.renamePorts' p := by sorry

end Graphiti.Module

namespace Graphiti

open Lean Meta Simp Qq

/--
Reduce `toString 5` to `"5"`
-/
@[inline] def reduceModuleconnect'Imp (e : Expr) : SimpM Simp.DStep := do
  -- trace[Meta.Tactic.simp.rewrite] m!"Heyyyy\n{e}\nwhnf: {← withDefault <| Meta.whnf e}"
  -- let rd ← withDefault <| whnf e
  -- let rd1 ← withDefault <| reduce <| rd.getArg! 2
  -- let rd2 ← withDefault <| reduce <| rd.getArg! 3
  let rdm := e.getArg! 3
  let rdo ← withDefault <| whnf <| e.getArg! 4
  let rdi ← withDefault <| whnf <| e.getArg! 5
  -- unless rdm.isAppOf ``Module.mk do
  --   trace[Meta.Tactic.simp.rewrite] m!"Heyyyy\n{rdm}"
  --   return .continue
  let findo ← mkAppM ``Batteries.AssocList.find? #[rdo, ← mkAppM ``Module.outputs #[rdm]]
  let ruleo ← withDefault <| whnf findo
  unless ruleo.isAppOf ``Option.some do
    trace[Meta.Tactic.simp.debug] m!"Error:\n{findo}\n{rdo}\n{ruleo}"
    return .continue
  let findi ← mkAppM ``Batteries.AssocList.find? #[rdi, ← mkAppM ``Module.inputs #[rdm]]
  let rulei ← withDefault <| whnf findi
  unless rulei.isAppOf ``Option.some do
    trace[Meta.Tactic.simp.debug] m!"Error:\n{findi}\n{rdi}\n{rulei}"
    return .continue
  let eraseOut ← mkAppM ``Batteries.AssocList.eraseAll #[rdo, ← mkAppM ``Module.outputs #[rdm]]
  let eraseIn ← mkAppM ``Batteries.AssocList.eraseAll #[rdi, ← mkAppM ``Module.inputs #[rdm]]
  let consList ← mkAppM ``List.cons #[← mkAppM ``Module.connect'' #[← mkAppM ``Sigma.snd #[ruleo.getArg! 1], ← mkAppM ``Sigma.snd #[rulei.getArg! 1]], ← mkAppM ``Module.internals #[rdm]]
  let mod ← mkAppM ``Module.mk #[eraseIn, eraseOut, consList, ← mkAppM ``Module.init_state #[rdm]]
  return .done mod

@[inline] def reduceModuleconnect'2Imp (e : Expr) : SimpM Simp.DStep := do
  -- trace[Meta.Tactic.simp.rewrite] m!"Heyyyy\n{e}\nwhnf: {← withDefault <| Meta.whnf e}"
  -- let rd ← withDefault <| whnf e
  -- let rd1 ← withDefault <| reduce <| rd.getArg! 2
  -- let rd2 ← withDefault <| reduce <| rd.getArg! 3
  let rdm ← withDefault <| whnf <| e.getArg! 3
  let rdo ← withDefault <| whnf <| e.getArg! 4
  let rdi ← withDefault <| whnf <| e.getArg! 5
  unless rdm.isAppOf ``Module.mk do
    trace[Meta.Tactic.simp.debug] m!"Error:\n{rdm}"
    return .continue
  let findo ← mkAppM ``Batteries.AssocList.find? #[rdo, rdm.getArg! 3]
  let ruleo ← withDefault <| whnf findo
  unless ruleo.isAppOf ``Option.some do
    trace[Meta.Tactic.simp.debug] m!"Error:\n{findo}\n{rdo}\n{ruleo}"
    return .continue
  let findi ← mkAppM ``Batteries.AssocList.find? #[rdi, rdm.getArg! 2]
  let rulei ← withDefault <| whnf findi
  unless rulei.isAppOf ``Option.some do
    trace[Meta.Tactic.simp.debug] m!"Error:\n{findi}\n{rdi}\n{rulei}"
    return .continue
  let eraseOut ← mkAppM ``Batteries.AssocList.eraseAll #[rdo, rdm.getArg! 3]
  let eraseIn ← mkAppM ``Batteries.AssocList.eraseAll #[rdi, rdm.getArg! 2]
  let consList ← mkAppM ``List.cons #[← mkAppM ``Module.connect'' #[← mkAppM ``Sigma.snd #[ruleo.getArg! 1], ← mkAppM ``Sigma.snd #[rulei.getArg! 1]], rdm.getArg! 4]
  let mod ← mkAppM ``Module.mk #[eraseIn, eraseOut, consList, rdm.getArg! 5]
  return .done mod

@[inline] def reduceAssocListfind?Imp (e : Expr) : SimpM Simp.DStep := do
  return .done (← withDefault <| whnf e)

dsimproc [] reduceModuleconnect' (Module.connect' _ _ _) := reduceModuleconnect'Imp
dsimproc [] reduceModuleconnect'2 (Module.connect' (Module.mk _ _ _ _) _ _) := reduceModuleconnect'2Imp
dsimproc [drcompute] reduceAssocListfind? (Batteries.AssocList.find? _ _) := reduceAssocListfind?Imp
dsimproc [drcompute] reducePortMapgetIO (PortMap.getIO _ _) := reduceAssocListfind?Imp
dsimproc [] reduceStringifyInput (NatModule.stringify_input _) := reduceAssocListfind?Imp
dsimproc [] reduceEraseAll (Batteries.AssocList.eraseAll _ _) := reduceAssocListfind?Imp
dsimproc [] reduceListPartition (Prod.fst (List.partition _ _)) := reduceAssocListfind?Imp
dsimproc [] reduceExprHighLower (ExprHigh.lower_TR _) := reduceAssocListfind?Imp
dsimproc [] reduceExprHighLowerConnTR (ExprHigh.lower'_conn_TR _ _) := reduceAssocListfind?Imp
dsimproc [] reduceExprHighLowerProdTR (ExprHigh.lower'_prod_TR _ _) := reduceAssocListfind?Imp

macro "dr_reduce_module" : tactic =>
  `(tactic|
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [Module.liftL, Module.liftR, drcomponents]))

/--
Define a module by reducing it beforehand.
-/
elab mods:declModifiers "def_module " name:ident l:optDeclSig " := " t:term "reduction_by " tac:tacticSeq : command => do
  elabCommand <|← `($mods:declModifiers def $name $l := by precomputeTac $t by $tac)

elab mods:declModifiers "def_module " name:ident l:optDeclSig " := " t:term : command => do
  elabCommand <|← `($mods:declModifiers def_module $name $l := $t reduction_by dr_reduce_module)

/--
Define a module by reducing it beforehand.
-/
elab mods:declModifiers "defmodule " name:ident binders:bracketedBinder* " := " t:term "reduction_by " tac:tacticSeq : command => do
  -- let mvar ← Lean.Meta.mkFreshExprMVar
  elabCommand <|← `($mods:declModifiers def $name:ident $binders:bracketedBinder* := by precomputeTacEq $t by $tac)

elab mods:declModifiers "defmodule " name:ident binders:bracketedBinder* " := " t:term : command => do
  elabCommand <|← `($mods:declModifiers def_module $name $binders:bracketedBinder* := $t reduction_by dr_reduce_module)

macro "solve_match_interface" : tactic =>
  `(tactic|
    (rw [MatchInterface_simpler_iff]
     intros; and_intros
     <;> (apply Batteries.AssocList.find?_eq_contains
          <;> (intro k heq; replace heq := Batteries.AssocList.keysInMap heq; fin_cases heq <;> rfl)))
  )

end Graphiti
