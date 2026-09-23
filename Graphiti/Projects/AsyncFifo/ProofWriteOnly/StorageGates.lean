/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteBank
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadBank
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Lifting
import Graphiti.Projects.AsyncFifo.TopGates
import Graphiti.Projects.AsyncFifo.components.level6.WriteBank
import Graphiti.Projects.AsyncFifo.components.level6.ReadBank

/-! # The storage blocks as gates

For each storage block `X`: `X.gates` (`TopGates.lean`, the same graph with every child replaced
by its gates) refines `X`'s reduced implementation `X.xNetlist`, by substitution, and so `X`'s
specification: `X.gates_refines`.  `X.netlist_sigma` says the reduced implementation is the
graph's; `TopRefinement.lean` uses it for `X.impl_refines`. -/

namespace Graphiti.AsyncFifo
open Batteries (AssocList)
open Contracts Timed

theorem BusReg.gateEnv_dff : BusReg.gateEnv.find? "dff" = .some ⟨_, Dff.dffImpl⟩ := rfl

theorem BusReg.gateEnv_find_ne (t : String) (h0 : t ≠ "dff") :
    BusReg.gateEnv.find? t = BusReg.benv.find? t := by
  have e0 : ("dff" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h0)
  simp [BusReg.gateEnv, AssocList.find?, e0]

theorem BusReg.wf_gateEnv : ExprLow.wf BusReg.gateEnv.find? BusReg.busLowered := by rfl
theorem BusReg.wf_benv : ExprLow.wf BusReg.benv.find? BusReg.busLowered := by rfl

seal BusReg.benv in
theorem BusReg.netlist_sigma :
    (⟨BusReg.busT, BusReg.busNetlist⟩ : Σ T, StringModule T) =
      ExprLow.build_module BusReg.benv.find? BusReg.busLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

/-- **The three-bit Gray-pointer register, its three flip-flops expanded to gates.** -/
theorem BusReg.gates_refines : BusReg.gates ⊑ BusReg.busSpec := by
  refine Module.refines_transitive _ ?_ BusReg.reg_refines
  refine Module.refines_transitive _ ?_ (Module.refines_eq' BusReg.netlist_sigma.symm)
  apply ExprLow.refines_env _ BusReg.wf_gateEnv BusReg.wf_benv
  intro i t
  by_cases h0 : t = "dff"
  · subst h0
    exact ExprLow.refines_base_of_refines i _ BusReg.gateEnv_dff BusReg.benv_dff Dff.dffImpl_refines
  · exact ExprLow.refines_base_of_eq i t (BusReg.gateEnv_find_ne t h0)

theorem WriteState.gateEnv_dff : WriteState.gateEnv.find? "dff" = .some ⟨_, Dff.dffImpl⟩ := rfl

theorem WriteState.gateEnv_find_ne (t : String) (h0 : t ≠ "dff") :
    WriteState.gateEnv.find? t = WriteState.senv.find? t := by
  have e0 : ("dff" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h0)
  simp [WriteState.gateEnv, AssocList.find?, e0]

theorem WriteState.wf_gateEnv : ExprLow.wf WriteState.gateEnv.find? WriteState.stLowered := by rfl
theorem WriteState.wf_senv : ExprLow.wf WriteState.senv.find? WriteState.stLowered := by rfl

seal WriteState.senv in
theorem WriteState.netlist_sigma :
    (⟨WriteState.stT, WriteState.stNetlist⟩ : Σ T, StringModule T) =
      ExprLow.build_module WriteState.senv.find? WriteState.stLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

/-- **The write domain's seven-bit state register, its flip-flops expanded to gates.** -/
theorem WriteState.gates_refines : WriteState.gates ⊑ WriteState.stSpec := by
  refine Module.refines_transitive _ ?_ WriteState.reg_refines
  refine Module.refines_transitive _ ?_ (Module.refines_eq' WriteState.netlist_sigma.symm)
  apply ExprLow.refines_env _ WriteState.wf_gateEnv WriteState.wf_senv
  intro i t
  by_cases h0 : t = "dff"
  · subst h0
    exact ExprLow.refines_base_of_refines i _ WriteState.gateEnv_dff WriteState.senv_dff Dff.dffImpl_refines
  · exact ExprLow.refines_base_of_eq i t (WriteState.gateEnv_find_ne t h0)

theorem ReadState.gateEnv_dff : ReadState.gateEnv.find? "dff" = .some ⟨_, Dff.dffImpl⟩ := rfl

theorem ReadState.gateEnv_find_ne (t : String) (h0 : t ≠ "dff") :
    ReadState.gateEnv.find? t = ReadState.senv.find? t := by
  have e0 : ("dff" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h0)
  simp [ReadState.gateEnv, AssocList.find?, e0]

theorem ReadState.wf_gateEnv : ExprLow.wf ReadState.gateEnv.find? ReadState.stLowered := by rfl
theorem ReadState.wf_senv : ExprLow.wf ReadState.senv.find? ReadState.stLowered := by rfl

seal ReadState.senv in
theorem ReadState.netlist_sigma :
    (⟨ReadState.stT, ReadState.stNetlist⟩ : Σ T, StringModule T) =
      ExprLow.build_module ReadState.senv.find? ReadState.stLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

/-- **The read domain's seven-bit state register, its flip-flops expanded to gates.** -/
theorem ReadState.gates_refines : ReadState.gates ⊑ ReadState.stSpec := by
  refine Module.refines_transitive _ ?_ ReadState.reg_refines
  refine Module.refines_transitive _ ?_ (Module.refines_eq' ReadState.netlist_sigma.symm)
  apply ExprLow.refines_env _ ReadState.wf_gateEnv ReadState.wf_senv
  intro i t
  by_cases h0 : t = "dff"
  · subst h0
    exact ExprLow.refines_base_of_refines i _ ReadState.gateEnv_dff ReadState.senv_dff Dff.dffImpl_refines
  · exact ExprLow.refines_base_of_eq i t (ReadState.gateEnv_find_ne t h0)

theorem EnReg.gateEnv_dff : EnReg.gateEnv.find? "dff" = .some ⟨_, Dff.dffImpl⟩ := rfl

theorem EnReg.gateEnv_find_ne (t : String) (h0 : t ≠ "dff") :
    EnReg.gateEnv.find? t = EnReg.eenv.find? t := by
  have e0 : ("dff" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h0)
  simp [EnReg.gateEnv, AssocList.find?, e0]

theorem EnReg.wf_gateEnv : ExprLow.wf EnReg.gateEnv.find? EnReg.enLowered := by rfl
theorem EnReg.wf_eenv : ExprLow.wf EnReg.eenv.find? EnReg.enLowered := by rfl

seal EnReg.eenv in
theorem EnReg.netlist_sigma :
    (⟨EnReg.enT, EnReg.enNetlist⟩ : Σ T, StringModule T) =
      ExprLow.build_module EnReg.eenv.find? EnReg.enLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

/-- **The memory cell, its flip-flop expanded to gates.** -/
theorem EnReg.gates_refines : EnReg.gates ⊑ EnReg.enSpec := by
  refine Module.refines_transitive _ ?_ EnReg.en_refines
  refine Module.refines_transitive _ ?_ (Module.refines_eq' EnReg.netlist_sigma.symm)
  apply ExprLow.refines_env _ EnReg.wf_gateEnv EnReg.wf_eenv
  intro i t
  by_cases h0 : t = "dff"
  · subst h0
    exact ExprLow.refines_base_of_refines i _ EnReg.gateEnv_dff EnReg.eenv_dff Dff.dffImpl_refines
  · exact ExprLow.refines_base_of_eq i t (EnReg.gateEnv_find_ne t h0)

theorem RegFile.gateEnv_cell : RegFile.gateEnv.find? "cell" = .some ⟨_, EnReg.gates⟩ := rfl

theorem RegFile.gateEnv_find_ne (t : String) (h0 : t ≠ "cell") :
    RegFile.gateEnv.find? t = RegFile.menv.find? t := by
  have e0 : ("cell" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h0)
  simp [RegFile.gateEnv, AssocList.find?, e0]

theorem RegFile.wf_gateEnv : ExprLow.wf RegFile.gateEnv.find? RegFile.memLowered := by rfl
theorem RegFile.wf_menv : ExprLow.wf RegFile.menv.find? RegFile.memLowered := by rfl

seal RegFile.menv in
theorem RegFile.netlist_sigma :
    (⟨RegFile.memT, RegFile.memNetlist⟩ : Σ T, StringModule T) =
      ExprLow.build_module RegFile.menv.find? RegFile.memLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

/-- **The four-entry register file, its cells expanded to gates.** -/
theorem RegFile.gates_refines : RegFile.gates ⊑ RegFile.memSpec := by
  refine Module.refines_transitive _ ?_ RegFile.mem_refines
  refine Module.refines_transitive _ ?_ (Module.refines_eq' RegFile.netlist_sigma.symm)
  apply ExprLow.refines_env _ RegFile.wf_gateEnv RegFile.wf_menv
  intro i t
  by_cases h0 : t = "cell"
  · subst h0
    exact ExprLow.refines_base_of_refines i _ RegFile.gateEnv_cell RegFile.menv_cell EnReg.gates_refines
  · exact ExprLow.refines_base_of_eq i t (RegFile.gateEnv_find_ne t h0)

theorem WriteBank.gateEnv_streg : WriteBank.gateEnv.find? "streg" = .some ⟨_, WriteState.gates⟩ := rfl
theorem WriteBank.gateEnv_busreg : WriteBank.gateEnv.find? "busreg" = .some ⟨_, BusReg.gates⟩ := rfl
theorem WriteBank.gateEnv_memory : WriteBank.gateEnv.find? "memory" = .some ⟨_, RegFile.gates⟩ := rfl

theorem WriteBank.gateEnv_find_ne (t : String) (h0 : t ≠ "streg") (h1 : t ≠ "busreg") (h2 : t ≠ "memory") :
    WriteBank.gateEnv.find? t = WriteBank.kenv.find? t := by
  have e0 : ("streg" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h0)
  have e1 : ("busreg" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h1)
  have e2 : ("memory" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h2)
  simp [WriteBank.gateEnv, AssocList.find?, e0, e1, e2]

theorem WriteBank.wf_gateEnv : ExprLow.wf WriteBank.gateEnv.find? WriteBank.bankLowered := by rfl
theorem WriteBank.wf_kenv : ExprLow.wf WriteBank.kenv.find? WriteBank.bankLowered := by rfl

seal WriteBank.kenv in
theorem WriteBank.netlist_sigma :
    (⟨WriteBank.bankT, WriteBank.bankNetlist⟩ : Σ T, StringModule T) =
      ExprLow.build_module WriteBank.kenv.find? WriteBank.bankLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

/-- ****the write domain's whole state as gates**: state register, Gray pointer and register file.** -/
theorem WriteBank.gates_refines_exact : WriteBank.gates ⊑ WriteBank.bankExact := by
  refine Module.refines_transitive _ ?_ WriteBank.bank_refines
  refine Module.refines_transitive _ ?_ (Module.refines_eq' WriteBank.netlist_sigma.symm)
  apply ExprLow.refines_env _ WriteBank.wf_gateEnv WriteBank.wf_kenv
  intro i t
  by_cases h0 : t = "streg"
  · subst h0
    exact ExprLow.refines_base_of_refines i _ WriteBank.gateEnv_streg WriteBank.kenv_streg WriteState.gates_refines
  by_cases h1 : t = "busreg"
  · subst h1
    exact ExprLow.refines_base_of_refines i _ WriteBank.gateEnv_busreg WriteBank.kenv_busreg BusReg.gates_refines
  by_cases h2 : t = "memory"
  · subst h2
    exact ExprLow.refines_base_of_refines i _ WriteBank.gateEnv_memory WriteBank.kenv_memory RegFile.gates_refines
  · exact ExprLow.refines_base_of_eq i t (WriteBank.gateEnv_find_ne t h0 h1 h2)

theorem ReadBank.gateEnv_streg : ReadBank.gateEnv.find? "streg" = .some ⟨_, ReadState.gates⟩ := rfl
theorem ReadBank.gateEnv_busreg : ReadBank.gateEnv.find? "busreg" = .some ⟨_, BusReg.gates⟩ := rfl

theorem ReadBank.gateEnv_find_ne (t : String) (h0 : t ≠ "streg") (h1 : t ≠ "busreg") :
    ReadBank.gateEnv.find? t = ReadBank.kenv.find? t := by
  have e0 : ("streg" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h0)
  have e1 : ("busreg" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h1)
  simp [ReadBank.gateEnv, AssocList.find?, e0, e1]

theorem ReadBank.wf_gateEnv : ExprLow.wf ReadBank.gateEnv.find? ReadBank.bankLowered := by rfl
theorem ReadBank.wf_kenv : ExprLow.wf ReadBank.kenv.find? ReadBank.bankLowered := by rfl

seal ReadBank.kenv in
theorem ReadBank.netlist_sigma :
    (⟨ReadBank.bankT, ReadBank.bankNetlist⟩ : Σ T, StringModule T) =
      ExprLow.build_module ReadBank.kenv.find? ReadBank.bankLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

/-- ****the read domain's whole state as gates**: state register and Gray pointer.** -/
theorem ReadBank.gates_refines_exact : ReadBank.gates ⊑ ReadBank.bankExact := by
  refine Module.refines_transitive _ ?_ ReadBank.bank_refines
  refine Module.refines_transitive _ ?_ (Module.refines_eq' ReadBank.netlist_sigma.symm)
  apply ExprLow.refines_env _ ReadBank.wf_gateEnv ReadBank.wf_kenv
  intro i t
  by_cases h0 : t = "streg"
  · subst h0
    exact ExprLow.refines_base_of_refines i _ ReadBank.gateEnv_streg ReadBank.kenv_streg ReadState.gates_refines
  by_cases h1 : t = "busreg"
  · subst h1
    exact ExprLow.refines_base_of_refines i _ ReadBank.gateEnv_busreg ReadBank.kenv_busreg BusReg.gates_refines
  · exact ExprLow.refines_base_of_eq i t (ReadBank.gateEnv_find_ne t h0 h1)
end Graphiti.AsyncFifo