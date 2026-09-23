/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadPort
import Graphiti.Projects.AsyncFifo.components.level4.ReadPort

/-!
# The read port as a block of the timed read domain

`ReadPort.lean` builds the port out of gates, proves its contract (`muxOut_readOut`) and records
what it has reported.  What is left is a direct refinement: `readMuxSpec` and `ReadPort.RDataSt`
hold the same three streams.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.ReadPortContract

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.ReadPort

instance : MatchInterface readMuxSpec (ReadPort.readSpec Bool (n := 2) 3 5) := by
  dsimp [readMuxSpec, ReadPort.readSpec]
  solve_match_interface

/-- The same three streams, read as the port's state. -/
def asRDataSt (i : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) : ReadPort.RDataSt Bool 2 :=
  ⟨i.1, i.2.1, i.2.2⟩

def psi (i : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (s : ReadPort.RDataSt Bool 2) : Prop :=
  s = asRDataSt i

theorem refines_psi : readMuxSpec ⊑_{psi} ReadPort.readSpec Bool (n := 2) 3 5 := by
  intro i s Hψ
  obtain ⟨st, mem, q⟩ := i
  dsimp only [psi, asRDataSt] at Hψ
  subst Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨st', mem', q'⟩ := mid_i
    case_transition Hcontains : Module.inputs readMuxSpec, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [readMuxSpec] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals refine ⟨_, _, ?_, existSR_reflexive, rfl⟩
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
    all_goals exact ⟨‹_›, rfl⟩
  · intro ident mid_i v Hrule
    obtain ⟨st', mem', q'⟩ := mid_i
    case_transition Hcontains : Module.outputs readMuxSpec, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [readMuxSpec] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    refine ⟨_, _, existSR_reflexive, ?_, rfl⟩
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
    exact ⟨‹_›, muxOut_readOut ‹_›, rfl⟩
  · intro rule mid_i Hin Hrule
    dsimp only [readMuxSpec] at Hin
    simp at Hin

theorem refines_initial :
    Module.refines_initial readMuxSpec (ReadPort.readSpec Bool (n := 2) 3 5) psi := by
  intro i hi
  obtain ⟨st, mem, q⟩ := i
  dsimp only [readMuxSpec] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl⟩ := hi
  exact ⟨⟨[], [], []⟩, rfl, rfl⟩

/-- **The read port as a block of the timed read domain.** -/
theorem readMuxSpec_refines : readMuxSpec ⊑ ReadPort.readSpec Bool (n := 2) 3 5 :=
  ⟨inferInstance, psi, refines_psi, refines_initial⟩

/-- **The gate-level read port is a block of the timed read domain**, with delay window
`[3, 5]`. -/
theorem netlist_refines : muxNetlist ⊑ ReadPort.readSpec Bool (n := 2) 3 5 :=
  Module.refines_transitive _ mux_refines readMuxSpec_refines


theorem readImpl_refines : ReadPort.readImpl ⊑ ReadPort.readSpec Bool (n := 2) 3 5 :=
  Module.refines_transitive _ (Module.refines_eq' ReadPort.muxNetlist_sigma.symm) netlist_refines

end Graphiti.AsyncFifo.ReadPortContract
