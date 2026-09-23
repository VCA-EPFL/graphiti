/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteBank
import Graphiti.Projects.AsyncFifo.components.level6.WriteBank

/-!
# The register bank as a block of the timed write domain

`WriteBank.lean` builds the bank out of gates, proves its contracts (`bank_stG` and friends), and
records what each of its four ports has reported --- the registers and the register file keep
that record themselves, the two ports that leave through an adapter have it kept for them.  So
the bank's reports only grow, which is what `WriteBank.bankSpec` asks and what the circuit does:
wires only grow, and it is the *abstraction* that forgets, since a block can only claim a
prefix of what it computes.

What is left for this file is the contracts, and it is a direct refinement: `bankExact` and
`WriteBank.RegSt` hold the same seven streams. -/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.WriteBankContract

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.WriteBank

/-- The seven streams a bank holds: its three inputs and its four reports. -/
abbrev BSt : Type :=
  List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) ×
    List (BitVec 2 → Bool)

section Block
variable {Rc : Nat}

/-- A prefix of a mapped list is the map of a prefix. -/
theorem prefix_map_exists {α β : Type} {f : α → β} {l : List α} {v : List β} (h : v <+: l.map f) :
    ∃ p, p <+: l ∧ v = p.map f := by
  refine ⟨l.take v.length, List.take_prefix _ _, ?_⟩
  rw [List.map_take, ← List.prefix_iff_eq_take.mp h]

instance : MatchInterface bankExact (WriteBank.bankSpec Bool (n := 2) 4 8 12 3 (Rc + 3) Rc) := by
  dsimp [bankExact, WriteBank.bankSpec]
  solve_match_interface

/-- The same seven streams, read as the bank's state. -/
def asRegSt (i : BSt) : WriteBank.RegSt Bool 2 :=
  ⟨i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2.1, i.2.2.2.2.2.1, i.2.2.2.2.2.2⟩

def psi (i : BSt) (s : WriteBank.RegSt Bool 2) : Prop := s = asRegSt i

theorem refines_psi (hR : 6 ≤ Rc) :
    bankExact ⊑_{psi} WriteBank.bankSpec Bool (n := 2) 4 8 12 3 (Rc + 3) Rc := by
  intro i s Hψ
  obtain ⟨clk, d, crn, stq, fq, gq, mq⟩ := i
  dsimp only [psi, asRegSt] at Hψ
  subst Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨clk', d', crn', stq', fq', gq', mq'⟩ := mid_i
    case_transition Hcontains : Module.inputs bankExact, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankExact] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals refine ⟨_, _, ?_, existSR_reflexive, rfl⟩
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
    all_goals exact ⟨‹_›, rfl⟩
  · intro ident mid_i v Hrule
    obtain ⟨clk', d', crn', stq', fq', gq', mq'⟩ := mid_i
    case_transition Hcontains : Module.outputs bankExact, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankExact] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · -- st
      refine ⟨_, _, existSR_reflexive, ?_, rfl⟩
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
      exact ⟨‹_›, (bank_stG hR ‹_›).weaken_su (by omega), rfl⟩
    · -- full
      refine ⟨_, _, existSR_reflexive, ?_, rfl⟩
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
      obtain ⟨p, hp, he⟩ := prefix_map_exists ‹_›
      exact ⟨‹_›, ⟨p, (bank_stG hR hp).weaken_su (by omega), he⟩, rfl⟩
    · -- gray
      refine ⟨_, _, existSR_reflexive, ?_, rfl⟩
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
      exact ⟨‹_›, (bank_grayG hR ‹_›).weaken_su (by omega), rfl⟩
    · -- mem
      refine ⟨_, _, existSR_reflexive, ?_, rfl⟩
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
      exact ⟨‹_›, bank_memG hR ‹_›, rfl⟩
  · intro rule mid_i Hin Hrule
    dsimp only [bankExact] at Hin
    simp at Hin

theorem refines_initial :
    Module.refines_initial bankExact (WriteBank.bankSpec Bool (n := 2) 4 8 12 3 (Rc + 3) Rc) psi := by
  intro i hi
  obtain ⟨clk, d, crn, stq, fq, gq, mq⟩ := i
  dsimp only [bankExact] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨⟨[], [], [], [], [], [], []⟩, rfl, rfl⟩

/-- **The bank as a block of the timed write domain.** -/
theorem bankSpec_refines (hR : 6 ≤ Rc) :
    bankExact ⊑ WriteBank.bankSpec Bool (n := 2) 4 8 12 3 (Rc + 3) Rc :=
  ⟨inferInstance, psi, refines_psi hR, refines_initial⟩

/-- **The gate-level register bank is a block of the timed write domain.** -/
theorem netlist_refines (hR : 6 ≤ Rc) :
    bankNetlist ⊑ WriteBank.bankSpec Bool (n := 2) 4 8 12 3 (Rc + 3) Rc :=
  Module.refines_transitive _ bank_refines (bankSpec_refines hR)

end Block

end Graphiti.AsyncFifo.WriteBankContract
