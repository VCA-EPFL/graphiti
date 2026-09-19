/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.BankR

/-!
# The read domain's register bank as a block of the timed read domain

`BankR.lean` builds the bank out of gates, proves its contracts (`bank_stG` and friends), and
records what each of its three ports has reported --- the two registers keep that record
themselves, the two ports that leave through an adapter have it kept for them.  So the bank's
reports only grow, which is what `Timed.rregBank` asks and what the circuit does: wires only
grow, and it is the *abstraction* that forgets, since a block can only claim a prefix of what
it computes.

What is left for this file is the contracts, and it is a direct refinement: `bankSpec` and
`RRegSt` hold the same six streams.  This is `GateBank.lean` without the register file. -/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.GateBankR

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.BankR

/-- The six streams the read bank holds: its three inputs and its three reports. -/
abbrev BSt : Type :=
  List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)

section Block
variable {Rc : Nat}

/-- A prefix of a mapped list is the map of a prefix. -/
theorem prefix_map_exists {α β : Type} {f : α → β} {l : List α} {v : List β} (h : v <+: l.map f) :
    ∃ p, p <+: l ∧ v = p.map f := by
  refine ⟨l.take v.length, List.take_prefix _ _, ?_⟩
  rw [List.map_take, ← List.prefix_iff_eq_take.mp h]

instance : MatchInterface bankSpec (rregBank (n := 2) 4 8 12 3 (Rc + 3) Rc) := by
  dsimp [bankSpec, rregBank]
  solve_match_interface

/-- The same six streams, read as the bank's state. -/
def asRegSt (i : BSt) : RRegSt 2 :=
  ⟨i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2.1, i.2.2.2.2.2⟩

def psi (i : BSt) (s : RRegSt 2) : Prop := s = asRegSt i

theorem refines_psi (hR : 6 ≤ Rc) :
    bankSpec ⊑_{psi} rregBank (n := 2) 4 8 12 3 (Rc + 3) Rc := by
  intro i s Hψ
  obtain ⟨clk, d, crn, stq, eq_, gq⟩ := i
  dsimp only [psi, asRegSt] at Hψ
  subst Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨clk', d', crn', stq', eq', gq'⟩ := mid_i
    case_transition Hcontains : Module.inputs bankSpec, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankSpec] at Hcontains
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
    obtain ⟨clk', d', crn', stq', eq', gq'⟩ := mid_i
    case_transition Hcontains : Module.outputs bankSpec, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankSpec] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · -- st
      refine ⟨_, _, existSR_reflexive, ?_, rfl⟩
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
      exact ⟨‹_›, (bank_stG hR ‹_›).weaken_su (by omega), rfl⟩
    · -- empty
      refine ⟨_, _, existSR_reflexive, ?_, rfl⟩
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
      obtain ⟨p, hp, he⟩ := prefix_map_exists ‹_›
      exact ⟨‹_›, ⟨p, (bank_stG hR hp).weaken_su (by omega), he⟩, rfl⟩
    · -- gray
      refine ⟨_, _, existSR_reflexive, ?_, rfl⟩
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
      exact ⟨‹_›, (bank_grayG hR ‹_›).weaken_su (by omega), rfl⟩
  · intro rule mid_i Hin Hrule
    dsimp only [bankSpec] at Hin
    simp at Hin

theorem refines_initial :
    Module.refines_initial bankSpec (rregBank (n := 2) 4 8 12 3 (Rc + 3) Rc) psi := by
  intro i hi
  obtain ⟨clk, d, crn, stq, eq_, gq⟩ := i
  dsimp only [bankSpec] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨⟨[], [], [], [], [], []⟩, rfl, rfl⟩

/-- **The bank as a block of the timed read domain.** -/
theorem bankSpec_refines (hR : 6 ≤ Rc) :
    bankSpec ⊑ rregBank (n := 2) 4 8 12 3 (Rc + 3) Rc :=
  ⟨inferInstance, psi, refines_psi hR, refines_initial⟩

/-- **The gate-level register bank is a block of the timed read domain.** -/
theorem bank_refines_rregBank (hR : 6 ≤ Rc) :
    bankNetlist ⊑ rregBank (n := 2) 4 8 12 3 (Rc + 3) Rc :=
  Module.refines_transitive _ bank_refines (bankSpec_refines hR)

end Block

end Graphiti.AsyncFifo.GateBankR
