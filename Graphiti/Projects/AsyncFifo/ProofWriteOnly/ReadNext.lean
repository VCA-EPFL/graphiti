/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadNextLemmas
import Graphiti.Projects.AsyncFifo.components.level4.ReadNext

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Graphiti.AsyncFifo.ReadNext

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Gates Gray
open Batteries (AssocList)
variable {s s' : ReadNext.RNextSt 2}
variable (s : ReadNext.RNextSt 2)

/-! ### The netlist, as an index type

Each wire holds a prefix of what the specification computes for it.  This block is
combinational, so `drv` does not read the other wires at all -- it is the specification's own
`W_*`, wire by wire -- and a connection is then one monotonicity step, written on its own
line below. -/

open Graphiti.AsyncFifo.Netlist

/-- The 54 driven wires. -/
inductive W
  | nem_a
  | ok_a
  | ok_b
  | fok_in
  | fp0_in
  | fp1_in
  | xp0_a
  | xp0_b
  | cp0_a
  | cp0_b
  | fc0_in
  | xp1_a
  | xp1_b
  | cp1_a
  | cp1_b
  | xp2_a
  | xp2_b
  | fpa_in
  | fpb_in
  | fpc_in
  | xg0_a
  | xg0_b
  | xg1_a
  | xg1_b
  | fq2_in
  | xu1_a
  | xu1_b
  | fu1_in
  | xu0_a
  | xu0_b
  | xe2_a
  | xe2_b
  | xe1_a
  | xe1_b
  | xe0_a
  | xe0_b
  | ae_a
  | ae_b
  | am_a
  | am_b
  | pk_p0
  | pk_p1
  | pk_p2
  | pk_em
  | fq1_in
  | pk_q0
  | pk_q1
  | pk_q2
  | pk_g0
  | pk_g1
  | pk_g2
  | pk_r1
  | pk_r2
  | pk_r3
  deriving DecidableEq

/-- What each wire settles to: the specification's value for it.  One line per wire, and the
only place the shape of this netlist is written down. -/
def drv (s : ReadNext.RNextSt 2) : Drv W
  | _, .nem_a => W_unp_em s
  | _, .ok_a => s.inc
  | _, .ok_b => W_nem s
  | _, .fok_in => W_ok s
  | _, .fp0_in => W_unp_p0 s
  | _, .fp1_in => W_unp_p1 s
  | _, .xp0_a => W_unp_p0 s
  | _, .xp0_b => W_ok s
  | _, .cp0_a => W_unp_p0 s
  | _, .cp0_b => W_ok s
  | _, .fc0_in => W_cp0 s
  | _, .xp1_a => W_unp_p1 s
  | _, .xp1_b => W_cp0 s
  | _, .cp1_a => W_unp_p1 s
  | _, .cp1_b => W_cp0 s
  | _, .xp2_a => W_unp_p2 s
  | _, .xp2_b => W_cp1 s
  | _, .fpa_in => W_xp0 s
  | _, .fpb_in => W_xp1 s
  | _, .fpc_in => W_xp2 s
  | _, .xg0_a => W_xp1 s
  | _, .xg0_b => W_xp0 s
  | _, .xg1_a => W_xp2 s
  | _, .xg1_b => W_xp1 s
  | _, .fq2_in => W_unp_q22 s
  | _, .xu1_a => W_unp_q22 s
  | _, .xu1_b => W_unp_q21 s
  | _, .fu1_in => W_xu1 s
  | _, .xu0_a => W_xu1 s
  | _, .xu0_b => W_unp_q20 s
  | _, .xe2_a => W_xp2 s
  | _, .xe2_b => W_unp_q22 s
  | _, .xe1_a => W_xp1 s
  | _, .xe1_b => W_xu1 s
  | _, .xe0_a => W_xp0 s
  | _, .xe0_b => W_xu0 s
  | _, .ae_a => W_xe2 s
  | _, .ae_b => W_xe1 s
  | _, .am_a => W_ae s
  | _, .am_b => W_xe0 s
  | _, .pk_p0 => W_xp0 s
  | _, .pk_p1 => W_xp1 s
  | _, .pk_p2 => W_xp2 s
  | _, .pk_em => W_am s
  | _, .fq1_in => W_unp_q10 s
  | _, .pk_q0 => W_unp_q10 s
  | _, .pk_q1 => W_unp_q11 s
  | _, .pk_q2 => W_unp_q12 s
  | _, .pk_g0 => W_xg0 s
  | _, .pk_g1 => W_xg1 s
  | _, .pk_g2 => W_xp2 s
  | _, .pk_r1 => W_unp_p0 s
  | _, .pk_r2 => s.inc
  | _, .pk_r3 => W_unp_q10 s

theorem drv_mono {s} : Mono (drv s) := by
  intro a b _ k; cases k <;> exact List.prefix_rfl

/-- Growing the block's own inputs grows every value it computes.  `s` and `s'` are explicit:
they are only reachable through projections in the hypotheses, which unification cannot
invert, and left implicit the two collapse into one metavariable. -/
theorem drv_env (s : ReadNext.RNextSt 2) {st' : List (RSt 2)} {inc' : List Bool} {q1' : List (BitVec 3)} (hst : s.st <+: st') (hinc : s.inc <+: inc') (hq1 : s.q1 <+: q1') (w : Wires W) (k : W) :
    drv s w k <+: drv { s with st := st', inc := inc', q1 := q1' } w k := by
  cases k <;> simp only [drv]
  case nem_a => exact W_unp_em_mono hst hinc hq1
  case ok_a => exact hinc
  case ok_b => exact W_nem_mono hst hinc hq1
  case fok_in => exact W_ok_mono hst hinc hq1
  case fp0_in => exact W_unp_p0_mono hst hinc hq1
  case fp1_in => exact W_unp_p1_mono hst hinc hq1
  case xp0_a => exact W_unp_p0_mono hst hinc hq1
  case xp0_b => exact W_ok_mono hst hinc hq1
  case cp0_a => exact W_unp_p0_mono hst hinc hq1
  case cp0_b => exact W_ok_mono hst hinc hq1
  case fc0_in => exact W_cp0_mono hst hinc hq1
  case xp1_a => exact W_unp_p1_mono hst hinc hq1
  case xp1_b => exact W_cp0_mono hst hinc hq1
  case cp1_a => exact W_unp_p1_mono hst hinc hq1
  case cp1_b => exact W_cp0_mono hst hinc hq1
  case xp2_a => exact W_unp_p2_mono hst hinc hq1
  case xp2_b => exact W_cp1_mono hst hinc hq1
  case fpa_in => exact W_xp0_mono hst hinc hq1
  case fpb_in => exact W_xp1_mono hst hinc hq1
  case fpc_in => exact W_xp2_mono hst hinc hq1
  case xg0_a => exact W_xp1_mono hst hinc hq1
  case xg0_b => exact W_xp0_mono hst hinc hq1
  case xg1_a => exact W_xp2_mono hst hinc hq1
  case xg1_b => exact W_xp1_mono hst hinc hq1
  case fq2_in => exact W_unp_q22_mono hst hinc hq1
  case xu1_a => exact W_unp_q22_mono hst hinc hq1
  case xu1_b => exact W_unp_q21_mono hst hinc hq1
  case fu1_in => exact W_xu1_mono hst hinc hq1
  case xu0_a => exact W_xu1_mono hst hinc hq1
  case xu0_b => exact W_unp_q20_mono hst hinc hq1
  case xe2_a => exact W_xp2_mono hst hinc hq1
  case xe2_b => exact W_unp_q22_mono hst hinc hq1
  case xe1_a => exact W_xp1_mono hst hinc hq1
  case xe1_b => exact W_xu1_mono hst hinc hq1
  case xe0_a => exact W_xp0_mono hst hinc hq1
  case xe0_b => exact W_xu0_mono hst hinc hq1
  case ae_a => exact W_xe2_mono hst hinc hq1
  case ae_b => exact W_xe1_mono hst hinc hq1
  case am_a => exact W_ae_mono hst hinc hq1
  case am_b => exact W_xe0_mono hst hinc hq1
  case pk_p0 => exact W_xp0_mono hst hinc hq1
  case pk_p1 => exact W_xp1_mono hst hinc hq1
  case pk_p2 => exact W_xp2_mono hst hinc hq1
  case pk_em => exact W_am_mono hst hinc hq1
  case fq1_in => exact W_unp_q10_mono hst hinc hq1
  case pk_q0 => exact W_unp_q10_mono hst hinc hq1
  case pk_q1 => exact W_unp_q11_mono hst hinc hq1
  case pk_q2 => exact W_unp_q12_mono hst hinc hq1
  case pk_g0 => exact W_xg0_mono hst hinc hq1
  case pk_g1 => exact W_xg1_mono hst hinc hq1
  case pk_g2 => exact W_xp2_mono hst hinc hq1
  case pk_r1 => exact W_unp_p0_mono hst hinc hq1
  case pk_r2 => exact hinc
  case pk_r3 => exact W_unp_q10_mono hst hinc hq1

/-- The reduced state is a nested product ending in a `PackSt`; `wires` reads it as an
assignment. -/
def wires (i : gateNextRT) : Wires W
  | .nem_a => i.2.1
  | .ok_a => i.2.2.2.1.1
  | .ok_b => i.2.2.2.1.2
  | .fok_in => i.2.2.2.2.1
  | .fp0_in => i.2.2.2.2.2.1
  | .fp1_in => i.2.2.2.2.2.2.1
  | .xp0_a => i.2.2.2.2.2.2.2.2.1.1
  | .xp0_b => i.2.2.2.2.2.2.2.2.1.2
  | .cp0_a => i.2.2.2.2.2.2.2.2.2.1.1
  | .cp0_b => i.2.2.2.2.2.2.2.2.2.1.2
  | .fc0_in => i.2.2.2.2.2.2.2.2.2.2.1
  | .xp1_a => i.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xp1_b => i.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .cp1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .cp1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xp2_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xp2_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .fpa_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .fpb_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .fpc_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .xg0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xg0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xg1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xg1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .fq2_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .xu1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xu1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .fu1_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .xu0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xu0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xe2_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xe2_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xe1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xe1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .xe0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .xe0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .ae_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .ae_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .am_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .am_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .pk_p0 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.p0
  | .pk_p1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.p1
  | .pk_p2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.p2
  | .pk_em => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.em
  | .fq1_in => i.2.2.2.2.2.2.2.1
  | .pk_q0 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.q0
  | .pk_q1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.q1
  | .pk_q2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.q2
  | .pk_g0 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.g0
  | .pk_g1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.g1
  | .pk_g2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.g2
  | .pk_r1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.r1
  | .pk_r2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.r2
  | .pk_r3 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.r3

/-- The invariant: the wires are well formed, the inputs the netlist holds are the
specification's, and the packer has reported no more than the wires behind it hold. -/
def ψ (i : gateNextRT) (s : ReadNext.RNextSt 2) : Prop :=
  Wf (drv s) (wires i)
    ∧ i.1.1 = s.st
    ∧ i.1.2 = s.q1
    ∧ i.2.2.1 = s.inc
    ∧ s.d <+: packROut ⟨(wires i .pk_p0), (wires i .pk_p1), (wires i .pk_p2), (wires i .pk_em), (wires i .pk_q0), (wires i .pk_q1), (wires i .pk_q2), (wires i .pk_g0), (wires i .pk_g1), (wires i .pk_g2), (wires i .pk_r1), (wires i .pk_r2), (wires i .pk_r3)⟩

/-- What the block reports meets the specification's combinational contract. -/
theorem out_comb {s : ReadNext.RNextSt 2} {w : Wires W} (hw : Wf (drv s) w) :
    CombOut (ReadNext.rnextDep s) (ReadNext.rnextFun) (ReadNext.rnextLen s) 0 8 (packROut ⟨(w .pk_p0), (w .pk_p1), (w .pk_p2), (w .pk_em), (w .pk_q0), (w .pk_q1), (w .pk_q2), (w .pk_g0), (w .pk_g1), (w .pk_g2), (w .pk_r1), (w .pk_r2), (w .pk_r3)⟩) :=
  CombOut.of_prefix (packROut_mono' (hw .pk_p0) (hw .pk_p1) (hw .pk_p2) (hw .pk_em) (hw .pk_q0) (hw .pk_q1) (hw .pk_q2) (hw .pk_g0) (hw .pk_g1) (hw .pk_g2) (hw .pk_r1) (hw .pk_r2) (hw .pk_r3)) (W_pack_comb s)

/-! ### One tactic for every connection -/

/-- Each of the packer's inputs either stands or advances; one `⊏` is in scope. -/
syntax "gn_pre" : tactic
/-- Every wire of `mid` is the wire of `i`: what an input rule changes is an input. -/
syntax "gn_same" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| gn_pre) => `(tactic| first | exact List.prefix_rfl | exact (‹_ ⊏ _›).isPrefix)
  | `(tactic| gn_same) =>
      `(tactic| (intro j; cases j <;> dsimp only [wires] <;> exact List.prefix_rfl))

/-- `gn_case t` proves one connection: `t` is the monotonicity step that says the value now on
the wire is still a prefix of what the specification computes for it. -/
syntax "gn_case " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| gn_case $t:term) => `(tactic| (
      obtain ⟨⟨unp_st, unp_q1⟩, nem_a, finc_in, ⟨ok_a, ok_b⟩, fok_in, fp0_in, fp1_in, fq1_in, ⟨xp0_a, xp0_b⟩, ⟨cp0_a, cp0_b⟩, fc0_in, ⟨xp1_a, xp1_b⟩, ⟨cp1_a, cp1_b⟩, ⟨xp2_a, xp2_b⟩, fpa_in, fpb_in, fpc_in, ⟨xg0_a, xg0_b⟩, ⟨xg1_a, xg1_b⟩, fq2_in, ⟨xu1_a, xu1_b⟩, fu1_in, ⟨xu0_a, xu0_b⟩, ⟨xe2_a, xe2_b⟩, ⟨xe1_a, xe1_b⟩, ⟨xe0_a, xe0_b⟩, ⟨ae_a, ae_b⟩, ⟨am_a, am_b⟩, ⟨pk_p0, pk_p1, pk_p2, pk_em, pk_q0, pk_q1, pk_q2, pk_g0, pk_g1, pk_g2, pk_r1, pk_r2, pk_r3⟩⟩ := i
      obtain ⟨⟨_, _⟩, _, _, ⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _⟩, _, _, ⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e0, e1, e2, hd⟩ := H
      try dsimp only [] at e0
      try dsimp only [] at e1
      try dsimp only [] at e2
      refine ⟨s, existSR_reflexive, Wf_step_of hw drv_mono ?_ ?_,
        e0, e1, e2, ?_⟩
      · intro j
        cases j <;> dsimp only [wires] <;> gn_pre
      · intro j
        have hj := hw j
        cases j <;> (try dsimp only [wires, drv] at hj) <;> dsimp only [wires, drv] <;>
          first | exact hj | exact $t
      · dsimp only [wires] at hd ⊢
        exact hd.trans (packROut_mono' (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre) (by gn_pre))))

theorem gateNextR_internals_eq : gateNextR.internals =
    [gateNextR.internals.getD 0 (fun _ _ => False), gateNextR.internals.getD 1 (fun _ _ => False), gateNextR.internals.getD 2 (fun _ _ => False),
     gateNextR.internals.getD 3 (fun _ _ => False), gateNextR.internals.getD 4 (fun _ _ => False), gateNextR.internals.getD 5 (fun _ _ => False),
     gateNextR.internals.getD 6 (fun _ _ => False), gateNextR.internals.getD 7 (fun _ _ => False), gateNextR.internals.getD 8 (fun _ _ => False),
     gateNextR.internals.getD 9 (fun _ _ => False), gateNextR.internals.getD 10 (fun _ _ => False), gateNextR.internals.getD 11 (fun _ _ => False),
     gateNextR.internals.getD 12 (fun _ _ => False), gateNextR.internals.getD 13 (fun _ _ => False), gateNextR.internals.getD 14 (fun _ _ => False),
     gateNextR.internals.getD 15 (fun _ _ => False), gateNextR.internals.getD 16 (fun _ _ => False), gateNextR.internals.getD 17 (fun _ _ => False),
     gateNextR.internals.getD 18 (fun _ _ => False), gateNextR.internals.getD 19 (fun _ _ => False), gateNextR.internals.getD 20 (fun _ _ => False),
     gateNextR.internals.getD 21 (fun _ _ => False), gateNextR.internals.getD 22 (fun _ _ => False), gateNextR.internals.getD 23 (fun _ _ => False),
     gateNextR.internals.getD 24 (fun _ _ => False), gateNextR.internals.getD 25 (fun _ _ => False), gateNextR.internals.getD 26 (fun _ _ => False),
     gateNextR.internals.getD 27 (fun _ _ => False), gateNextR.internals.getD 28 (fun _ _ => False), gateNextR.internals.getD 29 (fun _ _ => False),
     gateNextR.internals.getD 30 (fun _ _ => False), gateNextR.internals.getD 31 (fun _ _ => False), gateNextR.internals.getD 32 (fun _ _ => False),
     gateNextR.internals.getD 33 (fun _ _ => False), gateNextR.internals.getD 34 (fun _ _ => False), gateNextR.internals.getD 35 (fun _ _ => False),
     gateNextR.internals.getD 36 (fun _ _ => False), gateNextR.internals.getD 37 (fun _ _ => False), gateNextR.internals.getD 38 (fun _ _ => False),
     gateNextR.internals.getD 39 (fun _ _ => False), gateNextR.internals.getD 40 (fun _ _ => False), gateNextR.internals.getD 41 (fun _ _ => False),
     gateNextR.internals.getD 42 (fun _ _ => False), gateNextR.internals.getD 43 (fun _ _ => False), gateNextR.internals.getD 44 (fun _ _ => False),
     gateNextR.internals.getD 45 (fun _ _ => False), gateNextR.internals.getD 46 (fun _ _ => False), gateNextR.internals.getD 47 (fun _ _ => False),
     gateNextR.internals.getD 48 (fun _ _ => False), gateNextR.internals.getD 49 (fun _ _ => False), gateNextR.internals.getD 50 (fun _ _ => False),
     gateNextR.internals.getD 51 (fun _ _ => False), gateNextR.internals.getD 52 (fun _ _ => False), gateNextR.internals.getD 53 (fun _ _ => False)] := rfl

/-! All 54 connections, one line each: the wire, and why its new value is still
a prefix of what the specification computes. -/

theorem case_0 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- nem_a

theorem case_1 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (e2 ▸ List.prefix_rfl)   -- ok_a

theorem case_2 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gate1Out_mono _ (hw .nem_a)   -- ok_b

theorem case_3 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .ok_a) (hw .ok_b)   -- fok_in

theorem case_4 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- fp0_in

theorem case_5 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- fp1_in

theorem case_6 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp0_in)   -- xp0_a

theorem case_7 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fok_in)   -- xp0_b

theorem case_8 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp0_in)   -- cp0_a

theorem case_9 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fok_in)   -- cp0_b

theorem case_10 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .cp0_a) (hw .cp0_b)   -- fc0_in

theorem case_11 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp1_in)   -- xp1_a

theorem case_12 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fc0_in)   -- xp1_b

theorem case_13 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp1_in)   -- cp1_a

theorem case_14 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fc0_in)   -- cp1_b

theorem case_15 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- xp2_a

theorem case_16 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .cp1_a) (hw .cp1_b)   -- xp2_b

theorem case_17 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xp0_a) (hw .xp0_b)   -- fpa_in

theorem case_18 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xp1_a) (hw .xp1_b)   -- fpb_in

theorem case_19 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xp2_a) (hw .xp2_b)   -- fpc_in

theorem case_20 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpb_in)   -- xg0_a

theorem case_21 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpa_in)   -- xg0_b

theorem case_22 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpc_in)   -- xg1_a

theorem case_23 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpb_in)   -- xg1_b

theorem case_24 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- fq2_in

theorem case_25 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fq2_in)   -- xu1_a

theorem case_26 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- xu1_b

theorem case_27 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xu1_a) (hw .xu1_b)   -- fu1_in

theorem case_28 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 28 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fu1_in)   -- xu0_a

theorem case_29 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 29 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e0]; exact List.prefix_rfl)   -- xu0_b

theorem case_30 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 30 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpc_in)   -- xe2_a

theorem case_31 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 31 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fq2_in)   -- xe2_b

theorem case_32 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 32 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpb_in)   -- xe1_a

theorem case_33 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 33 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fu1_in)   -- xe1_b

theorem case_34 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 34 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpa_in)   -- xe0_a

theorem case_35 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 35 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xu0_a) (hw .xu0_b)   -- xe0_b

theorem case_36 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 36 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xe2_a) (hw .xe2_b)   -- ae_a

theorem case_37 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 37 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xe1_a) (hw .xe1_b)   -- ae_b

theorem case_38 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 38 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .ae_a) (hw .ae_b)   -- am_a

theorem case_39 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 39 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xe0_a) (hw .xe0_b)   -- am_b

theorem case_40 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 40 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpa_in)   -- pk_p0

theorem case_41 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 41 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpb_in)   -- pk_p1

theorem case_42 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 42 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpc_in)   -- pk_p2

theorem case_43 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 43 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .am_a) (hw .am_b)   -- pk_em

theorem case_44 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 44 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e1]; exact List.prefix_rfl)   -- fq1_in

theorem case_45 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 45 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fq1_in)   -- pk_q0

theorem case_46 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 46 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e1]; exact List.prefix_rfl)   -- pk_q1

theorem case_47 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 47 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (by rw [e1]; exact List.prefix_rfl)   -- pk_q2

theorem case_48 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 48 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xg0_a) (hw .xg0_b)   -- pk_g0

theorem case_49 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 49 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case gateOut_mono _ (hw .xg1_a) (hw .xg1_b)   -- pk_g1

theorem case_50 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 50 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fpc_in)   -- pk_g2

theorem case_51 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 51 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fp0_in)   -- pk_r1

theorem case_52 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 52 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (e2 ▸ List.prefix_rfl)   -- pk_r2

theorem case_53 (s) (i mid : gateNextRT) (H : ψ i s)
    (Hrule : (gateNextR.internals.getD 53 (fun _ _ => False)) i mid) :
    ∃ s', existSR (ReadNext.nextSpec (n := 2) 0 8).internals s s' ∧ ψ mid s' := by
  gn_case (hw .fq1_in)   -- pk_r3

/-! ### The specification's own rules -/

section SpecRules
variable (sp : ReadNext.RNextSt 2)
theorem spec_in_st (v : List (RSt 2)) (h : sp.st ⊏ v) :
    ((ReadNext.nextSpec (n := 2) 0 8).inputs.getIO ↑"st").2 sp v { sp with st := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_inc (v : List Bool) (h : sp.inc ⊏ v) :
    ((ReadNext.nextSpec (n := 2) 0 8).inputs.getIO ↑"inc").2 sp v { sp with inc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_q1 (v : List (BitVec 3)) (h : sp.q1 ⊏ v) :
    ((ReadNext.nextSpec (n := 2) 0 8).inputs.getIO ↑"q1").2 sp v { sp with q1 := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_out_d (v : List (RNext 2)) (h1 : sp.d <+: v)
    (h2 : CombOut (ReadNext.rnextDep sp) (ReadNext.rnextFun) (ReadNext.rnextLen sp) 0 8 v) :
    ((ReadNext.nextSpec (n := 2) 0 8).outputs.getIO ↑"d").2 sp v { sp with d := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : gateNextR ⊑_{ψ} (ReadNext.nextSpec (n := 2) 0 8) := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨unp_st, unp_q1⟩, nem_a, finc_in, ⟨ok_a, ok_b⟩, fok_in, fp0_in, fp1_in, fq1_in, ⟨xp0_a, xp0_b⟩, ⟨cp0_a, cp0_b⟩, fc0_in, ⟨xp1_a, xp1_b⟩, ⟨cp1_a, cp1_b⟩, ⟨xp2_a, xp2_b⟩, fpa_in, fpb_in, fpc_in, ⟨xg0_a, xg0_b⟩, ⟨xg1_a, xg1_b⟩, fq2_in, ⟨xu1_a, xu1_b⟩, fu1_in, ⟨xu0_a, xu0_b⟩, ⟨xe2_a, xe2_b⟩, ⟨xe1_a, xe1_b⟩, ⟨xe0_a, xe0_b⟩, ⟨ae_a, ae_b⟩, ⟨am_a, am_b⟩, ⟨pk_p0, pk_p1, pk_p2, pk_em, pk_q0, pk_q1, pk_q2, pk_g0, pk_g1, pk_g2, pk_r1, pk_r2, pk_r3⟩⟩ := i
    obtain ⟨⟨_, _⟩, _, _, ⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, hd⟩ := H
    try dsimp only [] at e0
    try dsimp only [] at e1
    try dsimp only [] at e2
    case_transition Hcontains : Module.inputs gateNextR, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [gateNextR] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    all_goals dsimp only [wires] at hd
    -- Both pieces are carried across pointwise; see `NetlistWf.lean` for why.
    all_goals first
      | (refine ⟨_, _, spec_in_st s _ (by rw [← e0]; exact hpre), existSR_reflexive,
             ?wf, rfl, e1, e2, ?hist⟩
         case wf =>
           exact Wf_congr drv_mono (Wf_drv hw (drv_env s (by rw [← e0]; exact hpre.isPrefix) List.prefix_rfl List.prefix_rfl _))
             (by gn_same) (by gn_same)
         case hist => exact hd.trans (packROut_mono' List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl))
      | (refine ⟨_, _, spec_in_q1 s _ (by rw [← e1]; exact hpre), existSR_reflexive,
             ?wf, e0, rfl, e2, ?hist⟩
         case wf =>
           exact Wf_congr drv_mono (Wf_drv hw (drv_env s List.prefix_rfl List.prefix_rfl (by rw [← e1]; exact hpre.isPrefix) _))
             (by gn_same) (by gn_same)
         case hist => exact hd.trans (packROut_mono' List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl))
      | (refine ⟨_, _, spec_in_inc s _ (by rw [← e2]; exact hpre), existSR_reflexive,
             ?wf, e0, e1, rfl, ?hist⟩
         case wf =>
           exact Wf_congr drv_mono (Wf_drv hw (drv_env s List.prefix_rfl (by rw [← e2]; exact hpre.isPrefix) List.prefix_rfl _))
             (by gn_same) (by gn_same)
         case hist => exact hd.trans (packROut_mono' List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl))
  · intro ident mid_i v Hrule
    obtain ⟨⟨unp_st, unp_q1⟩, nem_a, finc_in, ⟨ok_a, ok_b⟩, fok_in, fp0_in, fp1_in, fq1_in, ⟨xp0_a, xp0_b⟩, ⟨cp0_a, cp0_b⟩, fc0_in, ⟨xp1_a, xp1_b⟩, ⟨cp1_a, cp1_b⟩, ⟨xp2_a, xp2_b⟩, fpa_in, fpb_in, fpc_in, ⟨xg0_a, xg0_b⟩, ⟨xg1_a, xg1_b⟩, fq2_in, ⟨xu1_a, xu1_b⟩, fu1_in, ⟨xu0_a, xu0_b⟩, ⟨xe2_a, xe2_b⟩, ⟨xe1_a, xe1_b⟩, ⟨xe0_a, xe0_b⟩, ⟨ae_a, ae_b⟩, ⟨am_a, am_b⟩, ⟨pk_p0, pk_p1, pk_p2, pk_em, pk_q0, pk_q1, pk_q2, pk_g0, pk_g1, pk_g2, pk_r1, pk_r2, pk_r3⟩⟩ := i
    obtain ⟨⟨_, _⟩, _, _, ⟨_, _⟩, _, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, hd⟩ := H
    try dsimp only [] at e0
    try dsimp only [] at e1
    try dsimp only [] at e2
    have ho := out_comb hw
    dsimp only [wires] at ho hd
    case_transition Hcontains : Module.outputs gateNextR, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [gateNextR] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    exact ⟨s, _, existSR_reflexive, spec_out_d s _ hd ho,
      hw, e0, e1, e2, List.prefix_rfl⟩
  · intro rule mid_i Hin Hrule
    rw [gateNextR_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact case_0 s i mid_i H Hrule
    · subst h; exact case_1 s i mid_i H Hrule
    · subst h; exact case_2 s i mid_i H Hrule
    · subst h; exact case_3 s i mid_i H Hrule
    · subst h; exact case_4 s i mid_i H Hrule
    · subst h; exact case_5 s i mid_i H Hrule
    · subst h; exact case_6 s i mid_i H Hrule
    · subst h; exact case_7 s i mid_i H Hrule
    · subst h; exact case_8 s i mid_i H Hrule
    · subst h; exact case_9 s i mid_i H Hrule
    · subst h; exact case_10 s i mid_i H Hrule
    · subst h; exact case_11 s i mid_i H Hrule
    · subst h; exact case_12 s i mid_i H Hrule
    · subst h; exact case_13 s i mid_i H Hrule
    · subst h; exact case_14 s i mid_i H Hrule
    · subst h; exact case_15 s i mid_i H Hrule
    · subst h; exact case_16 s i mid_i H Hrule
    · subst h; exact case_17 s i mid_i H Hrule
    · subst h; exact case_18 s i mid_i H Hrule
    · subst h; exact case_19 s i mid_i H Hrule
    · subst h; exact case_20 s i mid_i H Hrule
    · subst h; exact case_21 s i mid_i H Hrule
    · subst h; exact case_22 s i mid_i H Hrule
    · subst h; exact case_23 s i mid_i H Hrule
    · subst h; exact case_24 s i mid_i H Hrule
    · subst h; exact case_25 s i mid_i H Hrule
    · subst h; exact case_26 s i mid_i H Hrule
    · subst h; exact case_27 s i mid_i H Hrule
    · subst h; exact case_28 s i mid_i H Hrule
    · subst h; exact case_29 s i mid_i H Hrule
    · subst h; exact case_30 s i mid_i H Hrule
    · subst h; exact case_31 s i mid_i H Hrule
    · subst h; exact case_32 s i mid_i H Hrule
    · subst h; exact case_33 s i mid_i H Hrule
    · subst h; exact case_34 s i mid_i H Hrule
    · subst h; exact case_35 s i mid_i H Hrule
    · subst h; exact case_36 s i mid_i H Hrule
    · subst h; exact case_37 s i mid_i H Hrule
    · subst h; exact case_38 s i mid_i H Hrule
    · subst h; exact case_39 s i mid_i H Hrule
    · subst h; exact case_40 s i mid_i H Hrule
    · subst h; exact case_41 s i mid_i H Hrule
    · subst h; exact case_42 s i mid_i H Hrule
    · subst h; exact case_43 s i mid_i H Hrule
    · subst h; exact case_44 s i mid_i H Hrule
    · subst h; exact case_45 s i mid_i H Hrule
    · subst h; exact case_46 s i mid_i H Hrule
    · subst h; exact case_47 s i mid_i H Hrule
    · subst h; exact case_48 s i mid_i H Hrule
    · subst h; exact case_49 s i mid_i H Hrule
    · subst h; exact case_50 s i mid_i H Hrule
    · subst h; exact case_51 s i mid_i H Hrule
    · subst h; exact case_52 s i mid_i H Hrule
    · subst h; exact case_53 s i mid_i H Hrule

theorem refines_initial : Module.refines_initial gateNextR (ReadNext.nextSpec (n := 2) 0 8) ψ := by
  intro i hi
  obtain ⟨⟨unp_st, unp_q1⟩, nem_a, finc_in, ⟨ok_a, ok_b⟩, fok_in, fp0_in, fp1_in, fq1_in, ⟨xp0_a, xp0_b⟩, ⟨cp0_a, cp0_b⟩, fc0_in, ⟨xp1_a, xp1_b⟩, ⟨cp1_a, cp1_b⟩, ⟨xp2_a, xp2_b⟩, fpa_in, fpb_in, fpc_in, ⟨xg0_a, xg0_b⟩, ⟨xg1_a, xg1_b⟩, fq2_in, ⟨xu1_a, xu1_b⟩, fu1_in, ⟨xu0_a, xu0_b⟩, ⟨xe2_a, xe2_b⟩, ⟨xe1_a, xe1_b⟩, ⟨xe0_a, xe0_b⟩, ⟨ae_a, ae_b⟩, ⟨am_a, am_b⟩, ⟨pk_p0, pk_p1, pk_p2, pk_em, pk_q0, pk_q1, pk_q2, pk_g0, pk_g1, pk_g2, pk_r1, pk_r2, pk_r3⟩⟩ := i
  dsimp only [gateNextR] at hi
  simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The gates refine the next-state block.** -/
theorem gateNextR_refines : gateNextR ⊑ (ReadNext.nextSpec (n := 2) 0 8) :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩


theorem nextImpl_refines : nextImpl ⊑ (ReadNext.nextSpec (n := 2) 0 8) :=
  Module.refines_transitive _ (Module.refines_eq' gateNextR_sigma.symm) gateNextR_refines

end Graphiti.AsyncFifo.ReadNext
