/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Timed
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadPortLemmas

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.ReadPort

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Over an index rather than a record with one
field per wire, the per-rule lemmas collapse into `Netlist.Wf_set` and `Netlist.Wf_drv`, so
what is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The 31 driven wires. -/
inductive W
  | o23_a
  | o23_b
  | outg_a
  | outg_b
  | s0_a
  | s0_b
  | s2_a
  | s2_b
  | s3_a
  | s3_b
  | fn1_in
  | na1_a
  | g1_a
  | g1_b
  | fn0_in
  | fa0_in
  | g2_a
  | g2_b
  | na0_a
  | fa1_in
  | o01_a
  | o01_b
  | g3_a
  | g3_b
  | cut_in
  | cut_r1
  | cut_r2
  | g0_a
  | g0_b
  | s1_a
  | s1_b
  deriving DecidableEq

/-- What drives each wire: one line per wire, and the only place the shape of this netlist
is written down. -/
def drv (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : Drv W
  | w, .o23_a => gateOut Bool.and (w .g2_a) (w .g2_b)
  | w, .o23_b => gateOut Bool.and (w .g3_a) (w .g3_b)
  | w, .outg_a => gateOut Bool.or (w .o01_a) (w .o01_b)
  | w, .outg_b => gateOut Bool.or (w .o23_a) (w .o23_b)
  | w, .s0_a => (w .fn0_in)
  | w, .s0_b => (w .fn1_in)
  | w, .s2_a => (w .fn0_in)
  | w, .s2_b => (w .fa1_in)
  | w, .s3_a => (w .fa0_in)
  | w, .s3_b => (w .fa1_in)
  | w, .fn1_in => gate1Out not (w .na1_a)
  | w, .na1_a => (w .fa1_in)
  | w, .g1_a => gateOut Bool.and (w .s1_a) (w .s1_b)
  | w, .g1_b => entry 1#2 mem
  | w, .fn0_in => gate1Out not (w .na0_a)
  | w, .fa0_in => addrBit 0 st
  | w, .g2_a => gateOut Bool.and (w .s2_a) (w .s2_b)
  | w, .g2_b => entry 2#2 mem
  | w, .na0_a => (w .fa0_in)
  | w, .fa1_in => addrBit 1 st
  | w, .o01_a => gateOut Bool.and (w .g0_a) (w .g0_b)
  | w, .o01_b => gateOut Bool.and (w .g1_a) (w .g1_b)
  | w, .g3_a => gateOut Bool.and (w .s3_a) (w .s3_b)
  | w, .g3_b => entry 3#2 mem
  | w, .cut_in => gateOut Bool.or (w .outg_a) (w .outg_b)
  | w, .cut_r1 => addrBit 0 st
  | w, .cut_r2 => entry 0#2 mem
  | w, .g0_a => gateOut Bool.and (w .s0_a) (w .s0_b)
  | w, .g0_b => entry 0#2 mem
  | w, .s1_a => (w .fa0_in)
  | w, .s1_b => (w .fn1_in)

theorem drv_mono {st mem} :
    Mono (drv st mem) := by
  intro a b h k
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, h, addrBit_mono, entry_mono, gate1Out_mono, gateOut_mono]
theorem drv_env {st st' : List (RSt 2)} {mem mem' : List (BitVec 2 → Bool)}
    (hst : st <+: st') (hmem : mem <+: mem') (w : Wires W) (k : W) :
    drv st mem w k <+:
      drv st' mem' w k := by
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, hmem, hst,
                 addrBit_mono, entry_mono, gate1Out_mono, gateOut_mono]
def wires (i : muxT) : Wires W
  | .o23_a => i.1.1
  | .o23_b => i.1.2
  | .outg_a => i.2.1.1
  | .outg_b => i.2.1.2
  | .s0_a => i.2.2.1.1
  | .s0_b => i.2.2.1.2
  | .s2_a => i.2.2.2.1.1
  | .s2_b => i.2.2.2.1.2
  | .s3_a => i.2.2.2.2.1.1
  | .s3_b => i.2.2.2.2.1.2
  | .fn1_in => i.2.2.2.2.2.1
  | .na1_a => i.2.2.2.2.2.2.1
  | .g1_a => i.2.2.2.2.2.2.2.2.1.1
  | .g1_b => i.2.2.2.2.2.2.2.2.1.2
  | .fn0_in => i.2.2.2.2.2.2.2.2.2.1
  | .fa0_in => i.2.2.2.2.2.2.2.2.2.2.1
  | .g2_a => i.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .g2_b => i.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .na0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .fa1_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .o01_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .o01_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .g3_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .g3_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .cut_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .cut_r1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  | .cut_r2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2
  | .g0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .g0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .s1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .s1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

def ψ (i : muxT) (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) : Prop :=
  Wf (drv s.1 s.2.1) (wires i)
    ∧ i.2.2.2.2.2.2.2.1.1 = s.1
    ∧ i.2.2.2.2.2.2.2.1.2 = s.2.1
    ∧ s.2.2 <+: cutOut (wires i .cut_in) (wires i .cut_r1) (wires i .cut_r2)

/-! ### The invariant, clause by clause

`hw .k` already says this, but with `drv` unapplied; spelling each driver out lets the
proofs below rewrite with it exactly as they did against the old record. -/

section Clauses
variable {st : List (RSt 2)} {mem : List (BitVec 2 → Bool)} {w : Wires W} (hInv : Wf (drv st mem) w)
include hInv

theorem wf_o23_a : w .o23_a <+: gateOut Bool.and (w .g2_a) (w .g2_b) := hInv .o23_a
theorem wf_o23_b : w .o23_b <+: gateOut Bool.and (w .g3_a) (w .g3_b) := hInv .o23_b
theorem wf_outg_a : w .outg_a <+: gateOut Bool.or (w .o01_a) (w .o01_b) := hInv .outg_a
theorem wf_outg_b : w .outg_b <+: gateOut Bool.or (w .o23_a) (w .o23_b) := hInv .outg_b
theorem wf_s0_a : w .s0_a <+: (w .fn0_in) := hInv .s0_a
theorem wf_s0_b : w .s0_b <+: (w .fn1_in) := hInv .s0_b
theorem wf_s2_a : w .s2_a <+: (w .fn0_in) := hInv .s2_a
theorem wf_s2_b : w .s2_b <+: (w .fa1_in) := hInv .s2_b
theorem wf_s3_a : w .s3_a <+: (w .fa0_in) := hInv .s3_a
theorem wf_s3_b : w .s3_b <+: (w .fa1_in) := hInv .s3_b
theorem wf_fn1_in : w .fn1_in <+: gate1Out not (w .na1_a) := hInv .fn1_in
theorem wf_na1_a : w .na1_a <+: (w .fa1_in) := hInv .na1_a
theorem wf_g1_a : w .g1_a <+: gateOut Bool.and (w .s1_a) (w .s1_b) := hInv .g1_a
theorem wf_g1_b : w .g1_b <+: entry 1#2 mem := hInv .g1_b
theorem wf_fn0_in : w .fn0_in <+: gate1Out not (w .na0_a) := hInv .fn0_in
theorem wf_fa0_in : w .fa0_in <+: addrBit 0 st := hInv .fa0_in
theorem wf_g2_a : w .g2_a <+: gateOut Bool.and (w .s2_a) (w .s2_b) := hInv .g2_a
theorem wf_g2_b : w .g2_b <+: entry 2#2 mem := hInv .g2_b
theorem wf_na0_a : w .na0_a <+: (w .fa0_in) := hInv .na0_a
theorem wf_fa1_in : w .fa1_in <+: addrBit 1 st := hInv .fa1_in
theorem wf_o01_a : w .o01_a <+: gateOut Bool.and (w .g0_a) (w .g0_b) := hInv .o01_a
theorem wf_o01_b : w .o01_b <+: gateOut Bool.and (w .g1_a) (w .g1_b) := hInv .o01_b
theorem wf_g3_a : w .g3_a <+: gateOut Bool.and (w .s3_a) (w .s3_b) := hInv .g3_a
theorem wf_g3_b : w .g3_b <+: entry 3#2 mem := hInv .g3_b
theorem wf_cut_in : w .cut_in <+: gateOut Bool.or (w .outg_a) (w .outg_b) := hInv .cut_in
theorem wf_cut_r1 : w .cut_r1 <+: addrBit 0 st := hInv .cut_r1
theorem wf_cut_r2 : w .cut_r2 <+: entry 0#2 mem := hInv .cut_r2
theorem wf_g0_a : w .g0_a <+: gateOut Bool.and (w .s0_a) (w .s0_b) := hInv .g0_a
theorem wf_g0_b : w .g0_b <+: entry 0#2 mem := hInv .g0_b
theorem wf_s1_a : w .s1_a <+: (w .fa0_in) := hInv .s1_a
theorem wf_s1_b : w .s1_b <+: (w .fn1_in) := hInv .s1_b

end Clauses

/-! ### What the netlist computes

This is the block's actual content; only the per-rule bookkeeping around it collapsed. -/

theorem out_q {st : List (RSt 2)} {mem : List (BitVec 2 → Bool)} {w : Wires W} (hInv : Wf (drv st mem) w) : cutOut (w .cut_in) (w .cut_r1) (w .cut_r2) <+: muxOut st mem := by
  have ha0 : (w .fa0_in) <+: addrBit 0 st :=
    (wf_fa0_in hInv).trans (addrBit_mono (List.prefix_rfl))
  have ha1 : (w .fa1_in) <+: addrBit 1 st :=
    (wf_fa1_in hInv).trans (addrBit_mono (List.prefix_rfl))
  have hn0 : (w .fn0_in) <+: na 0 st :=
    (wf_fn0_in hInv).trans (gate1Out_mono _ ((wf_na0_a hInv).trans ha0))
  have hn1 : (w .fn1_in) <+: na 1 st :=
    (wf_fn1_in hInv).trans (gate1Out_mono _ ((wf_na1_a hInv).trans ha1))
  have hs0 : gateOut Bool.and (w .s0_a) (w .s0_b) <+: sel0 st :=
    gateOut_mono _ ((wf_s0_a hInv).trans hn0) ((wf_s0_b hInv).trans hn1)
  have hs1 : gateOut Bool.and (w .s1_a) (w .s1_b) <+: sel1 st :=
    gateOut_mono _ ((wf_s1_a hInv).trans ha0) ((wf_s1_b hInv).trans hn1)
  have hs2 : gateOut Bool.and (w .s2_a) (w .s2_b) <+: sel2 st :=
    gateOut_mono _ ((wf_s2_a hInv).trans hn0) ((wf_s2_b hInv).trans ha1)
  have hs3 : gateOut Bool.and (w .s3_a) (w .s3_b) <+: sel3 st :=
    gateOut_mono _ ((wf_s3_a hInv).trans ha0) ((wf_s3_b hInv).trans ha1)
  have hm0 : (w .g0_b) <+: entry 0#2 mem :=
    (wf_g0_b hInv).trans (entry_mono (List.prefix_rfl))
  have hg0 : gateOut Bool.and (w .g0_a) (w .g0_b) <+: gd0 st mem :=
    gateOut_mono _ ((wf_g0_a hInv).trans hs0) hm0
  have hm1 : (w .g1_b) <+: entry 1#2 mem :=
    (wf_g1_b hInv).trans (entry_mono (List.prefix_rfl))
  have hg1 : gateOut Bool.and (w .g1_a) (w .g1_b) <+: gd1 st mem :=
    gateOut_mono _ ((wf_g1_a hInv).trans hs1) hm1
  have hm2 : (w .g2_b) <+: entry 2#2 mem :=
    (wf_g2_b hInv).trans (entry_mono (List.prefix_rfl))
  have hg2 : gateOut Bool.and (w .g2_a) (w .g2_b) <+: gd2 st mem :=
    gateOut_mono _ ((wf_g2_a hInv).trans hs2) hm2
  have hm3 : (w .g3_b) <+: entry 3#2 mem :=
    (wf_g3_b hInv).trans (entry_mono (List.prefix_rfl))
  have hg3 : gateOut Bool.and (w .g3_a) (w .g3_b) <+: gd3 st mem :=
    gateOut_mono _ ((wf_g3_a hInv).trans hs3) hm3
  have ho01 : gateOut Bool.or (w .o01_a) (w .o01_b) <+: or01 st mem :=
    gateOut_mono _ ((wf_o01_a hInv).trans hg0) ((wf_o01_b hInv).trans hg1)
  have ho23 : gateOut Bool.or (w .o23_a) (w .o23_b) <+: or23 st mem :=
    gateOut_mono _ ((wf_o23_a hInv).trans hg2) ((wf_o23_b hInv).trans hg3)
  have hw : gateOut Bool.or (w .outg_a) (w .outg_b) <+: muxWire st mem :=
    gateOut_mono _ ((wf_outg_a hInv).trans ho01) ((wf_outg_b hInv).trans ho23)
  exact cutOut_mono ((wf_cut_in hInv).trans hw)
    ((wf_cut_r1 hInv).trans (addrBit_mono (List.prefix_rfl)))
    ((wf_cut_r2 hInv).trans (entry_mono (List.prefix_rfl)))

/-! ### One tactic for every connection -/

syntax "mux_case " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mux_case $w:term) => `(tactic| (
      obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e0, e1, hq⟩ := H
      refine ⟨s, existSR_reflexive, ?_, e0, e1, ?_⟩
      · have key := Wf_set drv_mono hw $w _ (‹_ ⊏ _›).isPrefix (by
          simp only [drv, wires]
          first
            | exact List.prefix_rfl
            | exact List.prefix_rfl
            | exact e0 ▸ List.prefix_rfl
            | exact e1 ▸ List.prefix_rfl
            | exact (‹_ ⊏ _›).isPrefix
            | exact (‹_ ⊏ _›).isPrefix
            | assumption)
        intro j; have hj := key j
        cases j <;> simpa [wires, upd, drv] using hj
      · have key := hq.trans (cutOut_mono (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _) (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _) (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _))
        revert key; simp [wires, upd]))

theorem muxNetlist_internals_eq : muxNetlist.internals =
    [muxNetlist.internals.getD 0 (fun _ _ => False), muxNetlist.internals.getD 1 (fun _ _ => False), muxNetlist.internals.getD 2 (fun _ _ => False),
     muxNetlist.internals.getD 3 (fun _ _ => False), muxNetlist.internals.getD 4 (fun _ _ => False), muxNetlist.internals.getD 5 (fun _ _ => False),
     muxNetlist.internals.getD 6 (fun _ _ => False), muxNetlist.internals.getD 7 (fun _ _ => False), muxNetlist.internals.getD 8 (fun _ _ => False),
     muxNetlist.internals.getD 9 (fun _ _ => False), muxNetlist.internals.getD 10 (fun _ _ => False), muxNetlist.internals.getD 11 (fun _ _ => False),
     muxNetlist.internals.getD 12 (fun _ _ => False), muxNetlist.internals.getD 13 (fun _ _ => False), muxNetlist.internals.getD 14 (fun _ _ => False),
     muxNetlist.internals.getD 15 (fun _ _ => False), muxNetlist.internals.getD 16 (fun _ _ => False), muxNetlist.internals.getD 17 (fun _ _ => False),
     muxNetlist.internals.getD 18 (fun _ _ => False), muxNetlist.internals.getD 19 (fun _ _ => False), muxNetlist.internals.getD 20 (fun _ _ => False),
     muxNetlist.internals.getD 21 (fun _ _ => False), muxNetlist.internals.getD 22 (fun _ _ => False), muxNetlist.internals.getD 23 (fun _ _ => False),
     muxNetlist.internals.getD 24 (fun _ _ => False), muxNetlist.internals.getD 25 (fun _ _ => False), muxNetlist.internals.getD 26 (fun _ _ => False),
     muxNetlist.internals.getD 27 (fun _ _ => False), muxNetlist.internals.getD 28 (fun _ _ => False), muxNetlist.internals.getD 29 (fun _ _ => False),
     muxNetlist.internals.getD 30 (fun _ _ => False)] := rfl

/-! All 31 connections, one line each. -/

theorem case_0 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.fa0_in

theorem case_1 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.fa1_in

theorem case_2 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.cut_r1

theorem case_3 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.cut_r2

theorem case_4 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.na0_a

theorem case_5 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.na1_a

theorem case_6 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.fn0_in

theorem case_7 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.fn1_in

theorem case_8 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s0_a

theorem case_9 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s0_b

theorem case_10 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s1_a

theorem case_11 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s1_b

theorem case_12 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s2_a

theorem case_13 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s2_b

theorem case_14 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s3_a

theorem case_15 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s3_b

theorem case_16 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g0_a

theorem case_17 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g0_b

theorem case_18 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g1_a

theorem case_19 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g1_b

theorem case_20 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g2_a

theorem case_21 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g2_b

theorem case_22 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g3_a

theorem case_23 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g3_b

theorem case_24 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.o01_a

theorem case_25 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.o01_b

theorem case_26 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.o23_a

theorem case_27 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.o23_b

theorem case_28 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 28 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.outg_a

theorem case_29 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 29 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.outg_b

theorem case_30 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 30 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.cut_in

section SpecRules
variable (sp : List (RSt 2) × List (BitVec 2 → Bool) × List Bool)

theorem spec_in_st (v : List (RSt 2)) (h : sp.1 ⊏ v) :
    (readMuxSpec.inputs.getIO ↑"st").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_mem (v : List (BitVec 2 → Bool)) (h : sp.2.1 ⊏ v) :
    (readMuxSpec.inputs.getIO ↑"mem").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List Bool) (h1 : sp.2.2 <+: v) (h2 : v <+: muxOut sp.1 sp.2.1) :
    (readMuxSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 4000000 in
theorem refines_ψ : muxNetlist ⊑_{ψ} readMuxSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, hq⟩ := H
    case_transition Hcontains : Module.inputs muxNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [muxNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    -- The port's identity is decided by `hpre`'s type; the proofs are one shape.
    all_goals first
      | exact ⟨_, _, spec_in_st s _ (by rw [← e0]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env (e0 ▸ hpre.isPrefix) List.prefix_rfl _), rfl, e1, hq⟩
      | exact ⟨_, _, spec_in_mem s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl (e1 ▸ hpre.isPrefix) _), e0, rfl, hq⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, hq⟩ := H
    case_transition Hcontains : Module.outputs muxNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [muxNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    simp only [eq_mp_eq_cast, cast_self]
    dsimp only [wires] at hq
    have ho := out_q hw
    dsimp only [wires] at ho
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ hq ho, hw, e0, e1, List.prefix_rfl⟩
  · intro rule mid_i Hin Hrule
    rw [muxNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
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

theorem refines_initial : Module.refines_initial muxNetlist readMuxSpec ψ := by
  intro i hi
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  dsimp only [muxNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  repeat' (obtain ⟨rfl, hi⟩ := hi)
  refine ⟨([], [], []), rfl, ?_, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

theorem mux_refines : muxNetlist ⊑ readMuxSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.ReadPort
