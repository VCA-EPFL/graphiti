/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncStageLemmas
import Graphiti.Projects.AsyncFifo.components.level5.SyncStage

/-!
# The synchroniser stage as three settling flip-flops

`SyncStage.lean` builds the stage out of three `settlingDffO`s, a fork, the two projections and
a packer, and proves the mathematics that makes the substitution possible (`syncOut_pack`: the
bus-level stream *is* the three bits packed).  What is left is the refinement itself, in the
shape every other netlist in this development uses: a structural invariant, one lemma per rule.

This is *not* in tension with `Evidence/PlainSync.lean`, which proves the opposite for the plain
synchroniser: `syncNetlist ⊑ SyncStage.syncSpec` is false, because `Dff.dff_metastable` (in `Metastability.lean`)
exhibits a clean clock, a released clear and data glitching in the aperture for which the
Boolean netlist oscillates for ever --- no instant after which its output is any constant, so
nothing an oracle can name.  The stage here escapes that not by being cleverer but by being a
different object: `settlingDffO` takes the oracle as two *input ports* (`osel`, `ojunk`), and
that it settles at all is assumed, not derived.  `PlainSync.lean` remains the honest account of the
wiring of two ordinary stages; this file is where the assumption is carried, one bit at a time.

The point of the file is what it removes.  Before it, `SyncStage.syncSpec` was a primitive block and
metastability was assumed of a three-bit bus.  After it, `SyncStage.syncSpec` is a netlist like any other,
and the assumption has moved into one primitive about one bit: `settlingDffO`, three per domain.
See `stage_refines` for exactly what the chain depends on and what merely certifies it.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.SyncStageContract

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.BusReg Graphiti.AsyncFifo.SyncSettle Graphiti.AsyncFifo.SyncStage
open Batteries (AssocList)

instance instMatch (lat su stl : Nat) : MatchInterface (stageNetlist lat su stl) (SyncStage.syncSpec (n := 2) lat su stl) := by
  dsimp [stageNetlist, SyncStage.syncSpec]
  solve_match_interface

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Over an index rather than a record with one field
per wire, the per-rule lemmas collapse into `Netlist.Wf_step_of`, `Netlist.Wf_drv` and
`Netlist.Wf_congr`, so what is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The fifteen driven wires.  The stage's own clock, data bus and oracle are not among them:
they are inputs, closed over by `drv`. -/
inductive W
  | pk_b0
  | pk_b1
  | pk_b2
  | ff0_clk
  | ff0_d
  | ff0_osel
  | ff0_ojunk
  | ff1_clk
  | ff1_d
  | ff1_osel
  | ff1_ojunk
  | ff2_clk
  | ff2_d
  | ff2_osel
  | ff2_ojunk
  deriving DecidableEq

/-- What drives each wire, and the only place the shape of this stage is written down: three
settling flip-flops, each over its own bit of the delayed bus and its own two oracle bits. -/
def drv (lat su stl : Nat) (clk : List Bool) (d : List (BitVec 3)) (orc : List (Orc 2)) :
    Drv W
  | w, .pk_b0 => settleOut1 su stl (w .ff0_clk) (w .ff0_d) (w .ff0_osel) (w .ff0_ojunk)
  | w, .pk_b1 => settleOut1 su stl (w .ff1_clk) (w .ff1_d) (w .ff1_osel) (w .ff1_ojunk)
  | w, .pk_b2 => settleOut1 su stl (w .ff2_clk) (w .ff2_d) (w .ff2_osel) (w .ff2_ojunk)
  | _, .ff0_clk => clk
  | _, .ff0_d => bitsOf 0 (wireOf lat d)
  | _, .ff0_osel => selBit 0 orc
  | _, .ff0_ojunk => junkBit 0 orc
  | _, .ff1_clk => clk
  | _, .ff1_d => bitsOf 1 (wireOf lat d)
  | _, .ff1_osel => selBit 1 orc
  | _, .ff1_ojunk => junkBit 1 orc
  | _, .ff2_clk => clk
  | _, .ff2_d => bitsOf 2 (wireOf lat d)
  | _, .ff2_osel => selBit 2 orc
  | _, .ff2_ojunk => junkBit 2 orc

theorem drv_mono {lat su stl clk d orc} : Mono (drv lat su stl clk d orc) := by
  intro a b h k
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, h, settleOut1_mono]
theorem drv_env {lat su stl : Nat} {clk clk' : List Bool} {d d' : List (BitVec 3)}
    {orc orc' : List (Orc 2)} (hclk : clk <+: clk') (hd : d <+: d') (horc : orc <+: orc')
    (w : Wires W) (k : W) :
    drv lat su stl clk d orc w k <+: drv lat su stl clk' d' orc' w k := by
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, hclk, hd, horc,
                 bitsOf_mono, junkBit_mono, selBit_mono, wireOf_mono]
def wires (i : stageT) : Wires W
  | .pk_b0 => i.1.1
  | .pk_b1 => i.1.2.1
  | .pk_b2 => i.1.2.2
  | .ff0_clk => i.2.2.2.2.1.1
  | .ff0_d => i.2.2.2.2.1.2.1
  | .ff0_osel => i.2.2.2.2.1.2.2.1
  | .ff0_ojunk => i.2.2.2.2.1.2.2.2
  | .ff1_clk => i.2.2.2.2.2.1.1
  | .ff1_d => i.2.2.2.2.2.1.2.1
  | .ff1_osel => i.2.2.2.2.2.1.2.2.1
  | .ff1_ojunk => i.2.2.2.2.2.1.2.2.2
  | .ff2_clk => i.2.2.2.2.2.2.1
  | .ff2_d => i.2.2.2.2.2.2.2.1
  | .ff2_osel => i.2.2.2.2.2.2.2.2.1
  | .ff2_ojunk => i.2.2.2.2.2.2.2.2.2

/-- The invariant: the wires are well formed, the three inputs the netlist holds are the
specification's, and the packer has reported no more than the three flip-flops settle to. -/
def ψ (lat su stl : Nat) (i : stageT) (s : List Bool × List (BitVec 3) × List (Orc 2) × List (BitVec 3)) : Prop :=
  Wf (drv lat su stl s.1 s.2.1 s.2.2.1) (wires i)
    ∧ i.2.2.1 = s.1 ∧ i.2.1 = s.2.1 ∧ i.2.2.2.1 = s.2.2.1
    ∧ s.2.2.2 <+: pack3Out (wires i .pk_b0) (wires i .pk_b1) (wires i .pk_b2)

/-- What the stage reports is a prefix of what the specification says.  `syncOut_pack` is the
three per-bit `SettleOut` clauses; each flip-flop meets its own. -/
theorem out_q {lat su stl : Nat} {clk : List Bool} {d : List (BitVec 3)}
    {orc : List (Orc 2)} {w : Wires W} (hw : Wf (drv lat su stl clk d orc) w) :
    pack3Out (w .pk_b0) (w .pk_b1) (w .pk_b2) <+: SyncStage.syncOut lat su stl clk d orc := by
  rw [syncOut_pack]
  refine pack3Out_mono ?_ ?_ ?_
  · exact (hw .pk_b0).trans (settleOut1_mono (hw .ff0_clk) (hw .ff0_d)
      (hw .ff0_osel) (hw .ff0_ojunk))
  · exact (hw .pk_b1).trans (settleOut1_mono (hw .ff1_clk) (hw .ff1_d)
      (hw .ff1_osel) (hw .ff1_ojunk))
  · exact (hw .pk_b2).trans (settleOut1_mono (hw .ff2_clk) (hw .ff2_d)
      (hw .ff2_osel) (hw .ff2_ojunk))

/-! ### One tactic for every connection -/

/-- Each of the packer's three bits either stands or advances; one `⊏` is in scope. -/
syntax "sync_pre" : tactic
/-- Every wire of `mid` is the wire of `i`: what an input rule changes is an input. -/
syntax "sync_same" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sync_pre) => `(tactic| first | exact List.prefix_rfl | exact (‹_ ⊏ _›).isPrefix)
  | `(tactic| sync_same) =>
      `(tactic| (intro j; cases j <;> dsimp only [wires] <;> exact List.prefix_rfl))

syntax "sync_case" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sync_case) => `(tactic| (
      obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unpB_d, clkF_in, unpO_orc, ⟨ff0_clk, ff0_d, ff0_osel, ff0_ojunk⟩, ⟨ff1_clk, ff1_d, ff1_osel, ff1_ojunk⟩, ⟨ff2_clk, ff2_d, ff2_osel, ff2_ojunk⟩⟩ := i
      obtain ⟨⟨_, _, _⟩, _, _, _, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _, _⟩, _, _, _, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e0, e1, e2, h3⟩ := H
      refine ⟨s, existSR_reflexive, Wf_step_of hw drv_mono ?_ ?_, e0, e1, e2, ?_⟩
      · intro j
        cases j <;> dsimp only [wires] <;> sync_pre
      · intro j
        have hj := hw j
        cases j <;> (try dsimp only [wires, drv] at hj) <;> dsimp only [wires, drv] <;>
          first
            | exact hj
            | exact List.prefix_rfl
            | exact e0 ▸ List.prefix_rfl
            | exact e1 ▸ List.prefix_rfl
            | exact e2 ▸ List.prefix_rfl
            | assumption
      · dsimp only [wires] at h3 ⊢
        exact h3.trans (pack3Out_mono (by sync_pre) (by sync_pre) (by sync_pre))))

theorem stageNetlist_internals_eq (lat su stl : Nat) :
    (stageNetlist lat su stl).internals =
      [(stageNetlist lat su stl).internals.getD 0 (fun _ _ => False), (stageNetlist lat su stl).internals.getD 1 (fun _ _ => False),
       (stageNetlist lat su stl).internals.getD 2 (fun _ _ => False), (stageNetlist lat su stl).internals.getD 3 (fun _ _ => False),
       (stageNetlist lat su stl).internals.getD 4 (fun _ _ => False), (stageNetlist lat su stl).internals.getD 5 (fun _ _ => False),
       (stageNetlist lat su stl).internals.getD 6 (fun _ _ => False), (stageNetlist lat su stl).internals.getD 7 (fun _ _ => False),
       (stageNetlist lat su stl).internals.getD 8 (fun _ _ => False), (stageNetlist lat su stl).internals.getD 9 (fun _ _ => False),
       (stageNetlist lat su stl).internals.getD 10 (fun _ _ => False), (stageNetlist lat su stl).internals.getD 11 (fun _ _ => False),
       (stageNetlist lat su stl).internals.getD 12 (fun _ _ => False), (stageNetlist lat su stl).internals.getD 13 (fun _ _ => False),
       (stageNetlist lat su stl).internals.getD 14 (fun _ _ => False)] := rfl


/-! ### The specification's own rules -/

section SpecRules
variable (lat su stl : Nat) (sp : List Bool × List (BitVec 3) × List (Orc 2) × List (BitVec 3))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    ((SyncStage.syncSpec (n := 2) lat su stl).inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (BitVec 3)) (h : sp.2.1 ⊏ v) :
    ((SyncStage.syncSpec (n := 2) lat su stl).inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_orc (v : List (Orc 2)) (h : sp.2.2.1 ⊏ v) :
    ((SyncStage.syncSpec (n := 2) lat su stl).inputs.getIO ↑"orc").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List (BitVec 3)) (h1 : sp.2.2.2 <+: v)
    (h2 : v <+: SyncStage.syncOut lat su stl sp.1 sp.2.1 sp.2.2.1) :
    ((SyncStage.syncSpec (n := 2) lat su stl).outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ (lat su stl : Nat) :
    (stageNetlist lat su stl) ⊑_{ψ lat su stl} (SyncStage.syncSpec (n := 2) lat su stl) := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unpB_d, clkF_in, unpO_orc, ⟨ff0_clk, ff0_d, ff0_osel, ff0_ojunk⟩, ⟨ff1_clk, ff1_d, ff1_osel, ff1_ojunk⟩, ⟨ff2_clk, ff2_d, ff2_osel, ff2_ojunk⟩⟩ := i
    obtain ⟨⟨_, _, _⟩, _, _, _, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, h3⟩ := H
    case_transition Hcontains : Module.inputs (stageNetlist lat su stl), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [stageNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    all_goals dsimp only [wires] at h3
    -- Both pieces are carried across pointwise; see `NetlistWf.lean` for why.
    all_goals first
      | exact ⟨_, _, spec_in_clk lat su stl s _ (by rw [← e0]; exact hpre),
          existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env (e0 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl _))
            (by sync_same) (by sync_same), rfl, e1, e2,
          h3.trans (pack3Out_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl)⟩
      | exact ⟨_, _, spec_in_d lat su stl s _ (by rw [← e1]; exact hpre),
          existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl (e1 ▸ hpre.isPrefix) List.prefix_rfl _))
            (by sync_same) (by sync_same), e0, rfl, e2,
          h3.trans (pack3Out_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl)⟩
      | exact ⟨_, _, spec_in_orc lat su stl s _ (by rw [← e2]; exact hpre),
          existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix) _))
            (by sync_same) (by sync_same), e0, e1, rfl,
          h3.trans (pack3Out_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl)⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unpB_d, clkF_in, unpO_orc, ⟨ff0_clk, ff0_d, ff0_osel, ff0_ojunk⟩, ⟨ff1_clk, ff1_d, ff1_osel, ff1_ojunk⟩, ⟨ff2_clk, ff2_d, ff2_osel, ff2_ojunk⟩⟩ := i
    obtain ⟨⟨_, _, _⟩, _, _, _, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, h3⟩ := H
    have ho := out_q hw
    dsimp only [wires] at ho h3
    case_transition Hcontains : Module.outputs (stageNetlist lat su stl), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [stageNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    exact ⟨s, _, existSR_reflexive, spec_out_q lat su stl s _ h3 ho,
      hw, e0, e1, e2, List.prefix_rfl⟩
  · intro rule mid Hin Hrule
    rw [stageNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals (subst h; sync_case)

theorem refines_initial (lat su stl : Nat) :
    Module.refines_initial (stageNetlist lat su stl) (SyncStage.syncSpec (n := 2) lat su stl)
      (ψ lat su stl) := by
  intro i hi
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unpB_d, clkF_in, unpO_orc, ⟨ff0_clk, ff0_d, ff0_osel, ff0_ojunk⟩, ⟨ff1_clk, ff1_d, ff1_osel, ff1_ojunk⟩, ⟨ff2_clk, ff2_d, ff2_osel, ff2_ojunk⟩⟩ := i
  dsimp only [stageNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨([], [], [], []), rfl, ?_, rfl, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The three settling flip-flops refine one synchroniser stage.** -/
theorem stage_refines (lat su stl : Nat) :
    (stageNetlist lat su stl) ⊑ (SyncStage.syncSpec (n := 2) lat su stl) :=
  ⟨inferInstance, ψ lat su stl, refines_ψ lat su stl, refines_initial lat su stl⟩


theorem syncImpl_refines (lat su stl : Nat) :
    (SyncStage.syncImpl lat su stl) ⊑ (SyncStage.syncSpec (n := 2) lat su stl) :=
  Module.refines_transitive _ (Module.refines_eq' (SyncStage.stageNetlist_sigma lat su stl).symm)
    (stage_refines lat su stl)

end Graphiti.AsyncFifo.SyncStageContract
