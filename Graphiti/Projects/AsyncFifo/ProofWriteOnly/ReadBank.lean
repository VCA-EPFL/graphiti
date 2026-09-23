/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadState
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusReg
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadStateTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusRegTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadBankLemmas

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.ReadBank

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff
variable {clk : List Bool} {d : List (RNext 2)} {crn : List Bool} {R : Nat}

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  The wires carry different things -- bits, state
words, the Gray bus -- so this is `Netlist.Het`'s invariant, indexed by what each wire
carries. -/

open Graphiti.AsyncFifo.Netlist

/-- The eight driven wires.  The bank's own clock, next-state bus and clear are not among them:
they are inputs, closed over by `drv`. -/
inductive W
  | stR_clk | stR_d | stR_clrn
  | grR_clk | grR_d | grR_clrn
  | stF_in | emptyA_q
  deriving DecidableEq

/-- What each wire carries. -/
def Ty : W → Type
  | .stR_d | .stF_in | .emptyA_q => RSt 2
  | .grR_d => BitVec 3
  | _ => Bool

/-- What drives each wire, and the only place the shape of this netlist is written down: the
forks hand both registers the clock and the clear, `unpN` splits the next-state bus, the state
register feeds its own fork, and the `empty` adapter reads that fork. -/
def drv (clk crn : List Bool) (d : List (RNext 2)) : Het.Drv Ty
  | _, .stR_clk | _, .grR_clk => clk
  | _, .stR_clrn | _, .grR_clrn => crn
  | _, .stR_d => stOf d
  | _, .grR_d => gnextOf d
  | w, .stF_in => ReadState.stOut (w .stR_clk) (w .stR_d) (w .stR_clrn)
  | w, .emptyA_q => w .stF_in

/-- The two cases that are not the identity are named, and the rest are not left to
`apply_rules` as elsewhere: offering `ReadState.stOut_mono` to a goal it does not fit makes the
unifier unfold `stOut`, which is seven `dffOut`s deep, and the proof times out at `whnf`. -/
theorem drv_mono {clk crn d} : Het.Mono (drv clk crn d) := by
  intro a b h k
  cases k <;> simp only [drv]
  case stF_in => exact ReadState.stOut_mono (h .stR_clk) (h .stR_d) (h .stR_clrn)
  case emptyA_q => exact h .stF_in
  all_goals exact List.prefix_rfl

/-- Growing the bank's own inputs grows every driver. -/
theorem drv_env {clk clk' crn crn' : List Bool} {d d' : List (RNext 2)}
    (hc : clk <+: clk') (hr : crn <+: crn') (hd : d <+: d') (w : Het.Wires Ty) (k : W) :
    drv clk crn d w k <+: drv clk' crn' d' w k := by
  cases k <;> simp only [drv] <;>
    first
      | exact List.prefix_rfl | exact hc | exact hr
      | exact stOf_mono hd | exact gnextOf_mono hd

/-- The reduced state is a nested product; `wires` reads it as an assignment. -/
def wires (i : bankT) : Het.Wires Ty
  | .stF_in => i.1 | .emptyA_q => i.2.2.2.2.2.1
  | .stR_clk => i.2.2.1.1 | .stR_d => i.2.2.1.2.1 | .stR_clrn => i.2.2.1.2.2.1
  | .grR_clk => i.2.2.2.2.2.2.1 | .grR_d => i.2.2.2.2.2.2.2.1
  | .grR_clrn => i.2.2.2.2.2.2.2.2.1

/-- The invariant: the wires are well formed, the three inputs the netlist holds are the
specification's, the registered output is what it has reported, and the two combinational
outputs have reported no more than the wire behind them holds. -/
def ψ (i : bankT) (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool ×
    List (BitVec 3)) : Prop :=
  Het.Wf (drv s.1 s.2.2.1 s.2.1) (wires i)
    ∧ i.2.2.2.1 = s.1 ∧ i.2.2.2.2.1 = s.2.1 ∧ i.2.1 = s.2.2.1
    ∧ i.2.2.2.2.2.2.2.2.2 = s.2.2.2.2.2
    ∧ s.2.2.2.1 <+: wires i .stF_in
    ∧ s.2.2.2.2.1 <+: (wires i .emptyA_q).map (·.empty)

/-! ### Each block sees prefixes of the bank's own inputs -/

theorem out_st {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w) :
    w .stF_in <+: ReadState.stOut clk (stOf d) crn :=
  (hw .stF_in).trans (ReadState.stOut_mono (hw .stR_clk) (hw .stR_d) (hw .stR_clrn))

theorem out_empty {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w) :
    (w .emptyA_q).map (·.empty) <+: (ReadState.stOut clk (stOf d) crn).map (·.empty) :=
  ((hw .emptyA_q).trans (out_st hw)).map _

theorem out_gray {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w)
    {v : List (BitVec 3)} (h : v <+: BusReg.busOut (w .grR_clk) (w .grR_d) (w .grR_clrn)) :
    v <+: BusReg.busOut clk (gnextOf d) crn :=
  h.trans (BusReg.busOut_mono (hw .grR_clk) (hw .grR_d) (hw .grR_clrn))

/-! ### One tactic for every connection -/

syntax "bankr_case" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| bankr_case) => `(tactic| (
      obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q,
        ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
      obtain ⟨_, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨_, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e1, e2, e3, e4, h5, h6⟩ := H
      refine ⟨s, existSR_reflexive, Het.step hw drv_mono ?_ ?_, e1, e2, e3, e4, ?_, ?_⟩
      · intro j
        cases j <;> dsimp only [wires] <;>
          first | exact List.prefix_rfl | exact (‹_ ⊏ _›).isPrefix
      · intro j
        have hj := hw j
        cases j <;> (try dsimp only [wires, drv] at hj) <;> dsimp only [wires, drv] <;>
          first
            | exact hj
            | assumption
            | exact List.prefix_rfl
            | exact e1 ▸ List.prefix_rfl
            | exact e3 ▸ List.prefix_rfl
            | exact e2 ▸ List.prefix_rfl
      · dsimp only [wires] at h5 ⊢
        first | exact h5 | exact h5.trans (‹_ ⊏ _›).isPrefix
      · dsimp only [wires] at h6 ⊢
        first | exact h6 | exact h6.trans ((‹_ ⊏ _›).isPrefix.map _)))

theorem bankNetlist_internals_eq : bankNetlist.internals =
    [bankNetlist.internals.getD 0 (fun _ _ => False), bankNetlist.internals.getD 1 (fun _ _ => False), bankNetlist.internals.getD 2 (fun _ _ => False),
     bankNetlist.internals.getD 3 (fun _ _ => False), bankNetlist.internals.getD 4 (fun _ _ => False), bankNetlist.internals.getD 5 (fun _ _ => False),
     bankNetlist.internals.getD 6 (fun _ _ => False), bankNetlist.internals.getD 7 (fun _ _ => False)] := rfl


/-! ### The specification's own rules -/

section SpecRules
variable (sp : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool ×
  List (BitVec 3))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (bankExact.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (RNext 2)) (h : sp.2.1 ⊏ v) :
    (bankExact.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (bankExact.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_st (v : List (RSt 2)) (h1 : sp.2.2.2.1 <+: v)
    (h2 : v <+: ReadState.stOut sp.1 (stOf sp.2.1) sp.2.2.1) :
    (bankExact.outputs.getIO ↑"st").2 sp v (sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_empty (v : List Bool) (h1 : sp.2.2.2.2.1 <+: v)
    (h2 : v <+: (ReadState.stOut sp.1 (stOf sp.2.1) sp.2.2.1).map (·.empty)) :
    (bankExact.outputs.getIO ↑"empty").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_gray (v : List (BitVec 3)) (h1 : sp.2.2.2.2.2 <+: v)
    (h2 : v <+: BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1) :
    (bankExact.outputs.getIO ↑"gray").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : bankNetlist ⊑_{ψ} bankExact := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q,
      ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    obtain ⟨_, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, e4, h5, h6⟩ := H
    case_transition Hcontains : Module.inputs bankNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    -- The port's identity is decided by `hpre`'s type; the three proofs are one shape.
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env (e1 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl _),
          rfl, e2, e3, e4, h5, h6⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix) _),
          e1, rfl, e3, e4, h5, h6⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env List.prefix_rfl (e3 ▸ hpre.isPrefix) List.prefix_rfl _),
          e1, e2, rfl, e4, h5, h6⟩
  · intro ident mid_i v Hrule
    obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q,
      ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    obtain ⟨_, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, e4, h5, h6⟩ := H
    have hst := out_st hw
    have hem := out_empty hw
    dsimp only [wires] at hst hem h5 h6
    case_transition Hcontains : Module.outputs bankNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals first
      | exact ⟨s, _, existSR_reflexive, spec_out_st s _ h5 hst,
          hw, e1, e2, e3, e4, List.prefix_rfl, h6⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_empty s _ h6 hem,
          hw, e1, e2, e3, e4, h5, List.prefix_rfl⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_gray s _ (e4 ▸ ‹_›) (out_gray hw ‹_›),
          hw, e1, e2, e3, rfl, h5, h6⟩
  · intro rule mid Hin Hrule
    rw [bankNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h
    all_goals (subst h; bankr_case)

theorem refines_initial : Module.refines_initial bankNetlist bankExact ψ := by
  intro i hi
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q,
    ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  dsimp only [bankNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨([], [], [], [], [], []), rfl, ?_, rfl, rfl, rfl, rfl,
    List.nil_prefix, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The two registers refine the read domain's register bank.** -/
theorem bank_refines : bankNetlist ⊑ bankExact :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.ReadBank
