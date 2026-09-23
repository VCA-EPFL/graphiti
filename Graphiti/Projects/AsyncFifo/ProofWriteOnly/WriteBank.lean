/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteState
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusReg
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.RegFile
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteStateTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusRegTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteBankLemmas

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.WriteBank

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff
variable {clk : List Bool} {d : List (WNext Bool 2)} {crn : List Bool} {R : Nat}

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  The wires carry different things -- bits, bus
addresses, state words -- so this is `Netlist.Het`'s invariant, indexed by what each wire
carries. -/

open Graphiti.AsyncFifo.Netlist

/-- The thirteen driven wires.  The bank's own clock, next-state bus and clear are not among
them: they are inputs, closed over by `drv`. -/
inductive W
  | memB_clk | memB_we | memB_addr | memB_data | memB_clrn
  | stR_clk | stR_d | stR_clrn
  | grR_clk | grR_d | grR_clrn
  | stF_in | fullA_q
  deriving DecidableEq

/-- What each wire carries. -/
def Ty : W → Type
  | .memB_addr => BitVec 2
  | .stR_d | .stF_in | .fullA_q => WSt 2
  | .grR_d => BitVec 3
  | _ => Bool

/-- What drives each wire, and the only place the shape of this netlist is written down: the
forks hand the three blocks the clock and the clear, `unpN` splits the next-state bus, the
state register feeds its own fork, and the `full` adapter reads that fork. -/
def drv (clk crn : List Bool) (d : List (WNext Bool 2)) : Het.Drv Ty
  | _, .memB_clk | _, .stR_clk | _, .grR_clk => clk
  | _, .memB_clrn | _, .stR_clrn | _, .grR_clrn => crn
  | _, .memB_we => weOf d
  | _, .memB_addr => addrOf d
  | _, .memB_data => dataOf d
  | _, .stR_d => stOf d
  | _, .grR_d => gnextOf d
  | w, .stF_in => WriteState.stOut (w .stR_clk) (w .stR_d) (w .stR_clrn)
  | w, .fullA_q => w .stF_in

/-- The two cases that are not the identity are named, and the rest are not left to
`apply_rules` as elsewhere: offering `WriteState.stOut_mono` to a goal it does not fit makes the
unifier unfold `stOut`, which is seven `dffOut`s deep, and the proof times out at `whnf`. -/
theorem drv_mono {clk crn d} : Het.Mono (drv clk crn d) := by
  intro a b h k
  cases k <;> simp only [drv]
  case stF_in => exact WriteState.stOut_mono (h .stR_clk) (h .stR_d) (h .stR_clrn)
  case fullA_q => exact h .stF_in
  all_goals exact List.prefix_rfl

/-- Growing the bank's own inputs grows every driver. -/
theorem drv_env {clk clk' crn crn' : List Bool} {d d' : List (WNext Bool 2)}
    (hc : clk <+: clk') (hr : crn <+: crn') (hd : d <+: d') (w : Het.Wires Ty) (k : W) :
    drv clk crn d w k <+: drv clk' crn' d' w k := by
  cases k <;> simp only [drv] <;>
    first
      | exact List.prefix_rfl | exact hc | exact hr
      | exact weOf_mono hd | exact addrOf_mono hd | exact dataOf_mono hd
      | exact stOf_mono hd | exact gnextOf_mono hd

/-- The reduced state is a nested product; `wires` reads it as an assignment. -/
def wires (i : bankT) : Het.Wires Ty
  | .memB_clk => i.1.1 | .memB_we => i.1.2.1 | .memB_addr => i.1.2.2.1
  | .memB_data => i.1.2.2.2.1 | .memB_clrn => i.1.2.2.2.2.1
  | .stF_in => i.2.1 | .fullA_q => i.2.2.2.2.1
  | .stR_clk => i.2.2.2.1.1 | .stR_d => i.2.2.2.1.2.1 | .stR_clrn => i.2.2.2.1.2.2.1
  | .grR_clk => i.2.2.2.2.2.2.2.1 | .grR_d => i.2.2.2.2.2.2.2.2.1
  | .grR_clrn => i.2.2.2.2.2.2.2.2.2.1

/-- The invariant: the wires are well formed, the three inputs the netlist holds are the
specification's, the two registered outputs are what it has reported, and the two combinational
outputs have reported no more than the wire behind them holds. -/
def ψ (i : bankT) (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool ×
    List (BitVec 3) × List (BitVec 2 → Bool)) : Prop :=
  Het.Wf (drv s.1 s.2.2.1 s.2.1) (wires i)
    ∧ i.2.2.2.2.2.1 = s.1 ∧ i.2.2.2.2.2.2.1 = s.2.1 ∧ i.2.2.1 = s.2.2.1
    ∧ i.2.2.2.2.2.2.2.2.2.2 = s.2.2.2.2.2.1 ∧ i.1.2.2.2.2.2 = s.2.2.2.2.2.2
    ∧ s.2.2.2.1 <+: wires i .stF_in
    ∧ s.2.2.2.2.1 <+: (wires i .fullA_q).map (·.full)

/-! ### Each block sees prefixes of the bank's own inputs -/

theorem out_st {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w) :
    w .stF_in <+: WriteState.stOut clk (stOf d) crn :=
  (hw .stF_in).trans (WriteState.stOut_mono (hw .stR_clk) (hw .stR_d) (hw .stR_clrn))

theorem out_full {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w) :
    (w .fullA_q).map (·.full) <+: (WriteState.stOut clk (stOf d) crn).map (·.full) :=
  ((hw .fullA_q).trans (out_st hw)).map _

theorem out_gray {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w)
    {v : List (BitVec 3)} (h : v <+: BusReg.busOut (w .grR_clk) (w .grR_d) (w .grR_clrn)) :
    v <+: BusReg.busOut clk (gnextOf d) crn :=
  h.trans (BusReg.busOut_mono (hw .grR_clk) (hw .grR_d) (hw .grR_clrn))

theorem out_mem {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w)
    {v : List (BitVec 2 → Bool)}
    (h : v <+: RegFile.memOut (w .memB_clk) (w .memB_we) (w .memB_addr) (w .memB_data)
      (w .memB_clrn)) :
    v <+: RegFile.memOut clk (weOf d) (addrOf d) (dataOf d) crn :=
  h.trans (RegFile.memOut_mono (hw .memB_clk) (hw .memB_we) (hw .memB_addr) (hw .memB_data)
    (hw .memB_clrn))

/-! ### One tactic for every connection -/

syntax "bank_case" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| bank_case) => `(tactic| (
      obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in,
        ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d,
        ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
      obtain ⟨⟨_, _, _, _, _, _⟩, _, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _, _, _, _, _⟩, _, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e1, e2, e3, e4, e5, h6, h7⟩ := H
      refine ⟨s, existSR_reflexive, Het.step hw drv_mono ?_ ?_, e1, e2, e3, e4, e5, ?_, ?_⟩
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
      · dsimp only [wires] at h6 ⊢
        first | exact h6 | exact h6.trans (‹_ ⊏ _›).isPrefix
      · dsimp only [wires] at h7 ⊢
        first | exact h7 | exact h7.trans ((‹_ ⊏ _›).isPrefix.map _)))

theorem bankNetlist_internals_eq : bankNetlist.internals =
    [bankNetlist.internals.getD 0 (fun _ _ => False), bankNetlist.internals.getD 1 (fun _ _ => False), bankNetlist.internals.getD 2 (fun _ _ => False),
     bankNetlist.internals.getD 3 (fun _ _ => False), bankNetlist.internals.getD 4 (fun _ _ => False), bankNetlist.internals.getD 5 (fun _ _ => False),
     bankNetlist.internals.getD 6 (fun _ _ => False), bankNetlist.internals.getD 7 (fun _ _ => False), bankNetlist.internals.getD 8 (fun _ _ => False),
     bankNetlist.internals.getD 9 (fun _ _ => False), bankNetlist.internals.getD 10 (fun _ _ => False), bankNetlist.internals.getD 11 (fun _ _ => False),
     bankNetlist.internals.getD 12 (fun _ _ => False)] := rfl


/-! ### The specification's own rules -/

section SpecRules
variable (sp : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool ×
  List (BitVec 3) × List (BitVec 2 → Bool))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (bankExact.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (WNext Bool 2)) (h : sp.2.1 ⊏ v) :
    (bankExact.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (bankExact.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_st (v : List (WSt 2)) (h1 : sp.2.2.2.1 <+: v)
    (h2 : v <+: WriteState.stOut sp.1 (stOf sp.2.1) sp.2.2.1) :
    (bankExact.outputs.getIO ↑"st").2 sp v (sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_full (v : List Bool) (h1 : sp.2.2.2.2.1 <+: v)
    (h2 : v <+: (WriteState.stOut sp.1 (stOf sp.2.1) sp.2.2.1).map (·.full)) :
    (bankExact.outputs.getIO ↑"full").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_gray (v : List (BitVec 3)) (h1 : sp.2.2.2.2.2.1 <+: v)
    (h2 : v <+: BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1) :
    (bankExact.outputs.getIO ↑"gray").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v, sp.2.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_mem (v : List (BitVec 2 → Bool)) (h1 : sp.2.2.2.2.2.2 <+: v)
    (h2 : v <+: RegFile.memOut sp.1 (weOf sp.2.1) (addrOf sp.2.1) (dataOf sp.2.1) sp.2.2.1) :
    (bankExact.outputs.getIO ↑"mem").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, sp.2.2.2.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : bankNetlist ⊑_{ψ} bankExact := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in,
      ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d,
      ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, e4, e5, h6, h7⟩ := H
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
          rfl, e2, e3, e4, e5, h6, h7⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix) _),
          e1, rfl, e3, e4, e5, h6, h7⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env List.prefix_rfl (e3 ▸ hpre.isPrefix) List.prefix_rfl _),
          e1, e2, rfl, e4, e5, h6, h7⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in,
      ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d,
      ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, e4, e5, h6, h7⟩ := H
    have hst := out_st hw
    have hfl := out_full hw
    dsimp only [wires] at hst hfl h6 h7
    case_transition Hcontains : Module.outputs bankNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals first
      | exact ⟨s, _, existSR_reflexive, spec_out_st s _ h6 hst,
          hw, e1, e2, e3, e4, e5, List.prefix_rfl, h7⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_full s _ h7 hfl,
          hw, e1, e2, e3, e4, e5, h6, List.prefix_rfl⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_gray s _ (e4 ▸ ‹_›) (out_gray hw ‹_›),
          hw, e1, e2, e3, rfl, e5, h6, h7⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_mem s _ (e5 ▸ ‹_›) (out_mem hw ‹_›),
          hw, e1, e2, e3, e4, rfl, h6, h7⟩
  · intro rule mid Hin Hrule
    rw [bankNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals (subst h; bank_case)

theorem refines_initial : Module.refines_initial bankNetlist bankExact ψ := by
  intro i hi
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in,
    ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d,
    ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  dsimp only [bankNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := hi
  refine ⟨([], [], [], [], [], [], []), rfl, ?_, rfl, rfl, rfl, rfl, rfl,
    List.nil_prefix, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The three blocks refine the write domain's register bank.** -/
theorem bank_refines : bankNetlist ⊑ bankExact :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.WriteBank
