/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadState
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusReg
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.ReadStateTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusRegTiming
import Graphiti.Projects.AsyncFifo.components.level6.ReadBank

/-! # `ReadBank`: the lemmas

Facts about the definitions in `components/level6/ReadBank.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.ReadBank
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff

@[drenv] theorem kenv_unpackNext : kenv.find? "unpackNext" = .some ⟨_, unpackNext⟩ := rfl
@[drenv] theorem kenv_fork2 : kenv.find? "fork2" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem kenv_streg : kenv.find? "streg" = .some ⟨_, ReadState.stSpec⟩ := rfl
@[drenv] theorem kenv_forkSt : kenv.find? "forkSt" = .some ⟨_, fork2 (RSt 2)⟩ := rfl
@[drenv] theorem kenv_emptyOf : kenv.find? "emptyOf" = .some ⟨_, emptyOf⟩ := rfl
@[drenv] theorem kenv_busreg : kenv.find? "busreg" = .some ⟨_, BusReg.busSpec⟩ := rfl


@[simp] theorem stOf_length (d : List (RNext 2)) : (stOf d).length = d.length := by simp [stOf]
@[simp] theorem gnextOf_length (d : List (RNext 2)) : (gnextOf d).length = d.length := by
  simp [gnextOf]

theorem stOf_mono {d d' : List (RNext 2)} (h : d <+: d') : stOf d <+: stOf d' := h.map _
theorem gnextOf_mono {d d' : List (RNext 2)} (h : d <+: d') : gnextOf d <+: gnextOf d' :=
  h.map _

theorem stOf_getD (d : List (RNext 2)) (u : Nat) :
    (stOf d).getD u default = (d.getD u default).st := by
  by_cases h : u < d.length
  · simp [stOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [stOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem gnextOf_getD (d : List (RNext 2)) (u : Nat) :
    (gnextOf d).getD u 0#3 = (d.getD u default).gnext := by
  by_cases h : u < d.length
  · simp [gnextOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [gnextOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-! ### The bank's contracts

Each block was proved against its own contract over its own stream; here they are read back in
the bank's terms, where every field of the next-state bus has the bus's own horizon. -/

/-- How far the bank's inputs are known. -/
def bankLen (clk : List Bool) (d : List (RNext 2)) (crn : List Bool) : Nat :=
  min (min clk.length d.length) crn.length

theorem stLen_eq (clk : List Bool) (d : List (RNext 2)) (crn : List Bool) :
    ReadState.stLen clk (stOf d) crn = bankLen clk d crn := by simp [ReadState.stLen, bankLen]

theorem busLen_eq (clk : List Bool) (d : List (RNext 2)) (crn : List Bool) :
    BusReg.busLen clk (gnextOf d) crn = bankLen clk d crn := by simp [BusReg.busLen, bankLen]

/-- The filters the bank needs, at the bank's horizon. -/
structure BankOK (clk : List Bool) (d : List (RNext 2)) (crn : List Bool) (R : Nat) :
    Prop where
  hR : 6 ≤ R
  clear : ClearOK R crn crn.length
  reset : ResetOK (R + 3) clk clk.length
  pulse : PulseOK 3 clk clk.length
  period : ClockOK 12 clk clk.length

variable {clk : List Bool} {d : List (RNext 2)} {crn : List Bool} {R : Nat}

/-- **The state register's contract**, in the bank's terms. -/
theorem bank_st (H : BankOK clk d crn R) {v : List (RSt 2)}
    (hv : v <+: ReadState.stOut clk (stOf d) crn) :
    RegOut 4 1 default clk (fun u => (d.getD u default).st) d.length v := by
  have h := ReadState.stOut_regOut (clk := clk) (d := stOf d) (crn := crn) (R := R) (by have := H.hR; omega)
    (by rw [stLen_eq]; exact H.clear.mono (by unfold bankLen; omega))
    (by rw [stLen_eq]; exact H.reset.mono (by unfold bankLen; omega))
    (by rw [stLen_eq]; exact H.pulse.mono (by unfold bankLen; omega)) hv
  simpa only [stOf_getD, stOf_length] using h

/-- **The Gray pointer register's contract**: glitch-free across an edge, which is what makes it
safe to sample in the other clock domain. -/
theorem bank_gray (H : BankOK clk d crn R)
    (hstable : ∀ e, e < bankLen clk d crn → riseAt clk e = true →
      ∀ u, e - 2 ≤ u → u ≤ e → (d.getD u default).gnext = (d.getD e default).gnext)
    {v : List (BitVec 3)} (hv : v <+: BusReg.busOut clk (gnextOf d) crn) :
    BusRegOut 4 1 clk (fun u => (d.getD u default).gnext) d.length v := by
  have h := BusReg.busOut_busRegOut (clk := clk) (d := gnextOf d) (crn := crn) (R := R) (by have := H.hR; omega)
    (by rw [busLen_eq]; exact H.clear.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.reset.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.pulse.mono (by unfold bankLen; omega))
    (by
      intro e h1 h2 u h3 h4
      rw [busLen_eq] at h1
      rw [gnextOf_getD, gnextOf_getD]
      exact hstable e h1 h2 u h3 h4)
    (by
      intro e h1 h2 e' h3
      rw [busLen_eq] at h1
      have := H.period e' e (by have := h3.1; omega) (by unfold bankLen at h1; omega) h3.2.1 h2
      omega) hv
  simpa only [gnextOf_getD, gnextOf_length] using h

/-- **The Gray pointer register's value contract**, which needs no stability assumption: a
violated edge is forgotten at the next clean one.  Only the glitch-free clause needs the
history, and it carries it itself (`Contracts.CleanEdges`). -/
theorem bank_gray_val (H : BankOK clk d crn R) {v : List (BitVec 3)}
    (hv : v <+: BusReg.busOut clk (gnextOf d) crn) :
    RegOut 4 1 0#3 clk (fun u => (d.getD u default).gnext) d.length v := by
  have h := BusReg.busOut_regOut (clk := clk) (d := gnextOf d) (crn := crn) (R := R)
    (by have := H.hR; omega)
    (by rw [busLen_eq]; exact H.clear.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.reset.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.pulse.mono (by unfold bankLen; omega)) hv
  simpa only [gnextOf_getD, gnextOf_length] using h

/-! ### The contracts, per instant

The block files prove their contracts over a block's whole known history: the filters hold
everywhere, so the contract holds everywhere.  What `WriteBank.bankSpec` asks for is the per-instant
form --- at each instant, under the filters *before* that instant --- because that is the
discipline the domains keep, and a violation at one instant must not excuse the circuit at an
earlier one.

A netlist is causal, so the two are the same statement, and the passage from one to the other is
purely a matter of which inputs the whole-history theorem is applied to.  To read a contract at
`t`, apply it to the inputs **cut at `t`**: the cut circuit computes the same value at `t`, the
filters over the cut history are exactly the filters before `t`, and every block of the bank
reports exactly one instant past its inputs, so the cut circuit still reaches `t`. -/

section PerInstant

variable {t : Nat}

/-- Cutting the bank's inputs at `t` leaves a block whose horizon is exactly `t`. -/
theorem bankLen_take (h : t ≤ bankLen clk d crn) :
    bankLen (clk.take t) (d.take t) (crn.take t) = t := by
  unfold bankLen at h ⊢
  rw [List.length_take, List.length_take, List.length_take]
  omega

/-- ... and the filters over the cut history are the filters before `t`. -/
theorem bankOK_take (hR : 6 ≤ R) (h : t ≤ bankLen clk d crn)
    (G : GateOK 12 3 (R + 3) R clk crn t) : BankOK (clk.take t) (d.take t) (crn.take t) R := by
  have hc : t ≤ clk.length := by unfold bankLen at h; omega
  have hr : t ≤ crn.length := by unfold bankLen at h; omega
  have lc : (clk.take t).length = t := by rw [List.length_take]; omega
  have lr : (crn.take t).length = t := by rw [List.length_take]; omega
  exact { hR := hR
          clear := by rw [lr]; exact ClearOK.congr (List.take_prefix _ _) (by omega) G.clear
          reset := by rw [lc]; exact ResetOK.congr (List.take_prefix _ _) (by omega) G.reset
          pulse := by rw [lc]; exact PulseOK.congr (List.take_prefix _ _) (by omega) G.pulse
          period := by rw [lc]; exact ClockOK.congr (List.take_prefix _ _) (by omega) G.period }

theorem take_getD_st (u : Nat) (hu : u < (d.take t).length) :
    ((d.take t).getD u default).st = (d.getD u default).st := by
  rw [(List.take_prefix t d).getD_eq_left hu]

theorem take_getD_gnext (u : Nat) (hu : u < (d.take t).length) :
    ((d.take t).getD u default).gnext = (d.getD u default).gnext := by
  rw [(List.take_prefix t d).getD_eq_left hu]

/-- **The state register's contract, per instant.** -/
theorem bank_stG (hR : 6 ≤ R) {v : List (RSt 2)} (hv : v <+: ReadState.stOut clk (stOf d) crn) :
    RegOutG 4 1 default (GateOK 12 3 (R + 3) R clk crn) clk (fun u => (d.getD u default).st)
      d.length (bankLen clk d crn) v := by
  have hl := hv.length_le
  rw [ReadState.stOut_length, stLen_eq] at hl
  refine ⟨hl, fun t ht G => ?_⟩
  have htb : t ≤ bankLen clk d crn := by omega
  have hlt := bankLen_take (d := d) htb
  have hcut := bank_st (bankOK_take hR htb G)
    (v := ReadState.stOut (clk.take t) (stOf (d.take t)) (crn.take t)) List.prefix_rfl
  have hcl : (ReadState.stOut (clk.take t) (stOf (d.take t)) (crn.take t)).length = t + 1 := by
    rw [ReadState.stOut_length, stLen_eq, hlt]
  have hp : ReadState.stOut (clk.take t) (stOf (d.take t)) (crn.take t) <+: ReadState.stOut clk (stOf d) crn :=
    ReadState.stOut_mono (List.take_prefix _ _) (stOf_mono (List.take_prefix _ _)) (List.take_prefix _ _)
  have hct : t ≤ clk.length := by unfold bankLen at htb; omega
  refine RegAt.congr_out ?_ ((hcut.2 t (by omega)).mono (List.take_prefix _ _) take_getD_st
    (by rw [List.length_take]; unfold bankLen at htb; omega)
    (by rw [List.length_take]; omega) (by rw [List.length_take]; unfold bankLen at htb; omega))
  rw [hp.getD_eq_left (by omega), hv.getD_eq_left ht]

/-- **The Gray pointer register's contract, per instant.**  The stability the glitch-free clause
needs is the clause's own `CleanEdges`: cut at `t`, it is exactly the whole-history hypothesis
the block file asks for. -/
theorem bank_grayG (hR : 6 ≤ R) {v : List (BitVec 3)}
    (hv : v <+: BusReg.busOut clk (gnextOf d) crn) :
    BusRegOutG 4 1 (GateOK 12 3 (R + 3) R clk crn) clk (fun u => (d.getD u default).gnext)
      d.length (bankLen clk d crn) v := by
  have hl := hv.length_le
  rw [BusReg.busOut_length, busLen_eq] at hl
  have hpre : ∀ t, BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)
      <+: BusReg.busOut clk (gnextOf d) crn :=
    fun t => BusReg.busOut_mono (List.take_prefix _ _) (gnextOf_mono (List.take_prefix _ _))
      (List.take_prefix _ _)
  have hcl : ∀ t, t ≤ bankLen clk d crn →
      (BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)).length = t + 1 := by
    intro t htb; rw [BusReg.busOut_length, busLen_eq, bankLen_take (d := d) htb]
  refine ⟨⟨hl, fun t ht G => ?_⟩, fun t ht G => ?_⟩
  · have htb : t ≤ bankLen clk d crn := by omega
    have hcut := bank_gray_val (bankOK_take hR htb G)
      (v := BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)) List.prefix_rfl
    refine RegAt.congr_out ?_ ((hcut.2 t (by rw [hcl t htb]; omega)).mono (List.take_prefix _ _)
      take_getD_gnext (by rw [List.length_take]; unfold bankLen at htb; omega)
      (by rw [List.length_take]; unfold bankLen at htb; omega)
      (by rw [List.length_take]; unfold bankLen at htb; omega))
    rw [(hpre t).getD_eq_left (by rw [hcl t htb]; omega), hv.getD_eq_left ht]
  · intro hclean
    have htb : t ≤ bankLen clk d crn := by omega
    have hlk : t ≤ clk.length := by unfold bankLen at htb; omega
    have hld : t ≤ d.length := by unfold bankLen at htb; omega
    have hst : ∀ e, e < bankLen (clk.take t) (d.take t) (crn.take t) →
        riseAt (clk.take t) e = true → ∀ u, e - 2 ≤ u → u ≤ e →
          ((d.take t).getD u default).gnext = ((d.take t).getD e default).gnext := by
      intro e h1 h2 u h3 h4
      rw [bankLen_take (d := d) htb] at h1
      have hce : riseAt clk e = true := by
        rw [← riseAt_prefix (List.take_prefix t clk) (by rw [List.length_take]; omega)]
        exact h2
      have hs := hclean e h1 hce
      rw [take_getD_gnext u (by rw [List.length_take]; omega),
        take_getD_gnext e (by rw [List.length_take]; omega)]
      exact hs.2 u h3 h4
    have hcut := bank_gray (bankOK_take hR htb G) hst
      (v := BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)) List.prefix_rfl
    have hval : ∀ u, u ≤ t →
        (BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)).getD u 0#3 = v.getD u 0#3 := by
      intro u hu
      rw [(hpre t).getD_eq_left (by rw [hcl t htb]; omega), hv.getD_eq_left (by omega)]
    exact BusWinAt.congr_out hval ((hcut.2 t (by rw [hcl t htb]; omega)).mono (List.take_prefix _ _)
      take_getD_gnext (by rw [List.length_take]; omega) (by rw [List.length_take]; omega)
      (by rw [List.length_take]; omega)) hclean
end PerInstant

seal kenv in
def_module bankT : Type :=
  [T| bankLowered, kenv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal kenv in
def_module bankNetlist : StringModule bankT :=
  [e| bankLowered, kenv.find? ]


/-! ### The specification -/

/-- The bank as a single block: the state register, the Gray pointer register and the `empty`
bit, over the fields of the next-state bus. -/
@[drcomponents]
def bankExact : StringModule (List Bool × List (RNext 2) × List Bool × List (RSt 2) ×
    List Bool × List (BitVec 3)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (RNext 2), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              ].toAssocList
    outputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.2.2.2.1 <+: v ∧
                    v <+: ReadState.stOut s.1 (stOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
               , (↑"empty", ⟨List Bool, fun s v s' => s.2.2.2.2.1 <+: v ∧
                    v <+: (ReadState.stOut s.1 (stOf s.2.1) s.2.2.1).map (·.empty) ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩)
               , (↑"gray", ⟨List (BitVec 3), fun s v s' => s.2.2.2.2.2 <+: v ∧
                    v <+: BusReg.busOut s.1 (gnextOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v)⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], []) }

instance : MatchInterface bankNetlist bankExact := by
  dsimp [bankNetlist, bankExact]
  solve_match_interface

/-! ### The invariant -/

structure Wf (stF_in : List (RSt 2)) (crF_in : List Bool) (stR_clk : List Bool) (stR_d : List (RSt 2)) (stR_clrn : List Bool) (clkF_in : List Bool) (unpN_d : List (RNext 2)) (emptyA_q : List (RSt 2)) (grR_clk : List Bool) (grR_d : List (BitVec 3)) (grR_clrn : List Bool) (grR_qh : List (BitVec 3)) (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) : Prop where
  e_clk : clkF_in = s.1
end Graphiti.AsyncFifo.ReadBank