/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.StReg
import Graphiti.Projects.AsyncFifo.BusReg
import Graphiti.Projects.AsyncFifo.Mem
import Graphiti.Projects.AsyncFifo.StRegTiming
import Graphiti.Projects.AsyncFifo.BusRegTiming

/-!
# The write domain's register bank

`Timed.regBank` is the write domain's state: a seven-bit state register, the three-bit Gray
pointer that crosses into the read domain, the `full` flag (a projection of the state), and the
four-entry register file.  This file wires the three blocks together and unpacks the next-state
bus that feeds them.

The bank has one port the register-level model does not: the clear.  That is the finding of
`Dff.lean` working its way up -- a netlist of gates has no defined state until something puts
it there -- and it is why the write domain, and in the end the FIFO, need a reset input of
their own.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.Bank

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff

/-! ### The next-state bus and its fields -/

def stOf (d : List (WNext Bool 2)) : List (WSt 2) := d.map (·.st)
def gnextOf (d : List (WNext Bool 2)) : List (BitVec 3) := d.map (·.gnext)
def weOf (d : List (WNext Bool 2)) : List Bool := d.map (·.we)
def addrOf (d : List (WNext Bool 2)) : List (BitVec 2) := d.map (·.addr)
def dataOf (d : List (WNext Bool 2)) : List Bool := d.map (·.data)

@[simp] theorem stOf_length (d : List (WNext Bool 2)) : (stOf d).length = d.length := by simp [stOf]
@[simp] theorem gnextOf_length (d : List (WNext Bool 2)) : (gnextOf d).length = d.length := by
  simp [gnextOf]
@[simp] theorem weOf_length (d : List (WNext Bool 2)) : (weOf d).length = d.length := by simp [weOf]
@[simp] theorem addrOf_length (d : List (WNext Bool 2)) : (addrOf d).length = d.length := by
  simp [addrOf]
@[simp] theorem dataOf_length (d : List (WNext Bool 2)) : (dataOf d).length = d.length := by
  simp [dataOf]

theorem stOf_mono {d d' : List (WNext Bool 2)} (h : d <+: d') : stOf d <+: stOf d' := h.map _
theorem gnextOf_mono {d d' : List (WNext Bool 2)} (h : d <+: d') : gnextOf d <+: gnextOf d' :=
  h.map _
theorem weOf_mono {d d' : List (WNext Bool 2)} (h : d <+: d') : weOf d <+: weOf d' := h.map _
theorem addrOf_mono {d d' : List (WNext Bool 2)} (h : d <+: d') : addrOf d <+: addrOf d' := h.map _
theorem dataOf_mono {d d' : List (WNext Bool 2)} (h : d <+: d') : dataOf d <+: dataOf d' := h.map _

theorem stOf_getD (d : List (WNext Bool 2)) (u : Nat) :
    (stOf d).getD u default = (d.getD u default).st := by
  by_cases h : u < d.length
  · simp [stOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [stOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem gnextOf_getD (d : List (WNext Bool 2)) (u : Nat) :
    (gnextOf d).getD u 0#3 = (d.getD u default).gnext := by
  by_cases h : u < d.length
  · simp [gnextOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [gnextOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem weOf_getD (d : List (WNext Bool 2)) (u : Nat) :
    (weOf d).getD u false = (d.getD u default).we := by
  by_cases h : u < d.length
  · simp [weOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [weOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem addrOf_getD (d : List (WNext Bool 2)) (u : Nat) :
    (addrOf d).getD u 0#2 = (d.getD u default).addr := by
  by_cases h : u < d.length
  · simp [addrOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [addrOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem dataOf_getD (d : List (WNext Bool 2)) (u : Nat) :
    (dataOf d).getD u false = (d.getD u default).data := by
  by_cases h : u < d.length
  · simp [dataOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [dataOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- Split the next-state bus into the five streams the bank's blocks read. -/
@[drcomponents]
def unpackNext : StringModule (List (WNext Bool 2)) :=
  { inputs := [ (↑"d", ⟨List (WNext Bool 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"st", ⟨List (WSt 2), fun s v s' => s' = s ∧ v = stOf s⟩)
               , (↑"gnext", ⟨List (BitVec 3), fun s v s' => s' = s ∧ v = gnextOf s⟩)
               , (↑"we", ⟨List Bool, fun s v s' => s' = s ∧ v = weOf s⟩)
               , (↑"addr", ⟨List (BitVec 2), fun s v s' => s' = s ∧ v = addrOf s⟩)
               , (↑"data", ⟨List Bool, fun s v s' => s' = s ∧ v = dataOf s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The `full` flag is a bit of the state register. -/
@[drcomponents]
def fullOf : StringModule (List (WSt 2)) :=
  { inputs := [ (↑"q", ⟨List (WSt 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"full", ⟨List Bool, fun s v s' => s' = s ∧ v = s.map (·.full)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-! ### The bank's contracts

Each block was proved against its own contract over its own stream; here they are read back in
the bank's terms, where every field of the next-state bus has the bus's own horizon. -/

/-- How far the bank's inputs are known. -/
def bankLen (clk : List Bool) (d : List (WNext Bool 2)) (crn : List Bool) : Nat :=
  min (min clk.length d.length) crn.length

theorem stLen_eq (clk : List Bool) (d : List (WNext Bool 2)) (crn : List Bool) :
    StReg.stLen clk (stOf d) crn = bankLen clk d crn := by simp [StReg.stLen, bankLen]

theorem busLen_eq (clk : List Bool) (d : List (WNext Bool 2)) (crn : List Bool) :
    BusReg.busLen clk (gnextOf d) crn = bankLen clk d crn := by simp [BusReg.busLen, bankLen]

theorem memLen_eq (clk : List Bool) (d : List (WNext Bool 2)) (crn : List Bool) :
    Mem.memLen clk (weOf d) (addrOf d) (dataOf d) crn = bankLen clk d crn := by
  simp [Mem.memLen, bankLen]

/-- The filters the bank needs, at the bank's horizon. -/
structure BankOK (clk : List Bool) (d : List (WNext Bool 2)) (crn : List Bool) (R : Nat) :
    Prop where
  hR : 6 ≤ R
  clear : ClearOK R crn crn.length
  reset : ResetOK (R + 3) clk clk.length
  pulse : PulseOK 3 clk clk.length
  period : ClockOK 12 clk clk.length

variable {clk : List Bool} {d : List (WNext Bool 2)} {crn : List Bool} {R : Nat}

/-- **The state register's contract**, in the bank's terms. -/
theorem bank_st (H : BankOK clk d crn R) {v : List (WSt 2)}
    (hv : v <+: StReg.stOut clk (stOf d) crn) :
    RegOut 4 1 default clk (fun u => (d.getD u default).st) d.length v := by
  have h := StReg.stOut_regOut (clk := clk) (d := stOf d) (crn := crn) (R := R) (by have := H.hR; omega)
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
history, and it carries it itself (`Timed.CleanEdges`). -/
theorem bank_gray_val (H : BankOK clk d crn R) {v : List (BitVec 3)}
    (hv : v <+: BusReg.busOut clk (gnextOf d) crn) :
    RegOut 4 1 0#3 clk (fun u => (d.getD u default).gnext) d.length v := by
  have h := BusReg.busOut_regOut (clk := clk) (d := gnextOf d) (crn := crn) (R := R)
    (by have := H.hR; omega)
    (by rw [busLen_eq]; exact H.clear.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.reset.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.pulse.mono (by unfold bankLen; omega)) hv
  simpa only [gnextOf_getD, gnextOf_length] using h

/-- **The register file's contract**. -/
theorem bank_mem (H : BankOK clk d crn R) {v : List (BitVec 2 → Bool)}
    (hv : v <+: Mem.memOut clk (weOf d) (addrOf d) (dataOf d) crn) :
    MemOut 4 8 clk (fun u => (d.getD u default).we) (fun u => (d.getD u default).addr)
      (fun u => (d.getD u default).data) d.length v := by
  have h := Mem.memOut_memOut (clk := clk) (we := weOf d) (addr := addrOf d) (data := dataOf d)
    (crn := crn) (R := R)
    ⟨H.hR, H.clear, H.reset, H.pulse, H.period⟩ hv
  rw [memLen_eq] at h
  simp only [weOf_getD, addrOf_getD, dataOf_getD] at h
  exact h.mono List.prefix_rfl (by unfold bankLen; omega) (fun u _ => rfl) (fun u _ => rfl)
    (fun u _ => rfl)

/-- **The `full` flag** is a bit of the state register. -/
theorem bank_full (H : BankOK clk d crn R) {q : List (WSt 2)}
    (hq : q <+: StReg.stOut clk (stOf d) crn) :
    ∃ p, RegOut 4 1 default clk (fun u => (d.getD u default).st) d.length p ∧
      q.map (·.full) = p.map (·.full) :=
  ⟨q, bank_st H hq, rfl⟩

/-! ### The contracts, per instant

The block files prove their contracts over a block's whole known history: the filters hold
everywhere, so the contract holds everywhere.  What `Timed.regBank` asks for is the per-instant
form --- at each instant, under the filters *before* that instant --- because that is the
discipline the domains keep, and a violation at one instant must not excuse the circuit at an
earlier one.

A netlist is causal, so the two are the same statement, and the passage from one to the other is
purely a matter of which inputs the whole-history theorem is applied to.  To read a contract at
`t`, apply it to the inputs **cut at `t`**: the cut circuit computes the same value at `t`, the
filters over the cut history are exactly the filters before `t`, and every block of the bank
reports exactly one instant past its inputs, so the cut circuit still reaches `t`.  (That last
point is why `Mem.memOut` reports against the file's own inputs rather than against its cells:
a block that reported short would not reach `t` after the cut.) -/

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
theorem bank_stG (hR : 6 ≤ R) {v : List (WSt 2)} (hv : v <+: StReg.stOut clk (stOf d) crn) :
    RegOutG 4 1 default (GateOK 12 3 (R + 3) R clk crn) clk (fun u => (d.getD u default).st)
      d.length (bankLen clk d crn) v := by
  have hl := hv.length_le
  rw [StReg.stOut_length, stLen_eq] at hl
  refine ⟨hl, fun t ht G => ?_⟩
  have htb : t ≤ bankLen clk d crn := by omega
  have hlt := bankLen_take (d := d) htb
  have hcut := bank_st (bankOK_take hR htb G)
    (v := StReg.stOut (clk.take t) (stOf (d.take t)) (crn.take t)) List.prefix_rfl
  have hcl : (StReg.stOut (clk.take t) (stOf (d.take t)) (crn.take t)).length = t + 1 := by
    rw [StReg.stOut_length, stLen_eq, hlt]
  have hp : StReg.stOut (clk.take t) (stOf (d.take t)) (crn.take t) <+: StReg.stOut clk (stOf d) crn :=
    StReg.stOut_mono (List.take_prefix _ _) (stOf_mono (List.take_prefix _ _)) (List.take_prefix _ _)
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

/-- **The register file's contract, per instant.** -/
theorem bank_memG (hR : 6 ≤ R) {v : List (BitVec 2 → Bool)}
    (hv : v <+: Mem.memOut clk (weOf d) (addrOf d) (dataOf d) crn) :
    MemOutG 4 8 (GateOK 12 3 (R + 3) R clk crn) clk (fun u => (d.getD u default).we)
      (fun u => (d.getD u default).addr) (fun u => (d.getD u default).data) d.length
      (bankLen clk d crn) v := by
  have hl := hv.length_le
  rw [Mem.memOut_length, memLen_eq] at hl
  refine ⟨hl, fun t ht G => ?_⟩
  have htb : t ≤ bankLen clk d crn := by omega
  have hlt := bankLen_take (d := d) htb
  have hcut := bank_mem (bankOK_take hR htb G)
    (v := Mem.memOut (clk.take t) (weOf (d.take t)) (addrOf (d.take t)) (dataOf (d.take t)) (crn.take t))
    List.prefix_rfl
  have hcl : (Mem.memOut (clk.take t) (weOf (d.take t)) (addrOf (d.take t)) (dataOf (d.take t))
      (crn.take t)).length = t + 1 := by rw [Mem.memOut_length, memLen_eq, hlt]
  have hp : Mem.memOut (clk.take t) (weOf (d.take t)) (addrOf (d.take t)) (dataOf (d.take t)) (crn.take t)
      <+: Mem.memOut clk (weOf d) (addrOf d) (dataOf d) crn :=
    Mem.memOut_mono (List.take_prefix _ _) (weOf_mono (List.take_prefix _ _))
      (addrOf_mono (List.take_prefix _ _)) (dataOf_mono (List.take_prefix _ _)) (List.take_prefix _ _)
  have hdlen : t ≤ (d.take t).length := by rw [List.length_take]; unfold bankLen at htb; omega
  refine MemAt.congr_out ?_ ((hcut.2 t (by omega)).mono (List.take_prefix _ _)
    (by rw [List.length_take]; omega)
    (fun u hu => by rw [(List.take_prefix t d).getD_eq_left hu])
    (fun u hu => by rw [(List.take_prefix t d).getD_eq_left hu])
    (fun u hu => by rw [(List.take_prefix t d).getD_eq_left hu])
    (by rw [List.length_take]; unfold bankLen at htb; omega) hdlen)
  rw [hp.getD_eq_left (by omega), hv.getD_eq_left ht]

/-- **The `full` flag, per instant.** -/
theorem bank_fullG (hR : 6 ≤ R) {q : List (WSt 2)} (hq : q <+: StReg.stOut clk (stOf d) crn) :
    ∃ p, RegOutG 4 1 default (GateOK 12 3 (R + 3) R clk crn) clk (fun u => (d.getD u default).st)
      d.length (bankLen clk d crn) p ∧ q.map (·.full) = p.map (·.full) :=
  ⟨q, bank_stG hR hq, rfl⟩

end PerInstant

/-! ### The netlist -/

def bankGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    st [type="io"];
    full [type="io"];
    gray [type="io"];
    mem [type="io"];

    unpN [type="unpackNext", typeImp=$(⟨_, unpackNext⟩)];
    clkF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    crF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    stR [type="streg", typeImp=$(⟨_, StReg.stSpec⟩)];
    stF [type="forkSt", typeImp=$(⟨_, Timed.fork2 (WSt 2)⟩)];
    fullA [type="fullOf", typeImp=$(⟨_, fullOf⟩)];
    grR [type="busreg", typeImp=$(⟨_, BusReg.busSpec⟩)];
    memB [type="memory", typeImp=$(⟨_, Mem.memSpec⟩)];

    clk -> clkF [to="in"];
    d -> unpN [to="d"];
    clrn -> crF [to="in"];

    clkF -> stR [from="out1", to="clk"];
    clkF -> grR [from="out2", to="clk"];
    clkF -> memB [from="out3", to="clk"];
    crF -> stR [from="out1", to="clrn"];
    crF -> grR [from="out2", to="clrn"];
    crF -> memB [from="out3", to="clrn"];
    unpN -> stR [from="st", to="d"];
    unpN -> grR [from="gnext", to="d"];
    unpN -> memB [from="we", to="we"];
    unpN -> memB [from="addr", to="addr"];
    unpN -> memB [from="data", to="data"];
    stR -> stF [from="q", to="in"];
    stF -> fullA [from="out2", to="q"];

    stF -> st [from="out1"];
    fullA -> full [from="full"];
    grR -> gray [from="q"];
    memB -> mem [from="mem"];
  ]

@[drunfold_defs]
def bankLowered := bankGraph.1.lower_TR |>.get rfl

def kenv := bankGraph.2

@[drenv] theorem kenv_unpackNext : kenv.find? "unpackNext" = .some ⟨_, unpackNext⟩ := rfl
@[drenv] theorem kenv_fork3 : kenv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem kenv_streg : kenv.find? "streg" = .some ⟨_, StReg.stSpec⟩ := rfl
@[drenv] theorem kenv_forkSt : kenv.find? "forkSt" = .some ⟨_, Timed.fork2 (WSt 2)⟩ := rfl
@[drenv] theorem kenv_fullOf : kenv.find? "fullOf" = .some ⟨_, fullOf⟩ := rfl
@[drenv] theorem kenv_busreg : kenv.find? "busreg" = .some ⟨_, BusReg.busSpec⟩ := rfl
@[drenv] theorem kenv_memory : kenv.find? "memory" = .some ⟨_, Mem.memSpec⟩ := rfl

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

-- HEADER_END (everything below is generated by gen/gen_bank.py)

/-! ### The specification -/

/-- The bank as a single block: the state register, the Gray pointer register, the `full` bit
and the register file, over the fields of the next-state bus. -/
@[drcomponents]
def bankSpec : StringModule (List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) ×
    List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (WNext Bool 2), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              ].toAssocList
    outputs := [ (↑"st", ⟨List (WSt 2), fun s v s' => s.2.2.2.1 <+: v ∧
                    v <+: StReg.stOut s.1 (stOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
               , (↑"full", ⟨List Bool, fun s v s' => s.2.2.2.2.1 <+: v ∧
                    v <+: (StReg.stOut s.1 (stOf s.2.1) s.2.2.1).map (·.full) ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩)
               , (↑"gray", ⟨List (BitVec 3), fun s v s' => s.2.2.2.2.2.1 <+: v ∧
                    v <+: BusReg.busOut s.1 (gnextOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v, s.2.2.2.2.2.2)⟩)
               , (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2.2.2.2.2.2 <+: v ∧
                    v <+: Mem.memOut s.1 (weOf s.2.1) (addrOf s.2.1) (dataOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, v)⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], [], []) }

instance : MatchInterface bankNetlist bankSpec := by
  dsimp [bankNetlist, bankSpec]
  solve_match_interface

/-! ### The invariant -/

structure Wf (memB_clk : List Bool) (memB_we : List Bool) (memB_addr : List (BitVec 2)) (memB_data : List Bool) (memB_clrn : List Bool) (memB_qh : List (BitVec 2 → Bool)) (stF_in : List (WSt 2)) (crF_in : List Bool) (stR_clk : List Bool) (stR_d : List (WSt 2)) (stR_clrn : List Bool) (fullA_q : List (WSt 2)) (clkF_in : List Bool) (unpN_d : List (WNext Bool 2)) (grR_clk : List Bool) (grR_d : List (BitVec 3)) (grR_clrn : List Bool) (grR_qh : List (BitVec 3)) (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) : Prop where
  e_clk : clkF_in = s.1
  e_d : unpN_d = s.2.1
  e_crn : crF_in = s.2.2.1
  e_grh : grR_qh = s.2.2.2.2.2.1
  e_mmh : memB_qh = s.2.2.2.2.2.2
  h_st : s.2.2.2.1 <+: stF_in
  h_full : s.2.2.2.2.1 <+: fullA_q.map (·.full)
  w_memB_clk : memB_clk <+: clkF_in
  w_memB_we : memB_we <+: weOf unpN_d
  w_memB_addr : memB_addr <+: addrOf unpN_d
  w_memB_data : memB_data <+: dataOf unpN_d
  w_memB_clrn : memB_clrn <+: crF_in
  w_stF_in : stF_in <+: StReg.stOut stR_clk stR_d stR_clrn
  w_stR_clk : stR_clk <+: clkF_in
  w_stR_d : stR_d <+: stOf unpN_d
  w_stR_clrn : stR_clrn <+: crF_in
  w_fullA_q : fullA_q <+: stF_in
  w_grR_clk : grR_clk <+: clkF_in
  w_grR_d : grR_d <+: gnextOf unpN_d
  w_grR_clrn : grR_clrn <+: crF_in

def ψ (i : bankT) (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) : Prop :=
  Wf i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2.1 i.1.2.2.2.2.1 i.1.2.2.2.2.2 i.2.1 i.2.2.1 i.2.2.2.1.1 i.2.2.2.1.2.1 i.2.2.2.1.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2.1 i.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2 s

theorem Wf.init : Wf [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] ([], [], [], [], [], [], []) :=
  ⟨rfl, rfl, rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩

section SpecRules
variable (sp : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (bankSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (WNext Bool 2)) (h : sp.2.1 ⊏ v) :
    (bankSpec.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (bankSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_st (v : List (WSt 2)) (h1 : sp.2.2.2.1 <+: v)
    (h2 : v <+: StReg.stOut sp.1 (stOf sp.2.1) sp.2.2.1) :
    (bankSpec.outputs.getIO ↑"st").2 sp v (sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_full (v : List Bool) (h1 : sp.2.2.2.2.1 <+: v)
    (h2 : v <+: (StReg.stOut sp.1 (stOf sp.2.1) sp.2.2.1).map (·.full)) :
    (bankSpec.outputs.getIO ↑"full").2 sp v (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_gray (v : List (BitVec 3)) (h1 : sp.2.2.2.2.2.1 <+: v)
    (h2 : v <+: BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1) :
    (bankSpec.outputs.getIO ↑"gray").2 sp v (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v, sp.2.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_mem (v : List (BitVec 2 → Bool)) (h1 : sp.2.2.2.2.2.2 <+: v)
    (h2 : v <+: Mem.memOut sp.1 (weOf sp.2.1) (addrOf sp.2.1) (dataOf sp.2.1) sp.2.2.1) :
    (bankSpec.outputs.getIO ↑"mem").2 sp v (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, sp.2.2.2.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

end SpecRules

section Cases
variable {memB_clk : List Bool} {memB_we : List Bool} {memB_addr : List (BitVec 2)} {memB_data : List Bool} {memB_clrn : List Bool} {memB_qh : List (BitVec 2 → Bool)} {stF_in : List (WSt 2)} {crF_in : List Bool} {stR_clk : List Bool} {stR_d : List (WSt 2)} {stR_clrn : List Bool} {fullA_q : List (WSt 2)} {clkF_in : List Bool} {unpN_d : List (WNext Bool 2)} {grR_clk : List Bool} {grR_d : List (BitVec 3)} {grR_clrn : List Bool} {grR_qh : List (BitVec 3)} {sp : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)}
  (Hψ : Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp)
include Hψ

theorem in_clk (v : List Bool) (h : clkF_in ⊏ v) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q (v) unpN_d grR_clk grR_d grR_clrn grR_qh (v, sp.2) := by
  have hm : clkF_in <+: v := h.isPrefix
  exact { e_clk := rfl
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk.trans hm
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk.trans hm
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk.trans hm
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem in_d (v : List (WNext Bool 2)) (h : unpN_d ⊏ v) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in (v) grR_clk grR_d grR_clrn grR_qh (sp.1, v, sp.2.2) := by
  have hm : unpN_d <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := rfl
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we.trans (weOf_mono hm)
          w_memB_addr := Hψ.w_memB_addr.trans (addrOf_mono hm)
          w_memB_data := Hψ.w_memB_data.trans (dataOf_mono hm)
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d.trans (stOf_mono hm)
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d.trans (gnextOf_mono hm)
          w_grR_clrn := Hψ.w_grR_clrn }

theorem in_clrn (v : List Bool) (h : crF_in ⊏ v) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in (v) stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh (sp.1, sp.2.1, v, sp.2.2.2) := by
  have hm : crF_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := rfl
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn.trans hm
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn.trans hm
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn.trans hm }

theorem int_0 (_h : stR_clk ⊏ clkF_in) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in (clkF_in) stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in.trans (StReg.stOut_mono Hψ.w_stR_clk List.prefix_rfl List.prefix_rfl)
          w_stR_clk := List.prefix_rfl
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_1 (_h : grR_clk ⊏ clkF_in) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d (clkF_in) grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := List.prefix_rfl
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_2 (_h : memB_clk ⊏ clkF_in) :
    Wf (clkF_in) memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := List.prefix_rfl
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_3 (_h : stR_clrn ⊏ crF_in) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d (crF_in) fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in.trans (StReg.stOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_stR_clrn)
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := List.prefix_rfl
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_4 (_h : grR_clrn ⊏ crF_in) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d (crF_in) grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := List.prefix_rfl }

theorem int_5 (_h : memB_clrn ⊏ crF_in) :
    Wf memB_clk memB_we memB_addr memB_data (crF_in) memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := List.prefix_rfl
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_6 (_h : stR_d ⊏ stOf unpN_d) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk (stOf unpN_d) stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in.trans (StReg.stOut_mono List.prefix_rfl Hψ.w_stR_d List.prefix_rfl)
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := List.prefix_rfl
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_7 (_h : grR_d ⊏ gnextOf unpN_d) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk (gnextOf unpN_d) grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := List.prefix_rfl
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_8 (_h : memB_we ⊏ weOf unpN_d) :
    Wf memB_clk (weOf unpN_d) memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := List.prefix_rfl
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_9 (_h : memB_addr ⊏ addrOf unpN_d) :
    Wf memB_clk memB_we (addrOf unpN_d) memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := List.prefix_rfl
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_10 (_h : memB_data ⊏ dataOf unpN_d) :
    Wf memB_clk memB_we memB_addr (dataOf unpN_d) memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := List.prefix_rfl
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_11 {out : List (WSt 2)} (_h : stF_in ⊏ out) (hout : out <+: StReg.stOut stR_clk stR_d stR_clrn) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh (out) crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st.trans (_h.isPrefix)
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := hout
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q.trans (_h.isPrefix)
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_12 (_h : fullA_q ⊏ stF_in) :
    Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn (stF_in) clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full.trans (Hψ.w_fullA_q.map _)
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := List.prefix_rfl
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

/-- Each block sees prefixes of the bank's own inputs. -/
theorem out_st : stF_in <+: StReg.stOut sp.1 (stOf sp.2.1) sp.2.2.1 :=
  Hψ.w_stF_in.trans (StReg.stOut_mono (Hψ.w_stR_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
    (Hψ.w_stR_d.trans (stOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
    (Hψ.w_stR_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))

theorem out_full : fullA_q.map (·.full) <+: (StReg.stOut sp.1 (stOf sp.2.1) sp.2.2.1).map (·.full) :=
  (Hψ.w_fullA_q.trans (out_st Hψ)).map _

theorem out_gray {v : List (BitVec 3)} (h : v <+: BusReg.busOut grR_clk grR_d grR_clrn) :
    v <+: BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1 :=
  h.trans (BusReg.busOut_mono (Hψ.w_grR_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
    (Hψ.w_grR_d.trans (gnextOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
    (Hψ.w_grR_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))

theorem out_mem {v : List (BitVec 2 → Bool)}
    (h : v <+: Mem.memOut memB_clk memB_we memB_addr memB_data memB_clrn) :
    v <+: Mem.memOut sp.1 (weOf sp.2.1) (addrOf sp.2.1) (dataOf sp.2.1) sp.2.2.1 :=
  h.trans (Mem.memOut_mono (Hψ.w_memB_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
    (Hψ.w_memB_we.trans (weOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
    (Hψ.w_memB_addr.trans (addrOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
    (Hψ.w_memB_data.trans (dataOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
    (Hψ.w_memB_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))

/-! What it has reported it has reported: two ports leave through an adapter, which keeps
no record, so the block keeps it; the other two leave through a register that keeps its
own, and the block's record is that one. -/

theorem out_st_wf : Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh (sp.1, sp.2.1, sp.2.2.1, stF_in, sp.2.2.2.2) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := List.prefix_rfl
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem out_full_wf : Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, fullA_q.map (·.full), sp.2.2.2.2.2) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := List.prefix_rfl
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem out_gray_wf {v : List (BitVec 3)} : Wf memB_clk memB_we memB_addr memB_data memB_clrn memB_qh stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn (v) (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v, sp.2.2.2.2.2.2) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := rfl
          e_mmh := Hψ.e_mmh
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem out_mem_wf {v : List (BitVec 2 → Bool)} : Wf memB_clk memB_we memB_addr memB_data memB_clrn (v) stF_in crF_in stR_clk stR_d stR_clrn fullA_q clkF_in unpN_d grR_clk grR_d grR_clrn grR_qh (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, sp.2.2.2.2.2.1, v) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          e_mmh := rfl
          h_st := Hψ.h_st
          h_full := Hψ.h_full
          w_memB_clk := Hψ.w_memB_clk
          w_memB_we := Hψ.w_memB_we
          w_memB_addr := Hψ.w_memB_addr
          w_memB_data := Hψ.w_memB_data
          w_memB_clrn := Hψ.w_memB_clrn
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_fullA_q := Hψ.w_fullA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

end Cases

/-! ### The refinement -/

theorem int_case_0 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_0 Hψ ‹_›⟩

theorem int_case_1 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_1 Hψ ‹_›⟩

theorem int_case_2 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_2 Hψ ‹_›⟩

theorem int_case_3 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_3 Hψ ‹_›⟩

theorem int_case_4 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_4 Hψ ‹_›⟩

theorem int_case_5 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_5 Hψ ‹_›⟩

theorem int_case_6 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_6 Hψ ‹_›⟩

theorem int_case_7 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_7 Hψ ‹_›⟩

theorem int_case_8 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_8 Hψ ‹_›⟩

theorem int_case_9 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_9 Hψ ‹_›⟩

theorem int_case_10 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_10 Hψ ‹_›⟩

theorem int_case_11 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_11 Hψ ‹_› ‹_›⟩

theorem int_case_12 (s : List Bool × List (WNext Bool 2) × List Bool × List (WSt 2) × List Bool × List (BitVec 3) × List (BitVec 2 → Bool)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_memB_clk, c_memB_we, c_memB_addr, c_memB_data, c_memB_clrn, c_memB_qh⟩, c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_fullA_q, c_clkF_in, c_unpN_d, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_12 Hψ ‹_›⟩

theorem bankNetlist_internals_eq : bankNetlist.internals = [bankNetlist.internals.getD 0 (fun _ _ => False), bankNetlist.internals.getD 1 (fun _ _ => False), bankNetlist.internals.getD 2 (fun _ _ => False), bankNetlist.internals.getD 3 (fun _ _ => False), bankNetlist.internals.getD 4 (fun _ _ => False), bankNetlist.internals.getD 5 (fun _ _ => False), bankNetlist.internals.getD 6 (fun _ _ => False), bankNetlist.internals.getD 7 (fun _ _ => False), bankNetlist.internals.getD 8 (fun _ _ => False), bankNetlist.internals.getD 9 (fun _ _ => False), bankNetlist.internals.getD 10 (fun _ _ => False), bankNetlist.internals.getD 11 (fun _ _ => False), bankNetlist.internals.getD 12 (fun _ _ => False)] := rfl

theorem refines_ψ : bankNetlist ⊑_{ψ} bankSpec := by
  intro i s Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs bankNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← Hψ.e_clk]; assumption), existSR_reflexive, in_clk Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← Hψ.e_d]; assumption), existSR_reflexive, in_d Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← Hψ.e_crn]; assumption), existSR_reflexive, in_clrn Hψ _ ‹_›⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_memB_clk, m_memB_we, m_memB_addr, m_memB_data, m_memB_clrn, m_memB_qh⟩, m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_fullA_q, m_clkF_in, m_unpN_d, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs bankNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨s, _, existSR_reflexive, spec_out_st s _ Hψ.h_st (out_st Hψ), out_st_wf Hψ⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_full s _ Hψ.h_full (out_full Hψ),
          out_full_wf Hψ⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_gray s _ (Hψ.e_grh ▸ ‹_›)
          (out_gray Hψ ‹_›), out_gray_wf Hψ⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_mem s _ (Hψ.e_mmh ▸ ‹_›)
          (out_mem Hψ ‹_›), out_mem_wf Hψ⟩
  · intro rule mid_i Hin Hrule
    rw [bankNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact int_case_0 s i mid_i Hψ Hrule
    · subst h; exact int_case_1 s i mid_i Hψ Hrule
    · subst h; exact int_case_2 s i mid_i Hψ Hrule
    · subst h; exact int_case_3 s i mid_i Hψ Hrule
    · subst h; exact int_case_4 s i mid_i Hψ Hrule
    · subst h; exact int_case_5 s i mid_i Hψ Hrule
    · subst h; exact int_case_6 s i mid_i Hψ Hrule
    · subst h; exact int_case_7 s i mid_i Hψ Hrule
    · subst h; exact int_case_8 s i mid_i Hψ Hrule
    · subst h; exact int_case_9 s i mid_i Hψ Hrule
    · subst h; exact int_case_10 s i mid_i Hψ Hrule
    · subst h; exact int_case_11 s i mid_i Hψ Hrule
    · subst h; exact int_case_12 s i mid_i Hψ Hrule

theorem refines_initial : Module.refines_initial bankNetlist bankSpec ψ := by
  intro i hi
  obtain ⟨⟨memB_clk, memB_we, memB_addr, memB_data, memB_clrn, memB_qh⟩, stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, fullA_q, clkF_in, unpN_d, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  dsimp only [bankNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨([], [], [], [], [], [], []), rfl, Wf.init⟩

/-- **The three blocks refine the write domain's register bank.** -/
theorem bank_refines : bankNetlist ⊑ bankSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.Bank
