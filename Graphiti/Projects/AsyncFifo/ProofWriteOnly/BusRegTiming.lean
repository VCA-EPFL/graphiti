/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusReg
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.DffTiming

/-!
# What the three-bit register does in time

`BusReg.lean` shows that the three flip-flops report the bits of `busOut`.  This file turns the
per-bit theorems of `DffTiming.lean` into the bus contracts of `ProofWriteOnly/Timed.lean`: `RegOut` for the
bus, and the glitch-free window of `BusRegOut`, which is what a Gray-coded pointer needs when it
crosses into the other clock domain.

Nothing new happens here.  A bus is its bits: each clause of the bus contract is the
corresponding clause of the bit contract, assembled by `bv3`, and the stability hypothesis of
the bus gives the stability of each bit by projection.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.BusReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Dff

/-- How far the register's inputs are known. -/
def busLen (clk : List Bool) (d : List (BitVec 3)) (crn : List Bool) : Nat :=
  min (min clk.length d.length) crn.length

theorem dffLen_bits (i : Nat) (clk : List Bool) (d : List (BitVec 3)) (crn : List Bool) :
    dffLen clk (bitsOf i d) crn = busLen clk d crn := by
  simp [dffLen, busLen]

/-- A bus is its bits. -/
theorem bv3_bits (x : BitVec 3) : bv3 (x.getLsbD 0) (x.getLsbD 1) (x.getLsbD 2) = x := by
  revert x; decide

@[simp] theorem bv3_false : bv3 false false false = 0#3 := rfl

@[simp] theorem bv3_getLsbD_zero (b0 b1 b2 : Bool) : (bv3 b0 b1 b2).getLsbD 0 = b0 := by
  revert b0 b1 b2; decide

@[simp] theorem bv3_getLsbD_one (b0 b1 b2 : Bool) : (bv3 b0 b1 b2).getLsbD 1 = b1 := by
  revert b0 b1 b2; decide

@[simp] theorem bv3_getLsbD_two (b0 b1 b2 : Bool) : (bv3 b0 b1 b2).getLsbD 2 = b2 := by
  revert b0 b1 b2; decide

/-- The bit of a bus, as the flip-flop of that bit sees it.  Beyond the bus both sides pad with
`false`, so this needs no bound. -/
theorem bitsOf_getD_all (i : Nat) (d : List (BitVec 3)) (u : Nat) :
    (bitsOf i d).getD u false = (d.getD u 0#3).getLsbD i := by
  by_cases h : u < d.length
  · exact bitsOf_getD h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [bitsOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

@[simp] theorem busOut_length (clk : List Bool) (d : List (BitVec 3)) (crn : List Bool) :
    (busOut clk d crn).length = busLen clk d crn + 1 := by
  simp only [busOut, pack3Out_length, dffOut_length, dffLen_bits]
  omega

theorem busOut_getD {clk : List Bool} {d : List (BitVec 3)} {crn : List Bool} {t : Nat}
    (ht : t < busLen clk d crn + 1) :
    (busOut clk d crn).getD t 0#3 =
      bv3 ((dffOut clk (bitsOf 0 d) crn).getD t false) ((dffOut clk (bitsOf 1 d) crn).getD t false)
        ((dffOut clk (bitsOf 2 d) crn).getD t false) := by
  refine pack3Out_getD ?_
  simp only [dffOut_length, dffLen_bits]
  omega

/-! ### The contracts -/

variable {clk : List Bool} {d : List (BitVec 3)} {crn : List Bool} {R : Nat}

/-- Every bit of the bus is an edge-triggered register, by `DffTiming.dffOut_regOut`. -/
theorem bit_regOut (i : Nat) (hR : 2 ≤ R) (hclear : ClearOK R crn (busLen clk d crn))
    (hreset : ResetOK (R + 3) clk (busLen clk d crn)) (hpulse : PulseOK 3 clk (busLen clk d crn)) :
    RegOut 4 1 false clk (fun u => (d.getD u 0#3).getLsbD i) d.length
      (dffOut clk (bitsOf i d) crn) := by
  have h := dffOut_regOut (d := bitsOf i d) hR (by rwa [dffLen_bits]) (by rwa [dffLen_bits])
    (by rwa [dffLen_bits])
  simp only [bitsOf_getD_all, bitsOf_length] at h
  exact h

/-- **The three-bit register meets `RegOut`**, with clock-to-q `4` and setup `1`. -/
theorem busOut_regOut (hR : 2 ≤ R) (hclear : ClearOK R crn (busLen clk d crn))
    (hreset : ResetOK (R + 3) clk (busLen clk d crn)) (hpulse : PulseOK 3 clk (busLen clk d crn))
    {v : List (BitVec 3)} (hv : v <+: busOut clk d crn) :
    RegOut 4 1 0#3 clk (fun u => d.getD u 0#3) d.length v := by
  have hlen := hv.length_le
  rw [busOut_length] at hlen
  have hb : ∀ i, RegOut 4 1 false clk (fun u => (d.getD u 0#3).getLsbD i) d.length
      (dffOut clk (bitsOf i d) crn) := fun i => bit_regOut i hR hclear hreset hpulse
  refine ⟨by unfold busLen at hlen; omega, fun t ht => ?_⟩
  have htb : t < busLen clk d crn + 1 := by omega
  have hq : ∀ i, t < (dffOut clk (bitsOf i d) crn).length := by
    intro i; simp only [dffOut_length, dffLen_bits]; omega
  refine ⟨fun hn => ?_, fun e he hs hk => ?_⟩
  · have hz : ∀ i, (dffOut clk (bitsOf i d) crn).getD t false = false :=
      fun i => ((hb i).2 t (hq i)).1 hn
    show v.getD t 0#3 = 0#3
    rw [hv.getD_eq_left ht, busOut_getD htb, hz 0, hz 1, hz 2]
    rfl
  · have hs' : ∀ i, StableOn (fun u => (d.getD u 0#3).getLsbD i) d.length (e - 1 - 1) e :=
      fun i => ⟨hs.1, fun u h1 h2 => congrArg (fun x => x.getLsbD i) (hs.2 u h1 h2)⟩
    have hd : ∀ i, (dffOut clk (bitsOf i d) crn).getD t false = (d.getD e 0#3).getLsbD i :=
      fun i => ((hb i).2 t (hq i)).2 e he (hs' i) hk
    show v.getD t 0#3 = d.getD e 0#3
    rw [hv.getD_eq_left ht, busOut_getD htb, hd 0, hd 1, hd 2]
    exact bv3_bits _

/-- **The three-bit register is glitch-free across an edge**: inside the clock-to-q window every
bit shows the value it had at the edge or the value the edge saw.  This is what makes a
Gray-coded pointer safe to sample in the other clock domain. -/
theorem busOut_busRegOut (hR : 2 ≤ R) (hclear : ClearOK R crn (busLen clk d crn))
    (hreset : ResetOK (R + 3) clk (busLen clk d crn)) (hpulse : PulseOK 3 clk (busLen clk d crn))
    (hstable : ∀ e, e < busLen clk d crn → riseAt clk e = true →
      ∀ u, e - 2 ≤ u → u ≤ e → d.getD u 0#3 = d.getD e 0#3)
    (hsep : ∀ e, e < busLen clk d crn → riseAt clk e = true →
      ∀ e', LastEdge clk e' (e - 3) → e' + 3 ≤ e - 3)
    {v : List (BitVec 3)} (hv : v <+: busOut clk d crn) :
    BusRegOut 4 1 clk (fun u => d.getD u 0#3) d.length v := by
  have hlen := hv.length_le
  rw [busOut_length] at hlen
  refine ⟨busOut_regOut hR hclear hreset hpulse hv, fun t ht _hclean e he hk i => ?_⟩
  have het : e < t := he.1
  have hel : e < busLen clk d crn := by omega
  have hq : ∀ j, t < (dffOut clk (bitsOf j d) crn).length := by
    intro j; simp only [dffOut_length, dffLen_bits]; omega
  have hqe : ∀ j, e < (dffOut clk (bitsOf j d) crn).length := by
    intro j; simp only [dffOut_length, dffLen_bits]; omega
  -- every bit shows the value it had at the edge, or the one the edge saw
  have hbit : ∀ j, (dffOut clk (bitsOf j d) crn).getD t false = (d.getD e 0#3).getLsbD j ∨
      (dffOut clk (bitsOf j d) crn).getD t false = (dffOut clk (bitsOf j d) crn).getD e false := by
    intro j
    have hw := dffOut_window (clk := clk) (d := bitsOf j d) (crn := crn) (R := R) (e := e) (t := t)
      hR (by omega) (by omega) (by rw [dffLen_bits]; omega) he.2.1
      (by rwa [dffLen_bits]) (by rwa [dffLen_bits]) (by rwa [dffLen_bits])
      (fun e' h0 h1 h2 u h3 h4 => by
        rw [dffLen_bits] at h1
        rw [bitsOf_getD_all, bitsOf_getD_all, hstable e' h1 h2 u h3 h4])
      (fun e' h1 => hsep e hel he.2.1 e' h1)
    rcases hw with h | h
    · exact Or.inl (by rw [h, bitsOf_getD_all])
    · exact Or.inr h
  show (v.getD t 0#3).getLsbD i = _ ∨ (v.getD t 0#3).getLsbD i = (v.getD e 0#3).getLsbD i
  rw [hv.getD_eq_left ht, hv.getD_eq_left (by omega), busOut_getD (by omega),
    busOut_getD (by omega)]
  by_cases hi : i < 3
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rcases hbit 0 with h | h
      · exact Or.inl (by simp only [bv3_getLsbD_zero]; exact h)
      · exact Or.inr (by simp only [bv3_getLsbD_zero]; exact h)
    · rcases hbit 1 with h | h
      · exact Or.inl (by simp only [bv3_getLsbD_one]; exact h)
      · exact Or.inr (by simp only [bv3_getLsbD_one]; exact h)
    · rcases hbit 2 with h | h
      · exact Or.inl (by simp only [bv3_getLsbD_two]; exact h)
      · exact Or.inr (by simp only [bv3_getLsbD_two]; exact h)
  · exact Or.inl (by rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)])

end Graphiti.AsyncFifo.BusReg
