/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteState
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.DffTiming

/-!
# What the state register does in time

`WriteState.lean` shows that the seven flip-flops report the bits of `stOut`.  This file turns the
per-bit theorems of `DffTiming.lean` into `RegOut` for the record, exactly as
`BusRegTiming.lean` does for the Gray pointer: a record is its bits.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.WriteState

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Dff

/-- How far the register's inputs are known. -/
def stLen (clk : List Bool) (d : List (WSt 2)) (crn : List Bool) : Nat :=
  min (min clk.length d.length) crn.length

theorem dffLen_bits (i : Nat) (clk : List Bool) (d : List (WSt 2)) (crn : List Bool) :
    dffLen clk (bitsOf i d) crn = stLen clk d crn := by
  simp [dffLen, stLen]

@[simp] theorem stOut_length (clk : List Bool) (d : List (WSt 2)) (crn : List Bool) :
    (stOut clk d crn).length = stLen clk d crn + 1 := by
  simp only [stOut, packStOut_length, dffOut_length, dffLen_bits]
  omega

theorem stOut_getD {clk : List Bool} {d : List (WSt 2)} {crn : List Bool} {t : Nat}
    (ht : t < stLen clk d crn + 1) :
    (stOut clk d crn).getD t default =
      ⟨bv3 ((dffOut clk (bitsOf 0 d) crn).getD t false) ((dffOut clk (bitsOf 1 d) crn).getD t false)
          ((dffOut clk (bitsOf 2 d) crn).getD t false),
        (dffOut clk (bitsOf 3 d) crn).getD t false,
        bv3 ((dffOut clk (bitsOf 4 d) crn).getD t false) ((dffOut clk (bitsOf 5 d) crn).getD t false)
          ((dffOut clk (bitsOf 6 d) crn).getD t false)⟩ := by
  refine packStOut_getD ?_
  simp only [dffOut_length, dffLen_bits]
  omega

variable {clk : List Bool} {d : List (WSt 2)} {crn : List Bool} {R : Nat}

/-- Every bit of the record is an edge-triggered register. -/
theorem bit_regOut (i : Nat) (hR : 2 ≤ R) (hclear : ClearOK R crn (stLen clk d crn))
    (hreset : ResetOK (R + 3) clk (stLen clk d crn)) (hpulse : PulseOK 3 clk (stLen clk d crn)) :
    RegOut 4 1 false clk (fun u => stBit i (d.getD u default)) d.length
      (dffOut clk (bitsOf i d) crn) := by
  have h := dffOut_regOut (d := bitsOf i d) hR (by rwa [dffLen_bits]) (by rwa [dffLen_bits])
    (by rwa [dffLen_bits])
  simp only [bitsOf_getD_all, bitsOf_length] at h
  exact h

/-- **The seven-bit register meets `RegOut`**, with clock-to-q `4` and setup `1`. -/
theorem stOut_regOut (hR : 2 ≤ R) (hclear : ClearOK R crn (stLen clk d crn))
    (hreset : ResetOK (R + 3) clk (stLen clk d crn)) (hpulse : PulseOK 3 clk (stLen clk d crn))
    {v : List (WSt 2)} (hv : v <+: stOut clk d crn) :
    RegOut 4 1 default clk (fun u => d.getD u default) d.length v := by
  have hlen := hv.length_le
  rw [stOut_length] at hlen
  have hb : ∀ i, RegOut 4 1 false clk (fun u => stBit i (d.getD u default)) d.length
      (dffOut clk (bitsOf i d) crn) := fun i => bit_regOut i hR hclear hreset hpulse
  refine ⟨by unfold stLen at hlen; omega, fun t ht => ?_⟩
  have htb : t < stLen clk d crn + 1 := by omega
  have hq : ∀ i, t < (dffOut clk (bitsOf i d) crn).length := by
    intro i; simp only [dffOut_length, dffLen_bits]; omega
  refine ⟨fun hn => ?_, fun e he hs hk => ?_⟩
  · have hz : ∀ i, (dffOut clk (bitsOf i d) crn).getD t false = false :=
      fun i => ((hb i).2 t (hq i)).1 hn
    show v.getD t default = default
    rw [hv.getD_eq_left ht, stOut_getD htb, hz 0, hz 1, hz 2, hz 3, hz 4, hz 5, hz 6]
    rfl
  · have hs' : ∀ i, StableOn (fun u => stBit i (d.getD u default)) d.length (e - 1 - 1) e :=
      fun i => ⟨hs.1, fun u h1 h2 => congrArg (stBit i) (hs.2 u h1 h2)⟩
    have hd : ∀ i, (dffOut clk (bitsOf i d) crn).getD t false = stBit i (d.getD e default) :=
      fun i => ((hb i).2 t (hq i)).2 e he (hs' i) hk
    show v.getD t default = d.getD e default
    rw [hv.getD_eq_left ht, stOut_getD htb, hd 0, hd 1, hd 2, hd 3, hd 4, hd 5, hd 6]
    exact stBit_all _

end Graphiti.AsyncFifo.WriteState
