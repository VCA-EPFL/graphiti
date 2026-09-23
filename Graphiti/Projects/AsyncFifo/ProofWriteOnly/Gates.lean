/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Timed
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.GatesLemmas

/-!
# Gates: the combinational contracts of wires

`Comb lo hi F inp w` is the combinational contract of a wire of a netlist: `w` is the output
of logic of depth between `lo` and `hi` computing `F` of the netlist's primary inputs
`inp`.  It composes through gates (`Comb.gate2`, `Comb.gate1`), weakens to wider depth windows
(`Comb.weaken`), and a bundle of such wires satisfies the `CombOut` contract of the block.
-/


set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Gates

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed

/-! ### Combinational contracts of wires -/

/-- `w` is a wire of a netlist whose primary inputs are `inp` (known for `len` instants),
computing `F` of them through logic of depth between `lo` and `hi`: wherever the inputs were
constant over the delay window, the wire shows `F` of them. -/
def Comb {I : Type} (lo hi : Nat) (F : I → Bool) (inp : Nat → I) (w : List Bool) : Prop :=
  lo ≤ hi ∧
  ∀ t, hi ≤ t → t < w.length → (∀ u, t - hi ≤ u → u ≤ t - lo → inp u = inp (t - lo)) →
    w.getD t false = F (inp (t - hi))

variable {I : Type} {inp : Nat → I}

/-- A primary input, or a projection of one, is a wire of depth `0`. -/
theorem Comb.input {F : I → Bool} {w : List Bool}
    (h : ∀ t, t < w.length → w.getD t false = F (inp t)) : Comb 0 0 F inp w :=
  ⟨Nat.le_refl _, fun t _ ht _ => h t ht⟩

theorem Comb.weaken {lo hi lo' hi' : Nat} {F : I → Bool} {w : List Bool} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : Comb lo hi F inp w) : Comb lo' hi' F inp w := by
  obtain ⟨hlh, h⟩ := h
  refine ⟨by lia, fun t ht htl hs => ?_⟩
  rw [h t (by lia) htl (fun u hu1 hu2 => by rw [hs u (by lia) (by lia), hs (t - lo) (by lia) (by lia)])]
  rw [hs (t - hi) (by lia) (by lia), hs (t - hi') (by lia) (by lia)]

theorem Comb.gate2 {lo1 hi1 lo2 hi2 : Nat} {F1 F2 : I → Bool} {w1 w2 : List Bool} (f : Bool → Bool → Bool)
    (h1 : Comb lo1 hi1 F1 inp w1) (h2 : Comb lo2 hi2 F2 inp w2) :
    Comb (min lo1 lo2 + 1) (max hi1 hi2 + 1) (fun i => f (F1 i) (F2 i)) inp (gateOut f w1 w2) := by
  obtain ⟨hlh1, h1⟩ := h1
  obtain ⟨hlh2, h2⟩ := h2
  refine ⟨by omega, fun t ht htl hs => ?_⟩
  simp only [gateOut_length] at htl
  have hmin : min lo1 lo2 ≤ lo1 ∧ min lo1 lo2 ≤ lo2 := ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩
  have hmax : hi1 ≤ max hi1 hi2 ∧ hi2 ≤ max hi1 hi2 := ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  rw [gateOut_getD f w1 w2 (by omega) htl]
  rw [h1 (t - 1) (by omega) (by omega) (fun u hu1 hu2 => by rw [hs u (by omega) (by omega), hs (t - 1 - lo1) (by omega) (by omega)])]
  rw [h2 (t - 1) (by omega) (by omega) (fun u hu1 hu2 => by rw [hs u (by omega) (by omega), hs (t - 1 - lo2) (by omega) (by omega)])]
  rw [hs (t - 1 - hi1) (by omega) (by omega), hs (t - 1 - hi2) (by omega) (by omega),
    hs (t - (max hi1 hi2 + 1)) (by omega) (by omega)]

theorem Comb.gate1 {lo1 hi1 : Nat} {F1 : I → Bool} {w1 : List Bool} (f : Bool → Bool)
    (h1 : Comb lo1 hi1 F1 inp w1) :
    Comb (lo1 + 1) (hi1 + 1) (fun i => f (F1 i)) inp (gate1Out f w1) := by
  obtain ⟨hlh1, h1⟩ := h1
  refine ⟨by omega, fun t ht htl hs => ?_⟩
  simp only [gate1Out_length] at htl
  rw [gate1Out_getD f w1 (by omega) htl]
  rw [h1 (t - 1) (by omega) (by omega) (fun u hu1 hu2 => by rw [hs u (by omega) (by omega), hs (t - 1 - lo1) (by omega) (by omega)])]
  rw [hs (t - 1 - hi1) (by omega) (by omega), hs (t - (hi1 + 1)) (by omega) (by omega)]

/-- A prefix of a wire satisfies its contract. -/
theorem Comb.of_prefix {lo hi : Nat} {F : I → Bool} {w w' : List Bool} (h : w' <+: w) (hw : Comb lo hi F inp w) :
    Comb lo hi F inp w' := by
  have := h.length_le
  obtain ⟨hlh, hw⟩ := hw
  refine ⟨hlh, fun t ht htl hs => ?_⟩
  rw [h.getD_eq_left htl]; exact hw t ht (by omega) hs

/-- `getD` through `map`, below the length. -/
theorem getD_map_lt {α β : Type} [Inhabited α] (f : α → β) (l : List α) {t : Nat} (ht : t < l.length) (d : β) :
    (l.map f).getD t d = f (l.getD t default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

/-- `CombOut` is prefix-closed. -/
theorem _root_.Graphiti.AsyncFifo.Contracts.CombOut.of_prefix {κ ο : Type} [Inhabited ο] {dep : Nat → κ} {g : κ → ο} {len dmin dmax : Nat}
    {v v' : List ο} (h : v' <+: v) (hv : CombOut dep g len dmin dmax v) : CombOut dep g len dmin dmax v' := by
  have := h.length_le
  obtain ⟨hl, hv⟩ := hv
  refine ⟨by omega, fun t hdt ht hs => ?_⟩
  rw [h.getD_eq_left ht]; exact hv t hdt (by omega) hs

/-- The stability hypothesis of `CombOut` gives the one of `Comb` (for a window `[0, hi]`). -/
theorem Comb.stable_of_StableOn {κ : Type} {dep : Nat → κ} {len hi t : Nat} (hs : StableOn dep len (t - hi) t) :
    ∀ u, t - hi ≤ u → u ≤ t - 0 → dep u = dep (t - 0) := fun u hu1 hu2 => hs.2 u hu1 (by omega)

/-! ### Arithmetic on stream lengths without case splits

The length of a netlist's output is a nested `min` of its inputs' lengths.  `omega` handles
`min` by splitting every occurrence into two cases, so its cost doubles with each `min`: a
goal with 13 of them already needs minutes and gigabytes.  Generated proofs therefore never
give `omega` a nested `min`.  They rewrite `t < min a b` into a conjunction (`Nat.lt_min`),
`min a b ≤ c` into a disjunction (`min_le_iff_nat`), and prove monotonicity by composing
`min_mono`, all of which stay linear in the number of `min`s. -/

theorem min_mono {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : min a b ≤ min c d := by omega

theorem min_le_iff_nat {a b c : Nat} : min a b ≤ c ↔ a ≤ c ∨ b ≤ c := by omega

end Graphiti.AsyncFifo.Gates
