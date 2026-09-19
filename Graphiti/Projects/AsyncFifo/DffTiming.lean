/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Dff
import Graphiti.Projects.AsyncFifo.Timed

/-!
# What the flip-flop does in time

`Dff.lean` shows that the netlist's output is the wire `n5` of a six-bit automaton.  This file
says what that wire *is*: the register contract of `Timed.lean` -- `RegOut` as written there,
not a weakened version -- with clock-to-q `4` and setup `1`, under one filter the register
level did not need.

Three facts, each a finite check of the automaton followed by an induction along the stream:

* `run_good_pre`: while the clear is asserted the circuit reaches its cleared state from
  wherever it powered up, and a low clock then holds it there -- the output reads low until the
  first edge.  Without the clear there is no such instant (see `Dff.lean`).
* `run_good_edge`: from three instants after a rising edge until the next one, the output is
  the data the edge saw, provided that data was stable over the two instants before it.
* `run_window`: inside those three instants the output is the value at the edge or the new
  one -- no third value appears.  This is what a Gray-coded pointer crossing domains needs,
  and it is the one-bit case of `BusRegOut`.

One thing is new at this level: the clock filter `PulseOK 3`.  `ClockOK P` only keeps rising
edges `P` apart, and a clock that is high for one instant in `P` satisfies it while leaving the
flip-flop's internal loops unresolved.  A netlist needs the pulses themselves to be wide.

What is *not* needed is a startup allowance, and that is what the seventh gate buys.  Every
wire is low at instant `0`, so at instant `1` every gate shows its function of that all-low
state; an output NAND would read `true` there, and `RegOut` -- which pins the output at every
instant before the first edge -- would be unsatisfiable by any netlist of these gates.  With
the output gated by the clear it reads low from instant `0`, and the contract holds as
`Timed.lean` states it.  The alternative was to thread a startup allowance up through
`Settled`, the invariant and the specification, which would have weakened the register-level
theorem for a gate-level artefact.

The invariant `good` and the shape of the argument (a finite check at the edge, then one step
at a time) are Kobler's `sim_good` from `CombinationalStream.lean`.  What differs is that the
checks are on our resettable circuit and are left to the kernel rather than unfolded by hand,
and that the conclusions are the contracts of `Timed.lean` rather than her filtered stream.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Dff

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Timed

/-! ### The settled states of the automaton -/

/-- The flip-flop holds `D` and the clock is `c`: the output pair `n5`/`n6` is the stored
value, and the master half is consistent with it.  While the clock is low the master is idle
(`n2 = n3 = true`); while it is high it has captured `D`. -/
def good (s : DffSt) (D c : Bool) : Bool :=
  (s.n5 == D) && (s.n6 == !D) && (s.n2 == (if c then !D else true)) &&
  (s.n3 == (if c then D else true)) && (!c || (s.n1 == D)) && (!c || D || s.n4)

/-- The state the clear forces: `q` low, master idle. -/
def cleared : DffSt := ⟨false, true, true, true, false, true⟩

/-- Three instants of low clock, the data already settled to `dr` over the last two. -/
def preEdge (s : DffSt) (dm3 dr : Bool) : DffSt :=
  dffStep (dffStep (dffStep s (false, dm3, true)) (false, dr, true)) (false, dr, true)

/-- Three instants of high clock after the edge. -/
def afterEdge (s : DffSt) (dm3 dr d1 d2 : Bool) : DffSt :=
  dffStep (dffStep (dffStep (preEdge s dm3 dr) (true, dr, true)) (true, d1, true)) (true, d2, true)

/-! ### The finite checks

Each of these is a statement about `2 ^ n` boolean cases, which the kernel evaluates. -/

/-- Two instants of clear bring the circuit to its cleared state from any state at all. -/
theorem clear2 (s : DffSt) (d0 d1 : Bool) :
    dffStep (dffStep s (false, d0, false)) (false, d1, false) = cleared := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := s
  revert d0 d1; revert n1 n2 n3 n4 n5 n6; decide

theorem good_cleared : good cleared false false = true := by decide

/-- A settled state stays settled: one instant of clock that is not a rising edge. -/
theorem step_good (s : DffSt) (D c cn dn : Bool) (hg : good s D c = true)
    (hc : cn = true → c = true) : good (dffStep s (cn, dn, true)) D cn = true := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := s
  revert hg hc; revert D c cn dn; revert n1 n2 n3 n4 n5 n6; decide

/-- Three instants of low clock and three of high, from any state at all, leave the flip-flop
holding the data the edge saw. -/
theorem edge_good (s : DffSt) (dm3 dr d1 d2 : Bool) :
    good (afterEdge s dm3 dr d1 d2) dr true = true := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := s
  revert dm3 dr d1 d2; revert n1 n2 n3 n4 n5 n6; decide

/-- One instant into the clock-to-q window, the output is the old value or the new one. -/
theorem win1 (s : DffSt) (D c dm3 dr : Bool) (hg : good s D c = true) :
    (dffStep (preEdge s dm3 dr) (true, dr, true)).n5 = dr ∨
    (dffStep (preEdge s dm3 dr) (true, dr, true)).n5 = (preEdge s dm3 dr).n5 := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := s
  revert hg; revert D c dm3 dr; revert n1 n2 n3 n4 n5 n6; decide

/-- Two instants in, the same. -/
theorem win2 (s : DffSt) (D c dm3 dr d1 : Bool) (hg : good s D c = true) :
    (dffStep (dffStep (preEdge s dm3 dr) (true, dr, true)) (true, d1, true)).n5 = dr ∨
    (dffStep (dffStep (preEdge s dm3 dr) (true, dr, true)) (true, d1, true)).n5 =
      (preEdge s dm3 dr).n5 := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := s
  revert hg; revert D c dm3 dr d1; revert n1 n2 n3 n4 n5 n6; decide

/-- No rising edge before `t` means the clock has been low throughout. -/
theorem clk_low_of_noEdge {clk : List Bool} {t : Nat} (h : NoEdge clk t) :
    ∀ u, u < t → clk.getD u false = false := by
  intro u
  induction u with
  | zero => intro hu; have h0 := h 0 hu; unfold riseAt at h0; simpa using h0
  | succ u ih =>
    intro hu
    have hprev := ih (by omega)
    have h1 := h (u + 1) hu
    unfold riseAt at h1
    simp only [Nat.add_sub_cancel, hprev, Bool.not_false, Bool.or_true, Bool.and_true] at h1
    exact h1

/-! ### Before the first edge -/

/-- Wherever the circuit powered up, two instants of clear with a low clock settle it. -/
theorem run_cleared {clk d crn : List Bool} {t : Nat} (ht : 2 ≤ t)
    (hclk : ∀ u, u < t → clk.getD u false = false)
    (hcrn : ∀ u, u < t → crn.getD u false = false) :
    dffRun clk d crn t = cleared := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 2 := ⟨t - 2, by omega⟩
  have e : dffRun clk d crn (m + 2) =
      dffStep (dffStep (dffRun clk d crn m) (dffInp clk d crn m)) (dffInp clk d crn (m + 1)) := by
    simp only [dffRun, run_succ]
  rw [e]
  unfold dffInp
  rw [hclk m (by omega), hcrn m (by omega), hclk (m + 1) (by omega), hcrn (m + 1) (by omega)]
  exact clear2 _ _ _

/-- After the clear and until the first edge, the flip-flop holds low. -/
theorem run_good_pre {clk d crn : List Bool} {R t : Nat} (hR : 2 ≤ R) (hRt : R ≤ t)
    (hclk : ∀ u, u < t → clk.getD u false = false)
    (hcrn0 : ∀ u, u < R → crn.getD u false = false)
    (hcrn1 : ∀ u, R ≤ u → u < t → crn.getD u false = true) :
    good (dffRun clk d crn t) false false = true := by
  revert hclk hcrn1
  induction t, hRt using Nat.le_induction with
  | base =>
    intro hclk _
    rw [run_cleared hR hclk hcrn0]
    exact good_cleared
  | succ t hRt ih =>
    intro hclk hcrn1
    have hg := ih (fun u hu => hclk u (by omega)) (fun u h1 h2 => hcrn1 u h1 (by omega))
    have e : dffRun clk d crn (t + 1) = dffStep (dffRun clk d crn t) (dffInp clk d crn t) := rfl
    rw [e]
    unfold dffInp
    rw [hclk t (by omega), hcrn1 t hRt (by omega)]
    exact step_good _ _ _ _ _ hg (by simp)

/-! ### After an edge -/

/-- The six instants around an edge, as one application of the automaton. -/
theorem run_afterEdge {clk d crn : List Bool} {m : Nat}
    (hlow : ∀ u, m ≤ u → u < m + 3 → clk.getD u false = false)
    (hhigh : ∀ u, m + 3 ≤ u → u < m + 6 → clk.getD u false = true)
    (hcrn : ∀ u, m ≤ u → u < m + 6 → crn.getD u false = true)
    (hstable : ∀ u, m + 1 ≤ u → u ≤ m + 3 → d.getD u false = d.getD (m + 3) false) :
    dffRun clk d crn (m + 6) =
      afterEdge (dffRun clk d crn m) (d.getD m false) (d.getD (m + 3) false)
        (d.getD (m + 4) false) (d.getD (m + 5) false) := by
  have e : dffRun clk d crn (m + 6) = dffStep (dffStep (dffStep (dffStep (dffStep (dffStep
      (dffRun clk d crn m) (dffInp clk d crn m)) (dffInp clk d crn (m + 1)))
      (dffInp clk d crn (m + 2))) (dffInp clk d crn (m + 3))) (dffInp clk d crn (m + 4)))
      (dffInp clk d crn (m + 5)) := by
    simp only [dffRun, run_succ]
  rw [e]
  unfold dffInp afterEdge preEdge
  rw [hlow m (by omega) (by omega), hlow (m + 1) (by omega) (by omega),
    hlow (m + 2) (by omega) (by omega), hhigh (m + 3) (by omega) (by omega),
    hhigh (m + 4) (by omega) (by omega), hhigh (m + 5) (by omega) (by omega),
    hcrn m (by omega) (by omega), hcrn (m + 1) (by omega) (by omega),
    hcrn (m + 2) (by omega) (by omega), hcrn (m + 3) (by omega) (by omega),
    hcrn (m + 4) (by omega) (by omega), hcrn (m + 5) (by omega) (by omega),
    hstable (m + 1) (by omega) (by omega), hstable (m + 2) (by omega) (by omega)]

/-- The three instants of low clock before an edge, as one application. -/
theorem run_preEdge {clk d crn : List Bool} {m : Nat}
    (hlow : ∀ u, m ≤ u → u < m + 3 → clk.getD u false = false)
    (hcrn : ∀ u, m ≤ u → u < m + 3 → crn.getD u false = true)
    (hstable : ∀ u, m + 1 ≤ u → u ≤ m + 3 → d.getD u false = d.getD (m + 3) false) :
    dffRun clk d crn (m + 3) =
      preEdge (dffRun clk d crn m) (d.getD m false) (d.getD (m + 3) false) := by
  have e : dffRun clk d crn (m + 3) = dffStep (dffStep (dffStep
      (dffRun clk d crn m) (dffInp clk d crn m)) (dffInp clk d crn (m + 1)))
      (dffInp clk d crn (m + 2)) := by
    simp only [dffRun, run_succ]
  rw [e]
  unfold dffInp preEdge
  rw [hlow m (by omega) (by omega), hlow (m + 1) (by omega) (by omega),
    hlow (m + 2) (by omega) (by omega), hcrn m (by omega) (by omega),
    hcrn (m + 1) (by omega) (by omega), hcrn (m + 2) (by omega) (by omega),
    hstable (m + 1) (by omega) (by omega), hstable (m + 2) (by omega) (by omega)]

/-- From three instants after a rising edge until the next one, the flip-flop holds the data
the edge saw. -/
theorem run_good_edge {clk d crn : List Bool} {e t : Nat} (he : 3 ≤ e) (het : e + 3 ≤ t)
    (hlow : ∀ u, e - 3 ≤ u → u < e → clk.getD u false = false)
    (hhigh : ∀ u, e ≤ u → u < e + 3 → clk.getD u false = true)
    (hstable : ∀ u, e - 2 ≤ u → u ≤ e → d.getD u false = d.getD e false)
    (hcrn : ∀ u, e - 3 ≤ u → u < t → crn.getD u false = true)
    (hno : ∀ u, e < u → u < t → riseAt clk u = false) :
    good (dffRun clk d crn t) (d.getD e false) (clk.getD (t - 1) false) = true := by
  revert hcrn hno
  induction t, het using Nat.le_induction with
  | base =>
    intro hcrn _
    obtain ⟨m, rfl⟩ : ∃ m, e = m + 3 := ⟨e - 3, by omega⟩
    rw [show m + 3 + 3 = m + 6 by omega,
      run_afterEdge (fun u h1 h2 => hlow u (by omega) (by omega))
        (fun u h1 h2 => hhigh u (by omega) (by omega))
        (fun u h1 h2 => hcrn u (by omega) (by omega))
        (fun u h1 h2 => hstable u (by omega) (by omega)),
      show m + 6 - 1 = m + 5 by omega, hhigh (m + 5) (by omega) (by omega)]
    exact edge_good _ _ _ _ _
  | succ t het ih =>
    intro hcrn hno
    have hg := ih (fun u h1 h2 => hcrn u h1 (by omega)) (fun u h1 h2 => hno u h1 (by omega))
    have e1 : dffRun clk d crn (t + 1) = dffStep (dffRun clk d crn t) (dffInp clk d crn t) := rfl
    rw [e1]
    unfold dffInp
    rw [hcrn t (by omega) (by omega), show t + 1 - 1 = t by omega]
    refine step_good _ _ _ _ _ hg (fun hc => ?_)
    by_contra hne
    have hprev : clk.getD (t - 1) false = false := by
      cases hx : clk.getD (t - 1) false with
      | false => rfl
      | true => exact absurd hx hne
    have := hno t (by omega) (by omega)
    rw [riseAt, hc, hprev] at this
    simp at this

/-! ### Inside the clock-to-q window -/

/-- Inside the three instants after an edge, the output is the value it had at the edge or the
value the edge saw -- never a third value.  This needs the circuit to have been settled before
the edge, which it is once the previous edge is over. -/
theorem run_window {clk d crn : List Bool} {e t : Nat} (he : 3 ≤ e) (het : e ≤ t) (htw : t < e + 3)
    (hlow : ∀ u, e - 3 ≤ u → u < e → clk.getD u false = false)
    (hhigh : ∀ u, e ≤ u → u < t → clk.getD u false = true)
    (hstable : ∀ u, e - 2 ≤ u → u ≤ e → d.getD u false = d.getD e false)
    (hcrn : ∀ u, e - 3 ≤ u → u < t → crn.getD u false = true)
    (hsettled : ∃ D c, good (dffRun clk d crn (e - 3)) D c = true) :
    (dffRun clk d crn t).n5 = d.getD e false ∨
      (dffRun clk d crn t).n5 = (dffRun clk d crn e).n5 := by
  obtain ⟨D, c, hgood⟩ := hsettled
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 3 := ⟨e - 3, by omega⟩
  simp only [Nat.add_sub_cancel] at hgood
  have hpre : dffRun clk d crn (m + 3) =
      preEdge (dffRun clk d crn m) (d.getD m false) (d.getD (m + 3) false) :=
    run_preEdge (fun u h1 h2 => hlow u (by omega) (by omega))
      (fun u h1 h2 => hcrn u (by omega) (by omega))
      (fun u h1 h2 => hstable u (by omega) (by omega))
  rcases (by omega : t = m + 3 ∨ t = m + 3 + 1 ∨ t = m + 3 + 2) with rfl | rfl | rfl
  · exact Or.inr rfl
  · have e1 : dffRun clk d crn (m + 3 + 1) =
        dffStep (dffRun clk d crn (m + 3)) (dffInp clk d crn (m + 3)) := rfl
    rw [e1, hpre]
    unfold dffInp
    rw [hhigh (m + 3) (by omega) (by omega), hcrn (m + 3) (by omega) (by omega)]
    exact win1 _ D c _ _ hgood
  · have e2 : dffRun clk d crn (m + 3 + 2) = dffStep (dffStep (dffRun clk d crn (m + 3))
        (dffInp clk d crn (m + 3))) (dffInp clk d crn (m + 4)) := by
      simp only [dffRun, run_succ]
    rw [e2, hpre]
    unfold dffInp
    rw [hhigh (m + 3) (by omega) (by omega), hcrn (m + 3) (by omega) (by omega),
      hhigh (m + 4) (by omega) (by omega), hcrn (m + 4) (by omega) (by omega)]
    exact win2 _ D c _ _ _ hgood

/-! ### Reading the invariant -/

theorem good_n5 {s : DffSt} {D c : Bool} (h : good s D c = true) : s.n5 = D := by
  unfold good at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1

/-! ### The register contract

With the output gated by the clear there is nothing to weaken: this is `RegOut` exactly as
`Timed.lean` writes it, at clock-to-q `4` and setup `1`. -/

/-- A settled state stays settled over an instant of low clock, holding the same value. -/
theorem good_step_low {clk d crn : List Bool} {m : Nat} {D c : Bool}
    (hg : good (dffRun clk d crn m) D c = true) (hclk : clk.getD m false = false)
    (hcrn : crn.getD m false = true) : good (dffRun clk d crn (m + 1)) D false = true := by
  have e : dffRun clk d crn (m + 1) = dffStep (dffRun clk d crn m) (dffInp clk d crn m) := rfl
  rw [e]
  unfold dffInp
  rw [hclk, hcrn]
  exact step_good _ _ _ _ _ hg (by simp)

/-- **The flip-flop is an edge-triggered register** with clock-to-q `4` and setup `1`: `clrn`
asserted over `[0, R)`, no edge before `R + 3`, and every pulse at least three instants wide. -/
theorem dffOut_regOut {clk d crn : List Bool} {R : Nat} (hR : 2 ≤ R)
    (hclear : ClearOK R crn (dffLen clk d crn))
    (hreset : ResetOK (R + 3) clk (dffLen clk d crn))
    (hpulse : PulseOK 3 clk (dffLen clk d crn)) :
    RegOut 4 1 false clk (fun u => d.getD u false) d.length (dffOut clk d crn) := by
  refine ⟨by rw [dffOut_length]; unfold dffLen; omega, fun t ht => ?_⟩
  rw [dffOut_length] at ht
  refine ⟨fun hn => ?_, fun e hle hst hkq => ?_⟩
  · show (dffOut clk d crn).getD t false = false
    rw [dffOut_getD _ _ _ ht]
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rfl
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    show and2 _ _ = false
    by_cases hlt : u < R
    · rw [hclear.1 u hlt, and2]; simp
    · rw [good_n5 (run_good_pre hR (by omega) (fun w hw => clk_low_of_noEdge hn w (by omega))
        hclear.1 (fun w h1 h2 => hclear.2 w h1 (by omega))), and2]
      simp
  · have hel : e < dffLen clk d crn := by have := hle.1; omega
    obtain ⟨he3, hlow, hhigh⟩ := hpulse e hel hle.2.1
    have hRe : R + 3 ≤ e := hreset e hel hle.2.1
    have het : e < t := hle.1
    show (dffOut clk d crn).getD t false = d.getD e false
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    rw [dffOut_getD _ _ _ ht]
    show and2 _ _ = _
    rw [hclear.2 u (by omega) (by omega),
      good_n5 (run_good_edge he3 (show e + 3 ≤ u by omega) hlow
        (fun w h1 h2 => hhigh w h1 h2 (by omega))
        (fun w h1 h2 => hst.2 w (by omega) h2)
        (fun w h1 h2 => hclear.2 w (by omega) (by omega))
        (fun w h1 h2 => hle.2.2 w h1 (by omega))), and2]
    simp

/-- **The circuit is settled** at every instant after the clear at which the last edge, if any,
is three instants old. -/
theorem settled_at {clk d crn : List Bool} {R t : Nat} (hR : 2 ≤ R) (hRt : R ≤ t)
    (ht : t ≤ dffLen clk d crn)
    (hclear : ClearOK R crn (dffLen clk d crn))
    (hreset : ResetOK (R + 3) clk (dffLen clk d crn))
    (hpulse : PulseOK 3 clk (dffLen clk d crn))
    (hstable : ∀ e, e < t → e < dffLen clk d crn → riseAt clk e = true →
      ∀ u, e - 2 ≤ u → u ≤ e → d.getD u false = d.getD e false)
    (hlast : ∀ e, LastEdge clk e t → e + 3 ≤ t) :
    ∃ D c, good (dffRun clk d crn t) D c = true := by
  by_cases hn : NoEdge clk t
  · exact ⟨false, false, run_good_pre hR hRt (clk_low_of_noEdge hn) hclear.1
      (fun u h1 h2 => hclear.2 u h1 (by omega))⟩
  · obtain ⟨e, hle⟩ := exists_lastEdge hn
    have hel : e < dffLen clk d crn := by have := hle.1; omega
    obtain ⟨he3, hlow, hhigh⟩ := hpulse e hel hle.2.1
    have hRe : R + 3 ≤ e := hreset e hel hle.2.1
    have het3 : e + 3 ≤ t := hlast e hle
    exact ⟨d.getD e false, clk.getD (t - 1) false,
      run_good_edge he3 het3 hlow (fun u h1 h2 => hhigh u h1 h2 (by omega))
        (hstable e hle.1 hel hle.2.1) (fun u h1 h2 => hclear.2 u (by omega) (by omega))
        (fun u h1 h2 => hle.2.2 u h1 h2)⟩

/-- **The output is glitch-free across an edge**: inside the clock-to-q window it shows the
value it had at the edge or the value the edge saw.  This is the one-bit case of `BusRegOut`,
and it is what makes a Gray-coded pointer safe to sample in another clock domain. -/
theorem dffOut_window {clk d crn : List Bool} {R e t : Nat} (hR : 2 ≤ R)
    (het : e ≤ t) (htw : t < e + 4) (ht : t ≤ dffLen clk d crn) (hrise : riseAt clk e = true)
    (hclear : ClearOK R crn (dffLen clk d crn))
    (hreset : ResetOK (R + 3) clk (dffLen clk d crn))
    (hpulse : PulseOK 3 clk (dffLen clk d crn))
    (hstable : ∀ e', e' ≤ e → e' < dffLen clk d crn → riseAt clk e' = true →
      ∀ u, e' - 2 ≤ u → u ≤ e' → d.getD u false = d.getD e' false)
    (hsep : ∀ e', LastEdge clk e' (e - 3) → e' + 3 ≤ e - 3) :
    (dffOut clk d crn).getD t false = d.getD e false ∨
      (dffOut clk d crn).getD t false = (dffOut clk d crn).getD e false := by
  rcases Nat.eq_or_lt_of_le het with rfl | hlt
  · exact Or.inr rfl
  have hel : e < dffLen clk d crn := by omega
  obtain ⟨he3, hlow, hhigh⟩ := hpulse e hel hrise
  have hRe : R + 3 ≤ e := hreset e hel hrise
  -- the value at the edge: the circuit is settled from the previous edge, and three instants
  -- of low clock carry that value to the edge itself
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 3 := ⟨e - 3, by omega⟩
  simp only [Nat.add_sub_cancel] at hsep
  obtain ⟨D, c, hgood⟩ := settled_at hR (by omega) (by omega) hclear hreset hpulse
    (fun e' h1 h2 h3 => hstable e' (by omega) h2 h3) hsep
  have hg1 : good (dffRun clk d crn (m + 2)) D false = true :=
    good_step_low (good_step_low hgood (hlow m (by omega) (by omega))
      (hclear.2 m (by omega) (by omega))) (hlow (m + 1) (by omega) (by omega))
      (hclear.2 (m + 1) (by omega) (by omega))
  have hg2 : good (dffRun clk d crn (m + 3)) D false :=
    good_step_low hg1 (hlow (m + 2) (by omega) (by omega))
      (hclear.2 (m + 2) (by omega) (by omega))
  -- so the output at the edge is that value, and the window carries it or the new one
  obtain ⟨w, rfl⟩ : ∃ w, t = w + 1 := ⟨t - 1, by omega⟩
  rw [dffOut_getD _ _ _ (by omega), dffOut_getD _ _ _ (by omega)]
  show and2 _ _ = _ ∨ and2 _ _ = and2 _ _
  rw [hclear.2 w (by omega) (by omega), hclear.2 (m + 2) (by omega) (by omega), and2, and2]
  simp only [Bool.and_true]
  rw [good_n5 hg1, ← good_n5 hg2]
  exact run_window he3 (by omega) (by omega) hlow
    (fun u h1 h2 => hhigh u h1 (by omega) (by omega))
    (hstable (m + 3) (Nat.le_refl _) hel hrise) (fun u h1 h2 => hclear.2 u (by omega) (by omega))
    ⟨D, c, by simpa using hgood⟩

/-- **Where the assumption starts.**  The netlist satisfies the settling contract with
`stl = kq = 4` whenever its data is stable over the aperture of every edge --- which is what
`TimedProof.edge_value` discharges for every register of the bank.  So `Timed.settlingDff` and
the netlist differ in exactly one place: what happens at an edge whose data moved.  That is the
whole of what this development assumes about metastability, and `Metastability.lean` shows it
cannot be removed. -/
theorem dffOut_settleOut {clk d crn : List Bool} {R : Nat} (hR : 2 ≤ R)
    (hclear : ClearOK R crn (dffLen clk d crn))
    (hreset : ResetOK (R + 3) clk (dffLen clk d crn))
    (hpulse : PulseOK 3 clk (dffLen clk d crn))
    (hstable : ∀ e, e < dffLen clk d crn → riseAt clk e = true →
      StableOn (fun u => d.getD u false) d.length (e - 1 - 1) e) :
    SettleOut 4 1 4 clk (fun u => d.getD u false) d.length (dffOut clk d crn) := by
  have hreg := dffOut_regOut hR hclear hreset hpulse
  refine ⟨hreg, fun t ht e hle hk => ?_⟩
  have htl : t < dffLen clk d crn + 1 := by rw [← dffOut_length clk d crn]; exact ht
  have hel : e < dffLen clk d crn := by have := hle.1; omega
  have hst := hstable e hel hle.2.1
  have hone : ∀ u, e + 4 ≤ u → u < (dffOut clk d crn).length → LastEdge clk e u →
      (dffOut clk d crn).getD u false = d.getD e false :=
    fun u h1 h2 h3 => (hreg.2 u h2).2 e h3 hst h1
  have h4 : LastEdge clk e (e + 4) := ⟨by omega, hle.2.1, fun e' k1 k2 => hle.2.2 e' k1 (by omega)⟩
  have h1 : (dffOut clk d crn).getD t false = d.getD e false := hone t hk ht hle
  have h2 : (dffOut clk d crn).getD (e + 4) false = d.getD e false :=
    hone (e + 4) (Nat.le_refl _) (Nat.lt_of_le_of_lt hk ht) h4
  exact ⟨by rw [h1, h2], Or.inl h2⟩

end Graphiti.AsyncFifo.Dff
