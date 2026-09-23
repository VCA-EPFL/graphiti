/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.EnReg
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.DffTiming

/-!
# What the memory cell does in time

The cell is a flip-flop fed by a multiplexer that reads the flip-flop's own output, so its
eleven gates had to be given one automaton (`EnReg.lean`).  This file takes that apart again:
the six flip-flop wires of `enRun` are `Dff.dffRun` driven by the multiplexer's stream
(`enRun_ff`), so every theorem of `DffTiming.lean` applies to the cell with `d := mStream`, and
what remains is only what the multiplexer does.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.EnReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Dff

/-! ### What a write is -/

/-- A write to the cell: a rising edge whose enable and data were stable over the setup window,
with the enable high.  This is `Contracts.WriteEdge` for one cell. -/
def WriteAt (clk en dat : List Bool) (dlen su e : Nat) : Prop :=
  riseAt clk e = true ∧
  StableOn (fun u => en.getD u false) dlen (e - su - 1) e ∧
  StableOn (fun u => dat.getD u false) dlen (e - su - 1) e ∧
  en.getD e false = true

/-- Every edge so far was clean for the cell: the enable was stable over its setup window, and
so was the data when it was writing.  This is `Contracts.CleanWrites` for one cell. -/
def CleanCell (clk en dat : List Bool) (dlen su t : Nat) : Prop :=
  ∀ e, e < t → riseAt clk e = true →
    StableOn (fun u => en.getD u false) dlen (e - su - 1) e ∧
    (en.getD e false = true → StableOn (fun u => dat.getD u false) dlen (e - su - 1) e)

/-! ### What the multiplexer shows

The multiplexer is two gates deep, so its stream at `t` is built from the enable and the data at
`t - 2` and `t - 3`, and from the cell's own output at `t - 2`.  That is why the cell's setup
window is wider than the flip-flop's. -/

theorem mStream_val {clk en dat crn : List Bool} {t : Nat} (h3 : 3 ≤ t)
    (ht : t < enLen clk en dat crn) :
    (mStream clk en dat crn).getD t false =
      or2 (and2 (en.getD (t - 2) false) (dat.getD (t - 2) false))
        (and2 (not (en.getD (t - 3) false)) ((enOut clk en dat crn).getD (t - 2) false)) := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 3 := ⟨t - 3, by omega⟩
  rw [mStream_getD ht, enOut_getD _ _ _ _ (by omega)]
  simp only [show u + 3 - 2 = u + 1 by omega, show u + 3 - 3 = u by omega]
  simp only [enRun, run_succ, enStep, enInp]

/-- At a clean edge the multiplexer shows the data if the enable is high, and what the cell
already held otherwise. -/
theorem mStream_at_edge {clk en dat crn : List Bool} {e : Nat} (he : 6 ≤ e)
    (hel : e < enLen clk en dat crn)
    (hen : StableOn (fun u => en.getD u false) (enLen clk en dat crn) (e - 5 - 1) e)
    (hdat : en.getD e false = true →
      StableOn (fun u => dat.getD u false) (enLen clk en dat crn) (e - 5 - 1) e) :
    (mStream clk en dat crn).getD e false =
      if en.getD e false = true then dat.getD e false
      else (enOut clk en dat crn).getD (e - 2) false := by
  have hen' : ∀ u, e - 5 - 1 ≤ u → u ≤ e → en.getD u false = en.getD e false :=
    fun u h1 h2 => hen.2 u h1 h2
  rw [mStream_val (by omega) hel, hen' (e - 2) (by omega) (by omega),
    hen' (e - 3) (by omega) (by omega)]
  cases hb : en.getD e false
  · simp [or2, and2]
  · have hdat' : ∀ u, e - 5 - 1 ≤ u → u ≤ e → dat.getD u false = dat.getD e false :=
      fun u h1 h2 => (hdat hb).2 u h1 h2
    rw [hdat' (e - 2) (by omega) (by omega)]
    simp [or2, and2]

/-- The multiplexer's stream is stable over the flip-flop's setup window, provided the enable
and the data were stable over the cell's own (wider) window and the cell's output has settled. -/
theorem mStream_stable {clk en dat crn : List Bool} {e : Nat} (he : 6 ≤ e)
    (hel : e < enLen clk en dat crn)
    (hen : StableOn (fun u => en.getD u false) (enLen clk en dat crn) (e - 5 - 1) e)
    (hdat : en.getD e false = true →
      StableOn (fun u => dat.getD u false) (enLen clk en dat crn) (e - 5 - 1) e)
    (hq : ∀ u, e - 4 ≤ u → u ≤ e - 2 →
      (enOut clk en dat crn).getD u false = (enOut clk en dat crn).getD (e - 2) false) :
    StableOn (fun u => (mStream clk en dat crn).getD u false) (enLen clk en dat crn)
      (e - 1 - 1) e := by
  have hen' : ∀ u, e - 5 - 1 ≤ u → u ≤ e → en.getD u false = en.getD e false :=
    fun u h1 h2 => hen.2 u h1 h2
  refine ⟨hel, fun u h1 h2 => ?_⟩
  show (mStream clk en dat crn).getD u false = (mStream clk en dat crn).getD e false
  rw [mStream_val (by omega) (by omega), mStream_val (by omega) hel,
    hen' (u - 2) (by omega) (by omega), hen' (u - 3) (by omega) (by omega),
    hen' (e - 2) (by omega) (by omega), hen' (e - 3) (by omega) (by omega),
    hq (u - 2) (by omega) (by omega)]
  cases hb : en.getD e false
  · rfl
  · have hdat' : ∀ w, e - 5 - 1 ≤ w → w ≤ e → dat.getD w false = dat.getD e false :=
      fun w h3 h4 => (hdat hb).2 w h3 h4
    rw [hdat' (u - 2) (by omega) (by omega), hdat' (e - 2) (by omega) (by omega)]

/-! ### The cell's contract

The flip-flop's theorems give the value at the edge; what the multiplexer put there is the
cell's own value, so the two have to be untangled by one induction along the stream.  That is
the same shape as `TimedProof.lean`'s treatment of the write domain's state loop, one level
down. -/

/-- If something happens below `N`, there is a last time it happens. -/
theorem exists_last (P : Nat → Prop) (N : Nat) (h : ∃ w, w < N ∧ P w) :
    ∃ w, w < N ∧ P w ∧ ∀ w', w < w' → w' < N → ¬ P w' := by
  classical
  induction N with
  | zero => obtain ⟨w, hw, _⟩ := h; omega
  | succ N ih =>
    by_cases hN : P N
    · exact ⟨N, by omega, hN, fun w' h1 h2 => by omega⟩
    · obtain ⟨w, hw1, hw2⟩ := h
      have hwN : w < N := by
        rcases Nat.lt_or_ge w N with h' | h'
        · exact h'
        · exact absurd ((show w = N by omega) ▸ hw2) hN
      obtain ⟨w', k1, k2, k3⟩ := ih ⟨w, hwN, hw2⟩
      refine ⟨w', by omega, k2, fun w'' h1 h2 => ?_⟩
      rcases Nat.lt_or_ge w'' N with h3 | h3
      · exact k3 w'' h1 h3
      · exact (show w'' = N by omega) ▸ hN

/-- The filters the cell needs: the flip-flop's, clean enables, and a clock slow enough that the
cell's output has settled before the next edge reaches the multiplexer. -/
structure CellOK (clk en dat crn : List Bool) (R : Nat) : Prop where
  hR : 6 ≤ R
  clear : ClearOK R crn (enLen clk en dat crn)
  reset : ResetOK (R + 3) clk (enLen clk en dat crn)
  pulse : PulseOK 3 clk (enLen clk en dat crn)
  period : ClockOK 12 clk (enLen clk en dat crn)

variable {clk en dat crn : List Bool} {R : Nat}

/-- The cell's output is the flip-flop's output over the multiplexer's stream. -/
theorem cell_regOut (H : CellOK clk en dat crn R) :
    RegOut 4 1 false clk (fun u => (mStream clk en dat crn).getD u false)
      (enLen clk en dat crn) (enOut clk en dat crn) := by
  have h := dffOut_regOut (clk := clk) (d := mStream clk en dat crn) (crn := crn) (R := R)
    (by have := H.hR; omega) (by rw [dffLen_mStream]; exact H.clear)
    (by rw [dffLen_mStream]; exact H.reset) (by rw [dffLen_mStream]; exact H.pulse)
  rwa [mStream_length, ← enOut_eq] at h

/-- **What the cell holds**: low until it is first written to, and the data of the last write
from four instants after that write until the next one. -/
theorem cell_value (H : CellOK clk en dat crn R) :
    ∀ t, t ≤ enLen clk en dat crn → CleanCell clk en dat (enLen clk en dat crn) 5 t →
      ((∀ e, e < t → ¬ WriteAt clk en dat (enLen clk en dat crn) 5 e) →
        (enOut clk en dat crn).getD t false = false) ∧
      (∀ e, e < t → WriteAt clk en dat (enLen clk en dat crn) 5 e →
        (∀ e', e < e' → e' < t → ¬ WriteAt clk en dat (enLen clk en dat crn) 5 e') →
        e + 4 ≤ t → (enOut clk en dat crn).getD t false = dat.getD e false) := by
  have hreg := cell_regOut H
  have hlen : (enOut clk en dat crn).length = enLen clk en dat crn + 1 := enOut_length _ _ _ _
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro htL hclean
    have htq : t < (enOut clk en dat crn).length := by omega
    -- the multiplexer is stable at every edge below `t`, because the cell has settled by then
    have hstab : ∀ e', e' < t → e' < enLen clk en dat crn → riseAt clk e' = true →
        ∀ u, e' - 2 ≤ u → u ≤ e' →
          (mStream clk en dat crn).getD u false = (mStream clk en dat crn).getD e' false := by
      intro e' h1 h2 h3
      have hRe : R + 3 ≤ e' := H.reset e' h2 h3
      have hcl := hclean e' h1 h3
      have hR6 := H.hR
      refine (mStream_stable (by omega) h2 hcl.1 hcl.2 ?_).2
      -- the cell has settled: the previous edge is twelve instants back
      intro u hu1 hu2
      have hprev : ∀ w, w < e' - 2 → riseAt clk w = true → w + 12 ≤ e' :=
        fun w hw hrw => H.period w e' (by omega) h2 hrw h3
      by_cases hex : ∃ w, w < e' - 2 ∧ WriteAt clk en dat (enLen clk en dat crn) 5 w
      · obtain ⟨w, hw1, hw2, hw3⟩ := exists_last _ _ hex
        have hw12 : w + 12 ≤ e' := hprev w hw1 hw2.1
        rw [(ih u (by omega) (by omega) (fun w' k1 => hclean w' (by omega))).2 w (by omega) hw2
              (fun w' k1 k2 => hw3 w' k1 (by omega)) (by omega),
          (ih (e' - 2) (by omega) (by omega) (fun w' k1 => hclean w' (by omega))).2 w (by omega)
            hw2 hw3 (by omega)]
      · push Not at hex
        rw [(ih u (by omega) (by omega) (fun w' k1 => hclean w' (by omega))).1
              (fun w k1 => hex w (by omega)),
          (ih (e' - 2) (by omega) (by omega) (fun w' k1 => hclean w' (by omega))).1
            (fun w k1 => hex w k1)]
    by_cases hno : NoEdge clk t
    · refine ⟨fun _ => (hreg.2 t htq).1 hno, fun e he hwe _ _ => ?_⟩
      exact absurd (hno e he) (by rw [hwe.1]; simp)
    · obtain ⟨e₁, he₁⟩ := exists_lastEdge hno
      have he₁t : e₁ < t := he₁.1
      have he₁L : e₁ < enLen clk en dat crn := by omega
      have hRe : R + 3 ≤ e₁ := H.reset e₁ he₁L he₁.2.1
      have hcl := hclean e₁ he₁t he₁.2.1
      have hR6 := H.hR
      have hmx := mStream_at_edge (clk := clk) (en := en) (dat := dat) (crn := crn) (e := e₁)
        (by omega) he₁L hcl.1 hcl.2
      have hsep : ∀ w, LastEdge clk w (e₁ - 3) → w + 3 ≤ e₁ - 3 := by
        intro w hwl
        have := H.period w e₁ (by have := hwl.1; omega) he₁L hwl.2.1 he₁.2.1
        omega
      by_cases hset : e₁ + 4 ≤ t
      · -- settled: the flip-flop shows what the multiplexer had at the edge
        have hq : (enOut clk en dat crn).getD t false = (mStream clk en dat crn).getD e₁ false :=
          (hreg.2 t htq).2 e₁ he₁ ⟨he₁L, fun u k1 k2 => hstab e₁ he₁t he₁L he₁.2.1 u k1 k2⟩ hset
        cases hb : en.getD e₁ false
        · -- not a write: the multiplexer handed back what the cell already held
          have hnw : ¬ WriteAt clk en dat (enLen clk en dat crn) 5 e₁ := by
            intro hc; rw [hc.2.2.2] at hb; exact Bool.noConfusion hb
          rw [hq, hmx, hb]
          simp only [Bool.false_eq_true, if_false]
          refine ⟨fun hnone => (ih (e₁ - 2) (by omega) (by omega) (fun w k1 => hclean w (by omega))).1
              (fun w k => hnone w (by omega)), fun e he hwe hlast hk => ?_⟩
          have hlt : e < e₁ := by
            rcases Nat.lt_trichotomy e e₁ with h | h | h
            · exact h
            · exact absurd (h ▸ hwe) hnw
            · exact absurd (he₁.2.2 e h he) (by rw [hwe.1]; simp)
          have h12 : e + 12 ≤ e₁ := H.period e e₁ hlt he₁L hwe.1 he₁.2.1
          exact (ih (e₁ - 2) (by omega) (by omega) (fun w k1 => hclean w (by omega))).2 e (by omega) hwe
            (fun w k1 k2 => hlast w k1 (by omega)) (by omega)
        · -- a write: the multiplexer handed over the data
          have hwe₁ : WriteAt clk en dat (enLen clk en dat crn) 5 e₁ :=
            ⟨he₁.2.1, hcl.1, hcl.2 hb, hb⟩
          refine ⟨fun hnone => absurd hwe₁ (hnone e₁ he₁t), fun e he hwe hlast hk => ?_⟩
          have : e = e₁ := by
            rcases Nat.lt_trichotomy e e₁ with h | h | h
            · exact absurd hwe₁ (hlast e₁ h he₁t)
            · exact h
            · exact absurd (he₁.2.2 e h he) (by rw [hwe.1]; simp)
          subst this
          rw [hq, hmx, hb]
          simp
      · -- inside the clock-to-q window: the output is what it had at the edge, or what the
        -- multiplexer brought, and with no write at this edge those are the same value
        have hwin := dffOut_window (clk := clk) (d := mStream clk en dat crn) (crn := crn)
          (R := R) (e := e₁) (t := t) (by have := H.hR; omega) (by omega) (by omega)
          (by rw [dffLen_mStream]; omega) he₁.2.1
          (by rw [dffLen_mStream]; exact H.clear) (by rw [dffLen_mStream]; exact H.reset)
          (by rw [dffLen_mStream]; exact H.pulse)
          (fun e' k1 k2 k3 u k4 k5 => hstab e' (by omega) (by rwa [dffLen_mStream] at k2) k3 u k4 k5)
          hsep
        rw [← enOut_eq] at hwin
        refine ⟨fun hnone => ?_, fun e he hwe hlast hk => ?_⟩
        · have hb : en.getD e₁ false = false := by
            cases hb : en.getD e₁ false
            · rfl
            · exact absurd ⟨he₁.2.1, hcl.1, hcl.2 hb, hb⟩ (hnone e₁ he₁t)
          have h1 : (enOut clk en dat crn).getD e₁ false = false :=
            (ih e₁ he₁t (by omega) (fun w k1 => hclean w (by omega))).1 (fun w k => hnone w (by omega))
          have h2 : (mStream clk en dat crn).getD e₁ false = false := by
            rw [hmx, hb]
            simp only [Bool.false_eq_true, if_false]
            exact (ih (e₁ - 2) (by omega) (by omega) (fun w k1 => hclean w (by omega))).1 (fun w k => hnone w (by omega))
          rcases hwin with h | h
          · rw [h, h2]
          · rw [h, h1]
        · have hlt : e < e₁ := by
            rcases Nat.lt_trichotomy e e₁ with h | h | h
            · exact h
            · omega
            · exact absurd (he₁.2.2 e h he) (by rw [hwe.1]; simp)
          have h12 : e + 12 ≤ e₁ := H.period e e₁ hlt he₁L hwe.1 he₁.2.1
          have hb : en.getD e₁ false = false := by
            cases hb : en.getD e₁ false
            · rfl
            · exact absurd ⟨he₁.2.1, hcl.1, hcl.2 hb, hb⟩ (hlast e₁ hlt he₁t)
          have h1 : (enOut clk en dat crn).getD e₁ false = dat.getD e false :=
            (ih e₁ he₁t (by omega) (fun w k1 => hclean w (by omega))).2 e hlt hwe (fun w k1 k2 => hlast w k1 (by omega)) (by omega)
          have h2 : (mStream clk en dat crn).getD e₁ false = dat.getD e false := by
            rw [hmx, hb]
            simp only [Bool.false_eq_true, if_false]
            exact (ih (e₁ - 2) (by omega) (by omega) (fun w k1 => hclean w (by omega))).2 e (by omega) hwe
              (fun w k1 k2 => hlast w k1 (by omega)) (by omega)
          rcases hwin with h | h
          · rw [h, h2]
          · rw [h, h1]

end Graphiti.AsyncFifo.EnReg
