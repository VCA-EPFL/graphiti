/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.StreamsLemmas
import Graphiti.Projects.AsyncFifo.TopSpec

/-! # `TopSpec`: the lemmas

Facts about the definitions in `TopSpec.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo
variable {α : Type} [Inhabited α]

theorem ClockOK.mono {P : Nat} {c : List Bool} {T T' : Nat} (h : ClockOK P c T') (hT : T ≤ T') :
    ClockOK P c T :=
  fun e e' h1 h2 h3 h4 => h e e' h1 (by lia) h3 h4

theorem ClockOK.congr {P : Nat} {c c' : List Bool} {T : Nat} (hc : c <+: c') (hT : T ≤ c.length) :
    ClockOK P c' T → ClockOK P c T := by
  intro h e e' h1 h2 h3 h4
  exact h e e' h1 h2 (by rw [← riseAt_prefix hc (by lia)]; exact h3) (by rw [← riseAt_prefix hc (by lia)]; exact h4)

theorem InOK.mono {β : Type} [Inhabited β] {S : Nat} {clk : List Bool} {x : List β} {T T' : Nat}
    (h : InOK S clk x T') (hT : T ≤ T') : InOK S clk x T :=
  fun e he hr => h e (by lia) hr

theorem InOK.congr {β : Type} [Inhabited β] {S : Nat} {clk clk' : List Bool} {x x' : List β} {T : Nat}
    (hc : clk <+: clk') (hx : x <+: x') (hT : T ≤ clk.length) (hT' : T ≤ x.length) :
    InOK S clk' x' T → InOK S clk x T := by
  intro h e he hr u hu1 hu2
  have := h e he (by rw [← riseAt_prefix hc (by lia)]; exact hr) u hu1 hu2
  rwa [hx.getD_eq_left (by lia), hx.getD_eq_left (by lia)]

theorem PulseOK.mono {w : Nat} {clk : List Bool} {T T' : Nat} (h : PulseOK w clk T') (hT : T ≤ T') :
    PulseOK w clk T := by
  intro e he hr
  obtain ⟨h1, h2, h3⟩ := h e (by omega) hr
  exact ⟨h1, h2, fun u k1 k2 k3 => h3 u k1 k2 (by omega)⟩

/-- The pulse filter transfers to a longer stream: it only looks at instants below `T`. -/
theorem PulseOK.congr' {w : Nat} {clk clk' : List Bool} {T : Nat} (hc : clk <+: clk')
    (hT : T ≤ clk.length) (h : PulseOK w clk T) : PulseOK w clk' T := by
  intro e he hr
  have hec : e < clk.length := by omega
  obtain ⟨h1, h2, h3⟩ := h e he (by rw [riseAt_prefix hc hec]; exact hr)
  refine ⟨h1, fun u k1 k2 => ?_, fun u k1 k2 k3 => ?_⟩
  · rw [← hc.getD_eq_left (show u < clk.length by omega)]; exact h2 u k1 k2
  · rw [← hc.getD_eq_left (show u < clk.length by omega)]; exact h3 u k1 k2 k3

theorem PulseOK.congr {w : Nat} {clk clk' : List Bool} {T : Nat} (hc : clk <+: clk')
    (hT : T ≤ clk.length) (h : PulseOK w clk' T) : PulseOK w clk T := by
  intro e he hr
  have hec : e < clk.length := by omega
  obtain ⟨h1, h2, h3⟩ := h e he (by rwa [← riseAt_prefix hc hec])
  refine ⟨h1, fun u k1 k2 => ?_, fun u k1 k2 k3 => ?_⟩
  · rw [hc.getD_eq_left (by omega)]; exact h2 u k1 k2
  · rw [hc.getD_eq_left (by omega)]; exact h3 u k1 k2 k3

theorem ResetOK.mono {R : Nat} {clk : List Bool} {T T' : Nat} (h : ResetOK R clk T') (hT : T ≤ T') :
    ResetOK R clk T :=
  fun e he hr => h e (by lia) hr

theorem ResetOK.congr {R : Nat} {clk clk' : List Bool} {T : Nat} (hc : clk <+: clk') (hT : T ≤ clk.length) :
    ResetOK R clk' T → ResetOK R clk T := by
  intro h e he hr
  exact h e he (by rw [← riseAt_prefix hc (by lia)]; exact hr)

theorem ClearOK.mono {R : Nat} {crn : List Bool} {T T' : Nat} (h : ClearOK R crn T') (hT : T ≤ T') :
    ClearOK R crn T :=
  ⟨h.1, fun u k1 k2 => h.2 u k1 (by omega)⟩

theorem ClearOK.congr {R : Nat} {crn crn' : List Bool} {T : Nat} (hc : crn <+: crn')
    (hT : T ≤ crn.length) (h : ClearOK R crn' T) : ClearOK R crn T :=
  ⟨fun u hu => by
     by_cases h' : u < crn.length
     · rw [hc.getD_eq_left h']; exact h.1 u hu
     · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl,
   fun u k1 k2 => by rw [hc.getD_eq_left (by omega)]; exact h.2 u k1 k2⟩

/-! ### Weakening the filters

Each filter is weaker for a smaller parameter, which is what lets a block ask for less than
the domain assumes: a clock kept `P` apart is kept `12` apart, a pulse `pw` wide is `3` wide. -/

theorem ClockOK.weaken {P P' : Nat} {c : List Bool} {T : Nat} (h : ClockOK P c T) (hP : P' ≤ P) :
    ClockOK P' c T :=
  fun e e' h1 h2 h3 h4 => Nat.le_trans (by lia) (h e e' h1 h2 h3 h4)

theorem ResetOK.weaken {R R' : Nat} {clk : List Bool} {T : Nat} (h : ResetOK R clk T) (hR : R' ≤ R) :
    ResetOK R' clk T :=
  fun e he hr => Nat.le_trans hR (h e he hr)

theorem PulseOK.weaken {w w' : Nat} {clk : List Bool} {T : Nat} (h : PulseOK w clk T) (hw : w' ≤ w) :
    PulseOK w' clk T := by
  intro e he hr
  obtain ⟨h1, h2, h3⟩ := h e he hr
  exact ⟨by lia, fun u k1 k2 => h2 u (by lia) k2, fun u k1 k2 k3 => h3 u k1 (by lia) k3⟩

theorem enqAt_congr {wclk wclk' winc winc' full full' : List Bool} {t : Nat}
    (h₁ : wclk <+: wclk') (h₂ : winc <+: winc') (h₃ : full <+: full')
    (l₁ : t < wclk.length) (l₂ : t < winc.length) (l₃ : t < full.length) :
    enqAt wclk winc full t = enqAt wclk' winc' full' t := by
  unfold enqAt
  rw [riseAt_prefix h₁ l₁, h₂.getD_eq_left l₂, h₃.getD_eq_left l₃]

theorem deqAt_congr {rclk rclk' rinc rinc' empty empty' : List Bool} {t : Nat}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : empty <+: empty')
    (l₁ : t < rclk.length) (l₂ : t < rinc.length) (l₃ : t < empty.length) :
    deqAt rclk rinc empty t = deqAt rclk' rinc' empty' t := by
  unfold deqAt
  rw [riseAt_prefix h₁ l₁, h₂.getD_eq_left l₂, h₃.getD_eq_left l₃]

theorem enqs_congr {wclk wclk' winc winc' full full' : List Bool} {wdata wdata' : List α} {T : Nat}
    (h₁ : wclk <+: wclk') (h₂ : winc <+: winc') (h₃ : wdata <+: wdata') (h₄ : full <+: full')
    (l₁ : T ≤ wclk.length) (l₂ : T ≤ winc.length) (l₃ : T ≤ wdata.length) (l₄ : T ≤ full.length) :
    enqs wclk winc wdata full T = enqs wclk' winc' wdata' full' T := by
  unfold enqs
  apply events_congr
  intro t ht
  exact ⟨enqAt_congr h₁ h₂ h₄ (by lia) (by lia) (by lia), h₃.getD_eq_left (by lia) _⟩

theorem deqs_congr {rclk rclk' rinc rinc' empty empty' : List Bool} {rdata rdata' : List α} {T : Nat}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : empty <+: empty') (h₄ : rdata <+: rdata')
    (l₁ : T ≤ rclk.length) (l₂ : T ≤ rinc.length) (l₃ : T ≤ empty.length) (l₄ : T ≤ rdata.length) :
    deqs rclk rinc empty rdata T = deqs rclk' rinc' empty' rdata' T := by
  unfold deqs
  apply events_congr
  intro t ht
  exact ⟨deqAt_congr h₁ h₂ h₃ (by lia) (by lia) (by lia), h₄.getD_eq_left (by lia) _⟩
namespace FifoIO

/-- Componentwise information order. -/
structure le (s s' : FifoIO α) : Prop where
  wclk : s.wclk <+: s'.wclk
  winc : s.winc <+: s'.winc
  wdata : s.wdata <+: s'.wdata
  rclk : s.rclk <+: s'.rclk
  rinc : s.rinc <+: s'.rinc
  full : s.full <+: s'.full
  empty : s.empty <+: s'.empty
  rdata : s.rdata <+: s'.rdata

omit [Inhabited α] in
theorem le.known {s s' : FifoIO α} (h : s.le s') {T : Nat} (hT : s.known T) : s'.known T := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have := h1.length_le; have := h2.length_le; have := h3.length_le; have := h4.length_le
  have := h5.length_le; have := h6.length_le; have := h7.length_le; have := h8.length_le
  unfold FifoIO.known at *
  lia
end FifoIO

/-- `FifoOK` is prefix-closed: it only gets weaker when signals are truncated. -/
theorem FifoOK.mono {P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat} {s s' : FifoIO α}
    (h : FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r s') (hle : s.le s') :
    FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r s := by
  intro T hT hw hr hi1 hi2 hi3 hrw hrr hpw hpr
  have hT' : s'.known T := hle.known hT
  obtain ⟨hmin1, hmin2, hmin3, hmin4, hmin5, hmin6, hmin7, hmin8⟩ := hT
  have hi1' : InOK S_w s'.wclk s'.winc T := by
    intro e he hre u hu1 hu2
    have := hi1 e he (by rw [riseAt_prefix hle.wclk (by lia)]; exact hre) u hu1 hu2
    rwa [← hle.winc.getD_eq_left (by lia), ← hle.winc.getD_eq_left (by lia)]
  have hi2' : InOK S_w s'.wclk s'.wdata T := by
    intro e he hre u hu1 hu2
    have := hi2 e he (by rw [riseAt_prefix hle.wclk (by lia)]; exact hre) u hu1 hu2
    rwa [← hle.wdata.getD_eq_left (by lia), ← hle.wdata.getD_eq_left (by lia)]
  have hi3' : InOK S_r s'.rclk s'.rinc T := by
    intro e he hre u hu1 hu2
    have := hi3 e he (by rw [riseAt_prefix hle.rclk (by lia)]; exact hre) u hu1 hu2
    rwa [← hle.rinc.getD_eq_left (by lia), ← hle.rinc.getD_eq_left (by lia)]
  have hw' : ClockOK P_w s'.wclk T := by
    intro e e' h1 h2 h3 h4
    exact hw e e' h1 h2 (by rw [riseAt_prefix hle.wclk (by lia)]; exact h3)
      (by rw [riseAt_prefix hle.wclk (by lia)]; exact h4)
  have hr' : ClockOK P_r s'.rclk T := by
    intro e e' h1 h2 h3 h4
    exact hr e e' h1 h2 (by rw [riseAt_prefix hle.rclk (by lia)]; exact h3)
      (by rw [riseAt_prefix hle.rclk (by lia)]; exact h4)
  have hrw' : ResetOK R_w s'.wclk T := fun e he hre =>
    hrw e he (by rw [riseAt_prefix hle.wclk (by lia)]; exact hre)
  have hrr' : ResetOK R_r s'.rclk T := fun e he hre =>
    hrr e he (by rw [riseAt_prefix hle.rclk (by lia)]; exact hre)
  have hpw' : PulseOK pw_w s'.wclk T := hpw.congr' hle.wclk (by lia)
  have hpr' : PulseOK pw_r s'.rclk T := hpr.congr' hle.rclk (by lia)
  have e : s.enqs T = s'.enqs T :=
    enqs_congr hle.wclk hle.winc hle.wdata hle.full (by lia) (by lia) (by lia) (by lia)
  have d : s.deqs T = s'.deqs T :=
    deqs_congr hle.rclk hle.rinc hle.empty hle.rdata (by lia) (by lia) (by lia) (by lia)
  rw [e, d]
  exact h T hT' hw' hr' hi1' hi2' hi3' hrw' hrr' hpw' hpr'
end Graphiti.AsyncFifo