/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Filtered

/-!
# The global invariant and the FIFO theorem

The composed circuit stores ten streams (`Wires`): the five inputs of the write domain and the
five of the read domain.  `ConsistentF` says that the three cross-domain wires satisfy the
*relaxed* relations of `Filtered.lean` with respect to the domain driving them: exact when
that domain's registers have settled, glitch-free (each bit old or new) inside a clk-to-q
window, unconstrained once the driving domain's timing assumptions were violated.

`fifo_correctF` then shows that any output streams satisfying the relaxed relations make the
FIFO specification `FifoOK P_w P_r S_w S_r` hold, provided

* the synchronisers settle within a period (`stl < P`), and
* a clk-to-q window followed by a sampling window fits in a period (`kq + su < P`),

for both clocks.  The heart of the argument is `sample_choice`: whatever a sampler sees
through a wire inside these windows — a mixture of old and new bits of a Gray pointer that is
itself still settling — is the Gray code of a count between the two counts the driver held
at the ends of the window, and those counts differ by at most one because the driver's clock
respects its period.  The memory needs the second synchroniser stage to lag one edge
behind the first (`RInv.ep2`), so that a dequeued entry was written at least a period ago.

The exact wires of `Domains.lean` are the special case `kq = 0` (`fifo_correct`).
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

open Gray

/-- The ten streams stored by the two domains of the composed circuit. -/
structure Wires (α : Type) (n : Nat) where
  wclk : List Bool
  winc : List Bool
  wdata : List α
  rgray_w : List (BitVec (n+1))
  orcw : List (Orc n)
  rclk : List Bool
  rinc : List Bool
  wgray_r : List (BitVec (n+1))
  orcr : List (Orc n)
  mem_r : List (BitVec n → α)

/-! ### Counting through windows -/

/-- Per-bit choices among the Gray codes of the counts held over a window in which the count
changed at most once are the Gray code of a count inside the window. -/
theorem sample_choice {n : Nat} {c : Nat → Nat} (hmono : ∀ x y, x ≤ y → c x ≤ c y) {a b : Nat} (hab : a ≤ b)
    (hwin : c b ≤ c a + 1) {j : BitVec (n+1)}
    (h : ∀ i, ∃ x, a ≤ x ∧ x ≤ b ∧ j.getLsbD i = (gray (BitVec.ofNat (n+1) (c x))).getLsbD i) :
    ∃ k₀, j = gray (BitVec.ofNat (n+1) k₀) ∧ c a ≤ k₀ ∧ k₀ ≤ c b := by
  apply gray_choice_counter (kp := c a) (k := c b) _ (hmono a b hab) hwin
  intro i
  obtain ⟨x, hax, hxb, hi⟩ := h i
  have h1 := hmono a x hax
  have h2 := hmono x b hxb
  rcases Nat.lt_or_ge (c x) (c b) with hlt | hge
  · right; rw [hi]; congr 3; lia
  · left; rw [hi]; congr 3; lia

/-- What a relaxed Gray-pointer wire shows, read through a wire of latency `lat` at instant
`u`: every bit is a bit of the Gray code of the driver's count at some instant of the window
`[u - lat - kq, u - lat]` (the driver's count is `c`). -/
theorem sample_bit {n : Nat} {v : List (BitVec (n+1))} {c : Nat → Nat} {clk : List Bool} {kq lat u T : Nat}
    (hv : ∀ y, y < v.length → y ≤ T →
      (Settled kq clk y → v.getD y 0 = gray (BitVec.ofNat (n+1) (c y))) ∧
      (∀ e, LastEdge clk e y → y < e + kq → ∀ i,
        (v.getD y 0).getLsbD i = (gray (BitVec.ofNat (n+1) (c y))).getLsbD i ∨
        (v.getD y 0).getLsbD i = (gray (BitVec.ofNat (n+1) (c e))).getLsbD i))
    (hc0 : c 0 = 0) (hu : lat ≤ u → u - lat < v.length) (huT : u - lat ≤ T) (i : Nat) :
    ∃ x, u - lat - kq ≤ x ∧ x ≤ u - lat ∧
      (delayed lat v u).getLsbD i = (gray (BitVec.ofNat (n+1) (c x))).getLsbD i := by
  unfold delayed
  split
  · refine ⟨0, by lia, Nat.zero_le _, ?_⟩
    rw [hc0]; simp [gray]
  · have hg : v.getD (u - lat) 0#(n+1) = v.getD (u - lat) 0 := rfl
    rw [hg]
    obtain ⟨hs, hw⟩ := hv (u - lat) (hu (by lia)) huT
    by_cases hset : Settled kq clk (u - lat)
    · exact ⟨u - lat, by lia, Nat.le_refl _, by rw [hs hset]⟩
    · obtain ⟨e, he, hk⟩ := not_settled hset
      have he1 := he.1
      rcases hw e he hk i with h | h
      · exact ⟨u - lat, by lia, Nat.le_refl _, h⟩
      · exact ⟨e, by lia, by lia, h⟩

/-- Under the period assumption `kq + su < P`, the instant sampled at the previous edge lies
before the window `[t - lat - su - 1 - kq, t - lat]` of the current sample. -/
theorem SinceInv.sampled_le_window {stl P su kq lat : Nat} {c : List Bool} {t s : Nat} (h : SinceInv stl c t s)
    (hr : riseAt c t = true) (hP : kq + su < P) (hok : ClockOK P c (t + 1)) :
    t - 1 - s - lat ≤ t - lat - su - 1 - kq := by
  rcases h with ⟨_, hs⟩ | ⟨e, ⟨he, hre, _⟩, hs⟩
  · lia
  · have := hok e t he (by lia) hre hr
    lia

/-- The instant sampled at the previous edge lies at least a period before the current edge. -/
theorem SinceInv.sampled_le_period {stl P lat : Nat} {c : List Bool} {t s : Nat} (h : SinceInv stl c t s)
    (hr : riseAt c t = true) (hok : ClockOK P c (t + 1)) :
    t - 1 - s - lat ≤ t + 1 - P - lat - 1 := by
  rcases h with ⟨_, hs⟩ | ⟨e, ⟨he, hre, _⟩, hs⟩
  · lia
  · have := hok e t he (by lia) hre hr
    lia

/-- Two numbers below `2^n` apart with the same residue: the smaller one comes first. -/
theorem le_of_ofNat_eq_of_lt {n x y : Nat} (h : BitVec.ofNat n x = BitVec.ofNat n y) (hlt : x < y + 2 ^ n) :
    x ≤ y := by
  have hm : x % 2 ^ n = y % 2 ^ n := by
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat] using this
  rcases Nat.lt_or_ge y x with hyx | hyx
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hm)
    rcases k with _ | k
    · simp at hk; lia
    · have : 2 ^ n ≤ 2 ^ n * (k + 1) := Nat.le_mul_of_pos_right _ (by lia)
      lia
  · exact hyx

section Invariant

variable {α : Type} [Inhabited α] {n : Nat}
variable (lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq rdly : Nat) (W : Wires α n)

/-- The cross-domain wires satisfy the relaxed relations of the domains driving them. -/
structure ConsistentF : Prop where
  wg : WGrayF lat stl su kq P_w S_w R_w pw_w W.wclk W.winc W.wdata W.rgray_w W.orcw W.wgray_r
  mem : WMemF lat stl su kq P_w S_w R_w pw_w W.wclk W.winc W.wdata W.rgray_w W.orcw W.mem_r
  rg : RGrayF lat stl su kq P_r S_r R_r pw_r W.rclk W.rinc W.wgray_r W.orcr W.rgray_w

/-- The instant at which the value currently held by a first synchroniser stage was sampled
through the wire: the last edge, shifted by the wire latency. -/
def sampledAt (since t : Nat) : Nat := t - 1 - since - lat

/-- The global invariant at instant `t`. -/
structure Inv (t : Nat) : Prop where
  w : WInv (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t)
        (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t)
        (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r
          (sampledAt lat (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).since t)).length
        (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length
  r : RInv (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t) (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t)
        (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
          (sampledAt lat (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since t)).length
        (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t - P_r - lat - 1)).length
  pre : deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t <+: enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t
  wptrs : ∀ t', t' ≤ t → (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t').ptr =
            BitVec.ofNat (n+1) (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t').length
  rptrs : ∀ t', t' ≤ t → (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t').ptr =
            BitVec.ofNat (n+1) (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t').length
  wsince : SinceInv stl W.wclk t (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).since
  rsince : SinceInv stl W.rclk t (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since

theorem Inv.zero : Inv lat stl su P_r W 0 := by
  have h2 := Nat.two_pow_pos n
  refine ⟨⟨rfl, ?_, 0, 0, ?_, ?_, Nat.le_refl _, Nat.zero_le _, ?_, ?_⟩,
          ⟨rfl, 0, 0, ?_, ?_, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _, ?_⟩, ?_, ?_, ?_,
          SinceInv.zero _ _, SinceInv.zero _ _⟩
  · intro i _ hi; simp [enqM] at hi
  · simp [wRun, WReg.init, gray]
  · simp [wRun, WReg.init, gray]
  · simp [enqM]
  · intro; simp [enqM]; lia
  · simp [rRun, RReg.init, gray]
  · simp [rRun, RReg.init, gray]
  · intro h; simp [rRun, RReg.init] at h
  · simp [enqM, deqM]
  · intro t' ht'; have : t' = 0 := by lia
    subst this; simp [wRun, WReg.init, enqM]
  · intro t' ht'; have : t' = 0 := by lia
    subst this; simp [rRun, RReg.init, deqM]

variable {lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq rdly W}

/-- What the write domain samples at a rising edge: the Gray code of a number of dequeues
between the count at the start of its sampling window (extended by the read domain's clk-to-q
window) and the current count. -/
theorem rgray_sample (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W) {t : Nat}
    (hinv : Inv lat stl su P_r W t)
    (hokr : ClockOK P_r W.rclk (t + 1)) (hir : InOK S_r W.rclk W.rinc (t + 1)) (hrr : ResetOK R_r W.rclk (t + 1)) (hpr : PulseOK pw_r W.rclk (t + 1))
    (hkr : kq + su < P_r) (htw : t < wLen lat W.wclk W.winc W.wdata W.rgray_w W.orcw) :
    ∃ k₀, mix (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).orc.sel
        (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rgNew
        (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rgOld = gray (BitVec.ofNat (n+1) k₀) ∧
      (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r (t - lat - su - 1 - kq)).length ≤ k₀ ∧
      k₀ ≤ (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r (t - lat)).length := by
  have hwl := wLen_le lat W.wclk W.winc W.wdata W.rgray_w W.orcw
  have hv : ∀ y, y < W.rgray_w.length → y ≤ t →
      (Settled kq W.rclk y → W.rgray_w.getD y 0 =
        gray (BitVec.ofNat (n+1) (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r y).length)) ∧
      (∀ e, LastEdge W.rclk e y → y < e + kq → ∀ i,
        (W.rgray_w.getD y 0).getLsbD i =
          (gray (BitVec.ofNat (n+1) (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r y).length)).getLsbD i ∨
        (W.rgray_w.getD y 0).getLsbD i =
          (gray (BitVec.ofNat (n+1) (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r e).length)).getLsbD i) := by
    intro y hy hyt
    have hf : RFilter P_r S_r R_r pw_r W.rclk W.rinc y := ⟨hokr.mono (by lia), hir.mono (by lia), hrr.mono (by lia), hpr.mono (by lia)⟩
    obtain ⟨h1, h2⟩ := hc.rg.2 y hy hf
    refine ⟨fun hs => ?_, fun e he hk i => ?_⟩
    · rw [h1 hs, hinv.rptrs y hyt]
    · have he1 := he.1
      have h2 := h2 e he hk i
      rw [hinv.rptrs y hyt, hinv.rptrs e (by lia)] at h2
      exact h2
  apply sample_choice (c := fun x => (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r x).length)
    (fun x y hxy => events_length_mono _ _ hxy) (a := t - lat - su - 1 - kq) (b := t - lat) (by lia)
  · exact events_window (fun u h => rDeq_rise lat stl su W.rclk W.rinc W.wgray_r W.orcr h) (hokr.mono (by lia))
      (by lia) (by lia)
  · intro i
    rcases mix_choice (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).orc.sel
        (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rgNew
        (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rgOld i with h | h
    · rw [h]
      obtain ⟨x, hx1, hx2, hx⟩ := sample_bit (lat := lat) (kq := kq) (u := t) hv (by simp [deqM]) (fun _ => by lia) (by lia) i
      exact ⟨x, by lia, by lia, hx⟩
    · rw [h]
      obtain ⟨x, hx1, hx2, hx⟩ := sample_bit (lat := lat) (kq := kq) (u := t - su - 1) hv (by simp [deqM]) (fun _ => by lia) (by lia) i
      exact ⟨x, by lia, by lia, hx⟩

/-- What the read domain samples at a rising edge, symmetrically. -/
theorem wgray_sample (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W) {t : Nat}
    (hinv : Inv lat stl su P_r W t)
    (hokw : ClockOK P_w W.wclk (t + 1)) (hiw : InOK S_w W.wclk W.winc (t + 1)) (hid : InOK S_w W.wclk W.wdata (t + 1))
    (hrw : ResetOK R_w W.wclk (t + 1)) (hpw : PulseOK pw_w W.wclk (t + 1)) (hkw : kq + su < P_w)
    (htr : t < rLen lat W.rclk W.rinc W.wgray_r W.orcr) :
    ∃ k₀, mix (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).orc.sel
        (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).wgNew
        (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).wgOld = gray (BitVec.ofNat (n+1) k₀) ∧
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t - lat - su - 1 - kq)).length ≤ k₀ ∧
      k₀ ≤ (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t - lat)).length := by
  have hrl := rLen_le lat W.rclk W.rinc W.wgray_r W.orcr
  have hv : ∀ y, y < W.wgray_r.length → y ≤ t →
      (Settled kq W.wclk y → W.wgray_r.getD y 0 =
        gray (BitVec.ofNat (n+1) (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw y).length)) ∧
      (∀ e, LastEdge W.wclk e y → y < e + kq → ∀ i,
        (W.wgray_r.getD y 0).getLsbD i =
          (gray (BitVec.ofNat (n+1) (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw y).length)).getLsbD i ∨
        (W.wgray_r.getD y 0).getLsbD i =
          (gray (BitVec.ofNat (n+1) (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw e).length)).getLsbD i) := by
    intro y hy hyt
    have hf : WFilter P_w S_w R_w pw_w W.wclk W.winc W.wdata y :=
      ⟨hokw.mono (by lia), hiw.mono (by lia), hid.mono (by lia), hrw.mono (by lia), hpw.mono (by lia)⟩
    obtain ⟨h1, h2⟩ := hc.wg.2 y hy hf
    refine ⟨fun hs => ?_, fun e he hk i => ?_⟩
    · rw [h1 hs, hinv.wptrs y hyt]
    · have he1 := he.1
      have h2 := h2 e he hk i
      rw [hinv.wptrs y hyt, hinv.wptrs e (by lia)] at h2
      exact h2
  apply sample_choice (c := fun x => (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw x).length)
    (fun x y hxy => events_length_mono _ _ hxy) (a := t - lat - su - 1 - kq) (b := t - lat) (by lia)
  · exact events_window (fun u h => wEnq_rise lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw h) (hokw.mono (by lia))
      (by lia) (by lia)
  · intro i
    rcases mix_choice (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).orc.sel
        (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).wgNew
        (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).wgOld i with h | h
    · rw [h]
      obtain ⟨x, hx1, hx2, hx⟩ := sample_bit (lat := lat) (kq := kq) (u := t) hv (by simp [enqM]) (fun _ => by lia) (by lia) i
      exact ⟨x, by lia, by lia, hx⟩
    · rw [h]
      obtain ⟨x, hx1, hx2, hx⟩ := sample_bit (lat := lat) (kq := kq) (u := t - su - 1) hv (by simp [enqM]) (fun _ => by lia) (by lia) i
      exact ⟨x, by lia, by lia, hx⟩

/-- The last instant before `t` at which `Q` holds. -/
theorem exists_lastQ {Q : Nat → Prop} {t : Nat} (h : ∃ e, e < t ∧ Q e) :
    ∃ e, e < t ∧ Q e ∧ ∀ e', e < e' → e' < t → ¬ Q e' := by
  induction t with
  | zero => obtain ⟨e, he, _⟩ := h; exact absurd he (Nat.not_lt_zero e)
  | succ t ih =>
    by_cases hQ : Q t
    · exact ⟨t, Nat.lt_succ_self t, hQ,
        fun e' h1 h2 => absurd (Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h2)) (Nat.lt_irrefl _)⟩
    · obtain ⟨e, he, hQe⟩ := h
      have he' : e < t := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with h | h
        · exact h
        · subst h; exact absurd hQe hQ
      obtain ⟨e₀, h1, h2, h3⟩ := ih ⟨e, he', hQe⟩
      refine ⟨e₀, by lia, h2, fun e' h4 h5 => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h5) with h | h
      · exact h3 e' h4 h
      · subst h; exact hQ

/-- **The margin.**  Every write to the entry a dequeue at `t` reads happened at least a read
period plus the wire latency ago: the reader only ever dequeues a word the writer wrote well
before the read pointer's Gray code had even started crossing. -/
theorem write_margin (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W) {t : Nat}
    (hinv : Inv lat stl su P_r W t)
    (hkr : kq + su < P_r)
    (hd : ((rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise && (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).inc &&
          !(rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).empty) = true) :
    ∀ e, e < t → AsyncFifo.WriteAt lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
      (BitVec.ofNat n (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length) e →
      e < t - P_r - lat - 1 := by
  have hne : (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).empty = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hd; exact hd.2
  obtain ⟨j₁, j₂, _, _, _, _, hj₂, _, hlt⟩ := hinv.r.sync
  have hlt := hlt hne
  have hE := hinv.w.cap_d (events_length_mono _ _ (by unfold sampledAt; lia))
  have hDE : (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length <
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).length :=
    Nat.lt_of_lt_of_le hlt (Nat.le_trans hj₂ (events_length_mono _ _ (by lia)))
  intro e he hw
  obtain ⟨hre, hok, hptr⟩ := hw
  have henq : wEnq lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw e = true :=
    (wEnq_iff lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw e).mpr ⟨hre, hok⟩
  rw [hinv.wptrs e (by lia), setWidth_ofNat_succ] at hptr
  have hsucc : (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (e + 1)).length =
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw e).length + 1 := by
    unfold enqM; rw [events_succ_of_pos henq]; simp
  have hle : (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (e + 1)).length ≤
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).length := events_length_mono _ _ (by lia)
  have hidx := le_of_ofNat_eq_of_lt hptr (by lia)
  by_cases h : t - P_r - lat - 1 ≤ e
  · have := events_length_mono (wEnq lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw) (wval W.wdata) h
    unfold enqM at hj₂ hidx; lia
  · lia

/-- With no write to entry `a` in `[u, t)`, the machine's memory holds it: `wstep` only touches
the entry the write pointer names, and only at an accepted write. -/
theorem wmem_const {a : BitVec n} {u t : Nat} (hut : u ≤ t)
    (h : ∀ e, u ≤ e → e < t → ¬ AsyncFifo.WriteAt lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw a e) :
    (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).mem a =
      (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw u).mem a := by
  induction t with
  | zero => have hu : u = 0 := by omega
            rw [hu]
  | succ t ih =>
    rcases Nat.lt_or_ge u (t + 1) with hlt | hge
    · have hu : u ≤ t := by omega
      rw [← ih hu (fun e h1 h2 => h e h1 (by omega))]
      show (wstep stl (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t)
        (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t)).mem a = _
      have hnw := h t hu (Nat.lt_succ_self t)
      unfold wstep
      by_cases hr : (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true
      · rw [if_pos hr]
        simp only
        by_cases hok : ((winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).inc &&
            !(wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).full) = true
        · rw [if_pos hok, if_neg]
          intro hEq
          exact hnw ⟨hr, hok, hEq.symm⟩
        · rw [if_neg hok]
      · rw [if_neg hr]
    · have hu : u = t + 1 := by omega
      rw [hu]

/-- **The entry being read holds still over the read port's window.**  The margin is a whole
read period plus the wire latency, so a window of `rdly` instants is inside it with room to
spare; this is the one fact a read-domain output needs about the *write* domain's timing. -/
theorem mem_hold (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W) {t : Nat}
    (hinv : Inv lat stl su P_r W t)
    (hokw : ClockOK P_w W.wclk (t + 1)) (hiw : InOK S_w W.wclk W.winc (t + 1)) (hid : InOK S_w W.wclk W.wdata (t + 1))
    (hrw : ResetOK R_w W.wclk (t + 1)) (hpw : PulseOK pw_w W.wclk (t + 1)) (hkr : kq + su < P_r)
    (htm : t < W.mem_r.length) (hrd : kq + rdly ≤ P_r + lat + 1)
    (hd : ((rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise && (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).inc &&
          !(rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).empty) = true) :
    MemHold rdly W.mem_r ((rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).ptr.setWidth n) t := by
  rw [hinv.r.read_index]
  have hm := write_margin hc hinv hkr hd
  intro u hu1 hu2
  have hsu : MemSettled lat stl su kq W.wclk W.winc W.wdata W.rgray_w W.orcw
      (BitVec.ofNat n (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length) u :=
    fun e he hw => by have := hm e (by lia) hw; lia
  have hst : MemSettled lat stl su kq W.wclk W.winc W.wdata W.rgray_w W.orcw
      (BitVec.ofNat n (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length) t :=
    fun e he hw => by have := hm e he hw; lia
  rw [hc.mem.2 u (by lia) ⟨hokw.mono (by lia), hiw.mono (by lia), hid.mono (by lia),
        hrw.mono (by lia), hpw.mono (by lia)⟩ _ hsu,
      hc.mem.2 t htm ⟨hokw.mono (by lia), hiw.mono (by lia), hid.mono (by lia),
        hrw.mono (by lia), hpw.mono (by lia)⟩ _ hst]
  exact (wmem_const (u := u) (t := t) (by lia)
    (fun e h1 h2 hw => absurd (hm e (by lia) hw) (by lia))).symm

/-- A dequeue at instant `t` reads the memory entry it expects: the entry was written at
least a read period plus the wire latency ago, so it is outside every write window. -/
theorem mem_read (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W) {t : Nat}
    (hinv : Inv lat stl su P_r W t)
    (hokw : ClockOK P_w W.wclk (t + 1)) (hiw : InOK S_w W.wclk W.winc (t + 1)) (hid : InOK S_w W.wclk W.wdata (t + 1))
    (hrw : ResetOK R_w W.wclk (t + 1)) (hpw : PulseOK pw_w W.wclk (t + 1)) (hkr : kq + su < P_r) (htm : t < W.mem_r.length)
    (hd : ((rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise && (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).inc &&
          !(rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).empty) = true) :
    (W.mem_r.getD t (fun _ => default)) ((rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).ptr.setWidth n) =
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).getD
        (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length default := by
  have hne : (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).empty = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hd; exact hd.2
  obtain ⟨j₁, j₂, _, _, _, _, hj₂, _, hlt⟩ := hinv.r.sync
  have hlt := hlt hne
  have hE := hinv.w.cap_d (events_length_mono _ _ (by unfold sampledAt; lia))
  have hDE : (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length <
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).length :=
    Nat.lt_of_lt_of_le hlt (Nat.le_trans hj₂ (events_length_mono _ _ (by lia)))
  rw [hinv.r.read_index]
  have hset : MemSettled lat stl su kq W.wclk W.winc W.wdata W.rgray_w W.orcw
      (BitVec.ofNat n (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length) t := by
    intro e he hw
    obtain ⟨hre, hok, hptr⟩ := hw
    have henq : wEnq lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw e = true :=
      (wEnq_iff lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw e).mpr ⟨hre, hok⟩
    rw [hinv.wptrs e (by lia), setWidth_ofNat_succ] at hptr
    -- the enqueue at `e` is the one numbered `|D|` (or an older lap)
    have hsucc : (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (e + 1)).length =
        (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw e).length + 1 := by
      unfold enqM; rw [events_succ_of_pos henq]; simp
    have hle : (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (e + 1)).length ≤
        (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).length := events_length_mono _ _ (by lia)
    have hidx := le_of_ofNat_eq_of_lt hptr (by lia)
    -- so it happened before the instant the second stage sampled
    have hbefore : e < t - P_r - lat - 1 := by
      by_cases h : t - P_r - lat - 1 ≤ e
      · have := events_length_mono (wEnq lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw) (wval W.wdata) h
        unfold enqM at hj₂ hidx; lia
      · lia
    lia
  rw [hc.mem.2 t htm ⟨hokw.mono (by lia), hiw.mono (by lia), hid.mono (by lia), hrw.mono (by lia), hpw.mono (by lia)⟩ _ hset]
  exact hinv.w.mem _ (Nat.le_refl _) hDE

/-- The half step: from the invariant at `t`, the dequeues up to `t + 1` are still a prefix
of the enqueues up to `t + 1`. -/
theorem Inv.pre_succ (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W) {t : Nat}
    (hinv : Inv lat stl su P_r W t)
    (hokw : ClockOK P_w W.wclk (t + 1)) (hiw : InOK S_w W.wclk W.winc (t + 1)) (hid : InOK S_w W.wclk W.wdata (t + 1))
    (hrw : ResetOK R_w W.wclk (t + 1)) (hpw : PulseOK pw_w W.wclk (t + 1)) (hkr : kq + su < P_r) (htm : t < W.mem_r.length) :
    deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r (t + 1) <+:
      enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t + 1) := by
  rw [deqM_succ]
  refine List.IsPrefix.trans ?_ (events_prefix_succ _ _ _)
  have hep : (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
      (sampledAt lat (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since t)).length ≤
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).length :=
    events_length_mono _ _ (by unfold sampledAt; lia)
  exact hinv.r.step_prefix hep hinv.pre (fun hd => mem_read hc hinv hokw hiw hid hrw hpw hkr htm hd)

/-- The inductive step of the global invariant. -/
theorem Inv.succ (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
    (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W) {t : Nat} (hinv : Inv lat stl su P_r W t)
    (hokw : ClockOK P_w W.wclk (t + 1)) (hokr : ClockOK P_r W.rclk (t + 1))
    (hiw : InOK S_w W.wclk W.winc (t + 1)) (hid : InOK S_w W.wclk W.wdata (t + 1)) (hir : InOK S_r W.rclk W.rinc (t + 1))
    (hrw : ResetOK R_w W.wclk (t + 1)) (hpw : PulseOK pw_w W.wclk (t + 1)) (hrr : ResetOK R_r W.rclk (t + 1)) (hpr : PulseOK pw_r W.rclk (t + 1))
    (htw : t < wLen lat W.wclk W.winc W.wdata W.rgray_w W.orcw) (htr : t < rLen lat W.rclk W.rinc W.wgray_r W.orcr)
    (htm : t < W.mem_r.length) :
    Inv lat stl su P_r W (t + 1) := by
  have hwl := wLen_le lat W.wclk W.winc W.wdata W.rgray_w W.orcw
  have hrl := rLen_le lat W.rclk W.rinc W.wgray_r W.orcr
  -- the sampled values at an edge
  obtain ⟨k₀, hk₀, hk₀l, hk₀u⟩ : ∃ k₀,
      ((winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true →
        mix (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).orc.sel
          (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rgNew
          (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rgOld = gray (BitVec.ofNat (n+1) k₀)) ∧
      ((winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true →
        (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r (t - lat - su - 1 - kq)).length ≤ k₀) ∧
      ((winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true →
        k₀ ≤ (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r (t - lat)).length) := by
    by_cases hr : (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true
    · obtain ⟨k₀, h1, h2, h3⟩ := rgray_sample hc hinv hokr hir hrr hpr hkr htw
      exact ⟨k₀, fun _ => h1, fun _ => h2, fun _ => h3⟩
    · exact ⟨0, fun h => absurd h hr, fun h => absurd h hr, fun h => absurd h hr⟩
  obtain ⟨k₀', hk₀', hk₀l', hk₀u'⟩ : ∃ k₀',
      ((rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
        mix (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).orc.sel
          (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).wgNew
          (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).wgOld = gray (BitVec.ofNat (n+1) k₀')) ∧
      ((rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
        (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t - lat - su - 1 - kq)).length ≤ k₀') ∧
      ((rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
        k₀' ≤ (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t - lat)).length) := by
    by_cases hr : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true
    · obtain ⟨k₀, h1, h2, h3⟩ := wgray_sample hc hinv hokw hiw hid hrw hpw hkw htr
      exact ⟨k₀, fun _ => h1, fun _ => h2, fun _ => h3⟩
    · exact ⟨0, fun h => absurd h hr, fun h => absurd h hr, fun h => absurd h hr⟩
  -- settledness and the sampling windows at an edge
  have hsetw : (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true →
      stl ≤ (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).since :=
    fun hr => hinv.wsince.settled hr hstlw hokw
  have hsetr : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
      stl ≤ (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since :=
    fun hr => hinv.rsince.settled hr hstlr hokr
  have hsuw : (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true →
      t - 1 - (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).since - lat ≤ t - lat - su - 1 - kq :=
    fun hr => hinv.wsince.sampled_le_window hr hkw hokw
  have hsur : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
      t - 1 - (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since - lat ≤ t - lat - su - 1 - kq :=
    fun hr => hinv.rsince.sampled_le_window hr hkr hokr
  have hsur2 : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
      t - 1 - (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since - lat ≤ t + 1 - P_r - lat - 1 :=
    fun hr => hinv.rsince.sampled_le_period hr hokr
  -- the new lower bounds `dp'`, `ep'`
  have hdp : (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r
      (sampledAt lat (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).since t)).length ≤
      (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r
        (sampledAt lat (wstep stl (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t)
          (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t)).since (t + 1))).length := by
    apply events_length_mono
    unfold sampledAt
    by_cases hr : (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true
    · rw [wstep_rise hr]; simp only; lia
    · rw [wstep_norise (by simpa using hr)]; simp only; lia
  have hep : (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
      (sampledAt lat (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since t)).length ≤
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
        (sampledAt lat (rstep stl (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t)
          (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t)).since (t + 1))).length := by
    apply events_length_mono
    unfold sampledAt
    by_cases hr : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true
    · rw [rstep_rise hr]; simp only; lia
    · rw [rstep_norise (by simpa using hr)]; simp only; lia
  have hdp'd : (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r
      (sampledAt lat (wstep stl (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t)
        (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t)).since (t + 1))).length ≤
      (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r (t + 1)).length :=
    events_length_mono _ _ (by unfold sampledAt; lia)
  have hep'E : (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
      (sampledAt lat (rstep stl (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t)
        (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t)).since (t + 1))).length ≤
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).length :=
    events_length_mono _ _ (by unfold sampledAt; lia)
  -- the sampled counts at an edge
  have hk₀l_w : (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true →
      (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r
        (sampledAt lat (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t).since t)).length ≤ k₀ :=
    fun hr => Nat.le_trans (events_length_mono _ _ (hsuw hr)) (hk₀l hr)
  have hk₀u_w : (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true →
      k₀ ≤ (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r
        (sampledAt lat (wstep stl (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t)
          (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t)).since (t + 1))).length := by
    intro hr
    rw [wstep_rise hr]; simp only [sampledAt]
    have : t + 1 - 1 - 0 - lat = t - lat := by lia
    rw [this]; exact hk₀u hr
  have hk₀l_r : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
        (sampledAt lat (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since t)).length ≤ k₀' :=
    fun hr => Nat.le_trans (events_length_mono _ _ (hsur hr)) (hk₀l' hr)
  have hk₀u_r : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
      k₀' ≤ (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
        (sampledAt lat (rstep stl (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t)
          (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t)).since (t + 1))).length := by
    intro hr
    rw [rstep_rise hr]; simp only [sampledAt]
    have : t + 1 - 1 - 0 - lat = t - lat := by lia
    rw [this]; exact hk₀u' hr
  -- the second-stage bound
  have hep2 : (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t - P_r - lat - 1)).length ≤
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t + 1 - P_r - lat - 1)).length :=
    events_length_mono _ _ (by lia)
  have hep2' : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true →
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
        (sampledAt lat (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).since t)).length ≤
      (enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw (t + 1 - P_r - lat - 1)).length :=
    fun hr => events_length_mono _ _ (hsur2 hr)
  have hd1 : (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r t).length ≤
      (deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r (t + 1)).length := events_length_mono _ _ (Nat.le_succ t)
  have hw := hinv.w.step stl hdp (events_length_mono _ _ (by unfold sampledAt; lia)) hinv.pre.length_le
    hsetw hk₀ hk₀l_w hk₀u_w
  have hcap := hinv.w.cap_d (by unfold sampledAt at *; exact events_length_mono _ _ (by lia))
  have hr := hinv.r.step stl (memv := W.mem_r.getD t (fun _ => default)) hep hep'E hinv.pre hep2 hep2' hcap hsetr
    hk₀' hk₀l_r hk₀u_r
  have hpre := hinv.pre_succ hc hokw hiw hid hrw hpw hkr htm
  refine ⟨?_, ?_, hpre, ?_, ?_, ?_, ?_⟩
  · rw [enqM_succ]; exact hw.mono_d hd1
  · rw [deqM_succ]; exact hr
  · intro t' ht'
    rcases Nat.lt_or_eq_of_le ht' with h | h
    · exact hinv.wptrs t' (by lia)
    · subst h; rw [enqM_succ]; exact hw.ptr
  · intro t' ht'
    rcases Nat.lt_or_eq_of_le ht' with h | h
    · exact hinv.rptrs t' (by lia)
    · subst h; rw [deqM_succ]; exact hr.ptr
  · show SinceInv stl W.wclk (t + 1) (wstep stl (wRun lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw t)
      (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t)).since
    by_cases hr : (winp lat su W.wclk W.winc W.wdata W.rgray_w W.orcw t).rise = true
    · rw [wstep_rise hr]; exact SinceInv.step_rise hr
    · have hr' : riseAt W.wclk t = false := by unfold winp at hr; simpa using hr
      rw [wstep_norise hr']; exact hinv.wsince.step_norise hr'
  · show SinceInv stl W.rclk (t + 1) (rstep stl (rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t)
      (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t)).since
    by_cases hr : (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise = true
    · rw [rstep_rise hr]; exact SinceInv.step_rise hr
    · have hr' : riseAt W.rclk t = false := by unfold rinp at hr; simpa using hr
      rw [rstep_norise hr']; exact hinv.rsince.step_norise hr'

theorem Inv.all (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
    (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W) :
    ∀ t, t ≤ wLen lat W.wclk W.winc W.wdata W.rgray_w W.orcw → t ≤ rLen lat W.rclk W.rinc W.wgray_r W.orcr →
      t ≤ W.mem_r.length →
      ClockOK P_w W.wclk t → ClockOK P_r W.rclk t →
      InOK S_w W.wclk W.winc t → InOK S_w W.wclk W.wdata t → InOK S_r W.rclk W.rinc t →
      ResetOK R_w W.wclk t → ResetOK R_r W.rclk t →
      PulseOK pw_w W.wclk t → PulseOK pw_r W.rclk t →
      Inv lat stl su P_r W t := by
  intro t
  induction t with
  | zero => intros; exact Inv.zero _ _ _ _ _
  | succ t ih =>
    intro h1 h2 h3 hokw hokr hiw hid hir hrw hrr hpw hpr
    exact (ih (by lia) (by lia) (by lia) (hokw.mono (Nat.le_succ t)) (hokr.mono (Nat.le_succ t))
      (hiw.mono (Nat.le_succ t)) (hid.mono (Nat.le_succ t)) (hir.mono (Nat.le_succ t))
      (hrw.mono (Nat.le_succ t)) (hrr.mono (Nat.le_succ t)) (hpw.mono (Nat.le_succ t))
      (hpr.mono (Nat.le_succ t))).succ
      hkw hkr hstlw hstlr hc hokw hokr hiw hid hir hrw hpw hrr hpr (by lia) (by lia) (by lia)

/-- **Temporal correctness of the asynchronous FIFO, against relaxed wires.**  If the
cross-domain wires and the three outputs satisfy the relaxed relations of the domains driving
them, and each clock period is longer than the synchroniser settling time and than a clk-to-q
window followed by a sampling window, then the FIFO specification holds. -/
theorem fifo_correctF (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
    (hkrd : kq + rdly < P_r) (hrd : kq + rdly ≤ P_r + lat + 1) (hrdR : rdly ≤ R_r)
    (hc : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W)
    {full_q empty_q : List Bool} {rdata_q : List α}
    (hf : WFullF lat stl su kq P_w S_w R_w pw_w W.wclk W.winc W.wdata W.rgray_w W.orcw full_q)
    (he : REmptyF lat stl su kq P_r S_r R_r pw_r W.rclk W.rinc W.wgray_r W.orcr empty_q)
    (hd : RDataF lat stl su kq rdly P_r S_r R_r pw_r W.rclk W.rinc W.wgray_r W.orcr W.mem_r rdata_q) :
    FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r
      ⟨W.wclk, W.winc, W.wdata, W.rclk, W.rinc, full_q, empty_q, rdata_q⟩ := by
  intro T hT hokw hokr hiw hid hir hrw hrr hpw hpr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hT
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 hokw hokr hiw hid hir hrw hrr hpw hpr
  have hwl := wLen_le lat W.wclk W.winc W.wdata W.rgray_w W.orcw
  have hrl := rLen_le lat W.rclk W.rinc W.wgray_r W.orcr
  have hfl := hf.1
  have hel := he.1
  have hdl := hd.1
  have hdl' : T ≤ rLen lat W.rclk W.rinc W.wgray_r W.orcr + 1 ∧ T ≤ W.mem_r.length := by
    unfold rDataLen at hdl; omega
  have hkqw : kq < P_w := by lia
  have hkqr : kq < P_r := by lia
  have eE : FifoIO.enqs ⟨W.wclk, W.winc, W.wdata, W.rclk, W.rinc, full_q, empty_q, rdata_q⟩ T =
      enqM lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw T := by
    unfold FifoIO.enqs enqs enqM
    apply events_congr'
    intro t ht
    refine ⟨?_, fun _ => rfl⟩
    unfold enqAt wEnq winp
    simp only
    by_cases hr : riseAt W.wclk t = true
    · rw [hf.2 t (by lia) ⟨hokw.mono (by lia), hiw.mono (by lia), hid.mono (by lia), hrw.mono (by lia), hpw.mono (by lia)⟩
        (settled_at_edge (hokw.mono (by lia)) hkqw hr)]
    · simp only [Bool.not_eq_true] at hr; simp [hr]
  have eD : FifoIO.deqs ⟨W.wclk, W.winc, W.wdata, W.rclk, W.rinc, full_q, empty_q, rdata_q⟩ T =
      deqM lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r T := by
    unfold FifoIO.deqs deqs deqM
    apply events_congr'
    intro t ht
    have hf' : RFilter P_r S_r R_r pw_r W.rclk W.rinc t := ⟨hokr.mono (by lia), hir.mono (by lia), hrr.mono (by lia), hpr.mono (by lia)⟩
    by_cases hr : riseAt W.rclk t = true
    · have hs := settled_at_edge (hokr.mono (by lia)) hkqr hr
      have hs2 : Settled (kq + rdly) W.rclk t :=
        settled_at_edge (hokr.mono (by lia)) (by lia) hr
      refine ⟨?_, fun hdq => ?_⟩
      · unfold deqAt rDeq rinp
        simp only
        rw [he.2 t (by lia) hf' hs]
      · have hdeq : ((rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).rise &&
            (rinp lat su W.rclk W.rinc W.wgray_r W.orcr t).inc &&
            !(rRun lat stl su W.rclk W.rinc W.wgray_r W.orcr t).empty) = true := by
          unfold rinp
          simp only
          rw [← he.2 t (by lia) hf' hs]
          unfold deqAt at hdq
          exact hdq
        have hinv := Inv.all hkw hkr hstlw hstlr hc t (by lia) (by lia) (by lia)
          (hokw.mono (by lia)) (hokr.mono (by lia)) (hiw.mono (by lia)) (hid.mono (by lia))
          (hir.mono (by lia)) (hrw.mono (by lia)) (hrr.mono (by lia)) (hpw.mono (by lia))
          (hpr.mono (by lia))
        have hrt : R_r ≤ t := hrr t (by lia) hr
        exact hd.2 t (by lia) (by lia) hf' hs2 (mem_hold hc hinv (hokw.mono (by lia)) (hiw.mono (by lia))
          (hid.mono (by lia)) (hrw.mono (by lia)) (hpw.mono (by lia)) hkr (by lia) hrd hdeq)
    · simp only [Bool.not_eq_true] at hr
      refine ⟨?_, fun h => ?_⟩
      · unfold deqAt rDeq rinp; simp [hr]
      · unfold deqAt at h; simp [hr] at h
  rw [eE, eD]
  cases T with
  | zero => simp [enqM, deqM]
  | succ t =>
    have hinv := Inv.all hkw hkr hstlw hstlr hc t (by lia) (by lia) (by lia)
      (hokw.mono (Nat.le_succ t)) (hokr.mono (Nat.le_succ t))
      (hiw.mono (Nat.le_succ t)) (hid.mono (Nat.le_succ t)) (hir.mono (Nat.le_succ t))
      (hrw.mono (Nat.le_succ t)) (hrr.mono (Nat.le_succ t))
      (hpw.mono (Nat.le_succ t)) (hpr.mono (Nat.le_succ t))
    exact hinv.pre_succ hc hokw hiw hid hrw hpw hkr (by lia)

/-! ### The exact wires as a special case -/

variable (lat stl su W) in
/-- The wires of the composed circuit carry the exact outputs of the modules driving them. -/
structure Consistent : Prop where
  wg : W.wgray_r <+: wGray lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
  mem : W.mem_r <+: wMem lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw
  rg : W.rgray_w <+: rGray lat stl su W.rclk W.rinc W.wgray_r W.orcr

theorem Consistent.toF (hc : Consistent lat stl su W) : ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq W :=
  ⟨WGrayF.of_exact hc.wg, WMemF.of_exact hc.mem, RGrayF.of_exact hc.rg⟩

/-- **Temporal correctness of the asynchronous FIFO** with exact wires: the special case
`kq = 0`. -/
theorem fifo_correct (hstlw : stl < P_w) (hstlr : stl < P_r) (hsw : su < P_w) (hsr : su < P_r)
    (hc : Consistent lat stl su W) :
    FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r ⟨W.wclk, W.winc, W.wdata, W.rclk, W.rinc,
      wFull lat stl su W.wclk W.winc W.wdata W.rgray_w W.orcw,
      rEmpty lat stl su W.rclk W.rinc W.wgray_r W.orcr,
      rData lat stl su W.rclk W.rinc W.wgray_r W.orcr W.mem_r⟩ :=
  fifo_correctF (kq := 0) (rdly := 0) (by lia) (by lia) hstlw hstlr (by lia) (by lia) (by lia) hc.toF
    (WFullF.of_exact List.prefix_rfl) (REmptyF.of_exact List.prefix_rfl) (RDataF.of_exact List.prefix_rfl)

end Invariant

end Graphiti.AsyncFifo
