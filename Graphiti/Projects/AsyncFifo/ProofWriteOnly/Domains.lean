/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.DomainsLemmas

/-!
# The two clock domains: the lemmas

Length and indexing facts about the two machines, their congruence lemmas, and the
machine-level invariants (`WInv`, `RInv`).  The machines themselves, which the statement
of the main theorem names, are in `components/level2/Domains.lean`.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

open Gray


theorem mix_choice {w : Nat} (sel a b : BitVec w) (i : Nat) :
    (mix sel a b).getLsbD i = a.getLsbD i ∨ (mix sel a b).getLsbD i = b.getLsbD i := by
  simp only [mix, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases hi : i < w
  · cases hs : sel.getLsbD i <;> simp [hi]
  · have := BitVec.getLsbD_of_ge a i (by lia)
    have := BitVec.getLsbD_of_ge b i (by lia)
    simp_all

/-- A per-bit mixture of the Gray codes of two consecutive counts (`kp ≤ k ≤ kp + 1`) is the
Gray code of one of them: what a metastable sampler sees is an old or a new count, never
garbage.  This is where the Gray code does its work. -/
theorem gray_choice_counter {n : Nat} {j : BitVec (n+1)} {kp k : Nat}
    (h : ∀ i, j.getLsbD i = (gray (BitVec.ofNat (n+1) k)).getLsbD i ∨
              j.getLsbD i = (gray (BitVec.ofNat (n+1) kp)).getLsbD i)
    (hle : kp ≤ k) (hle' : k ≤ kp + 1) :
    ∃ k₀, j = gray (BitVec.ofNat (n+1) k₀) ∧ kp ≤ k₀ ∧ k₀ ≤ k := by
  rcases Nat.lt_or_ge kp k with hlt | hge
  · have hk : k = kp + 1 := by lia
    subst hk
    have hb' : ∀ i, j.getLsbD i = (gray (BitVec.ofNat (n+1) kp)).getLsbD i ∨
        j.getLsbD i = (gray (BitVec.ofNat (n+1) kp + 1#(n+1))).getLsbD i := by
      intro i; rcases h i with h | h
      · right; rw [← ofNat_succ]; exact h
      · left; exact h
    rcases gray_succ_choice _ _ hb' with h | h
    · exact ⟨kp, h, Nat.le_refl _, by lia⟩
    · exact ⟨kp + 1, by rw [ofNat_succ]; exact h, by lia, Nat.le_refl _⟩
  · have hk : k = kp := by lia
    subst hk
    have hb' : ∀ i, j.getLsbD i = (gray (BitVec.ofNat (n+1) k)).getLsbD i ∨
        j.getLsbD i = (gray (BitVec.ofNat (n+1) k)).getLsbD i := by
      intro i; rcases h i with h | h <;> exact Or.inl h
    exact ⟨k, eq_of_getLsbD_choice_same _ _ hb', Nat.le_refl _, Nat.le_refl _⟩


theorem delayed_congr {w : Nat} {lat : Nat} {s s' : List (BitVec w)} (h : s <+: s') {t : Nat}
    (ht : t < s.length + lat) : delayed lat s t = delayed lat s' t := by
  unfold delayed
  split
  · rfl
  · rw [h.getD_eq_left (by lia)]

section Machines

variable {α : Type} [Inhabited α] {n : Nat}


/-! ### Basic length / indexing facts -/

variable (lat stl su : Nat) (wclk winc : List Bool) (wdata : List α) (rgray : List (BitVec (n+1)))
  (orcw : List (Orc n)) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orcr : List (Orc n))
  (mem : List (BitVec n → α))

theorem wLen_le :
    wLen lat wclk winc wdata rgray orcw ≤ wclk.length ∧ wLen lat wclk winc wdata rgray orcw ≤ winc.length ∧
    wLen lat wclk winc wdata rgray orcw ≤ wdata.length ∧ wLen lat wclk winc wdata rgray orcw ≤ rgray.length + lat ∧
    wLen lat wclk winc wdata rgray orcw ≤ orcw.length := by
  unfold wLen; omega

theorem rLen_le :
    rLen lat rclk rinc wgray orcr ≤ rclk.length ∧ rLen lat rclk rinc wgray orcr ≤ rinc.length ∧
    rLen lat rclk rinc wgray orcr ≤ wgray.length + lat ∧ rLen lat rclk rinc wgray orcr ≤ orcr.length := by
  unfold rLen; omega

@[simp] theorem wGray_length : (wGray lat stl su wclk winc wdata rgray orcw).length = wLen lat wclk winc wdata rgray orcw + 1 := by
  simp [wGray]
@[simp] theorem wFull_length : (wFull lat stl su wclk winc wdata rgray orcw).length = wLen lat wclk winc wdata rgray orcw + 1 := by
  simp [wFull]
@[simp] theorem wMem_length : (wMem lat stl su wclk winc wdata rgray orcw).length = wLen lat wclk winc wdata rgray orcw + 1 := by
  simp [wMem]
@[simp] theorem rGray_length : (rGray lat stl su rclk rinc wgray orcr).length = rLen lat rclk rinc wgray orcr + 1 := by
  simp [rGray]
@[simp] theorem rEmpty_length : (rEmpty lat stl su rclk rinc wgray orcr).length = rLen lat rclk rinc wgray orcr + 1 := by
  simp [rEmpty]
@[simp] theorem rData_length : (rData lat stl su rclk rinc wgray orcr mem).length = rDataLen lat rclk rinc wgray orcr mem := by
  simp [rData]

theorem wGray_getD {t : Nat} (ht : t ≤ wLen lat wclk winc wdata rgray orcw) (d : BitVec (n+1)) :
    (wGray lat stl su wclk winc wdata rgray orcw).getD t d = gray (wRun lat stl su wclk winc wdata rgray orcw t).ptr :=
  moore_getD _ _ _ _ ht d
theorem wFull_getD {t : Nat} (ht : t ≤ wLen lat wclk winc wdata rgray orcw) (d : Bool) :
    (wFull lat stl su wclk winc wdata rgray orcw).getD t d = (wRun lat stl su wclk winc wdata rgray orcw t).full :=
  moore_getD _ _ _ _ ht d
theorem wMem_getD {t : Nat} (ht : t ≤ wLen lat wclk winc wdata rgray orcw) (d : BitVec n → α) :
    (wMem lat stl su wclk winc wdata rgray orcw).getD t d = (wRun lat stl su wclk winc wdata rgray orcw t).mem :=
  moore_getD _ _ _ _ ht d
theorem rGray_getD {t : Nat} (ht : t ≤ rLen lat rclk rinc wgray orcr) (d : BitVec (n+1)) :
    (rGray lat stl su rclk rinc wgray orcr).getD t d = gray (rRun lat stl su rclk rinc wgray orcr t).ptr :=
  moore_getD _ _ _ _ ht d
theorem rEmpty_getD {t : Nat} (ht : t ≤ rLen lat rclk rinc wgray orcr) (d : Bool) :
    (rEmpty lat stl su rclk rinc wgray orcr).getD t d = (rRun lat stl su rclk rinc wgray orcr t).empty :=
  moore_getD _ _ _ _ ht d
theorem rData_getD {t : Nat} (ht : t < rDataLen lat rclk rinc wgray orcr mem) (d : α) :
    (rData lat stl su rclk rinc wgray orcr mem).getD t d = rval lat stl su rclk rinc wgray orcr mem t :=
  timeline_getD _ ht d

/-! ### Monotonicity: more input information gives more output information -/

theorem winp_congr {wclk' winc' : List Bool} {wdata' : List α} {rgray' : List (BitVec (n+1))} {orcw' : List (Orc n)}
    (h₁ : wclk <+: wclk') (h₂ : winc <+: winc') (h₃ : wdata <+: wdata') (h₄ : rgray <+: rgray')
    (h₅ : orcw <+: orcw') :
    ∀ t, t < wLen lat wclk winc wdata rgray orcw →
      winp lat su wclk winc wdata rgray orcw t = winp lat su wclk' winc' wdata' rgray' orcw' t := by
  intro t ht
  have := wLen_le lat wclk winc wdata rgray orcw
  unfold winp
  rw [riseAt_prefix h₁ (by lia), h₂.getD_eq_left (by lia), h₃.getD_eq_left (by lia),
    delayed_congr h₄ (by lia), delayed_congr h₄ (by lia), h₅.getD_eq_left (by lia)]

theorem wLen_mono {wclk' winc' : List Bool} {wdata' : List α} {rgray' : List (BitVec (n+1))} {orcw' : List (Orc n)}
    (h₁ : wclk <+: wclk') (h₂ : winc <+: winc') (h₃ : wdata <+: wdata') (h₄ : rgray <+: rgray')
    (h₅ : orcw <+: orcw') :
    wLen lat wclk winc wdata rgray orcw ≤ wLen lat wclk' winc' wdata' rgray' orcw' := by
  have := h₁.length_le; have := h₂.length_le; have := h₃.length_le; have := h₄.length_le; have := h₅.length_le
  unfold wLen; omega

theorem wRun_congr {wclk' winc' : List Bool} {wdata' : List α} {rgray' : List (BitVec (n+1))} {orcw' : List (Orc n)}
    (h₁ : wclk <+: wclk') (h₂ : winc <+: winc') (h₃ : wdata <+: wdata') (h₄ : rgray <+: rgray')
    (h₅ : orcw <+: orcw') {t : Nat} (ht : t ≤ wLen lat wclk winc wdata rgray orcw) :
    wRun lat stl su wclk winc wdata rgray orcw t = wRun lat stl su wclk' winc' wdata' rgray' orcw' t :=
  run_congr _ _ (winp_congr lat su wclk winc wdata rgray orcw h₁ h₂ h₃ h₄ h₅) t ht

theorem wGray_mono {wclk' winc' : List Bool} {wdata' : List α} {rgray' : List (BitVec (n+1))} {orcw' : List (Orc n)}
    (h₁ : wclk <+: wclk') (h₂ : winc <+: winc') (h₃ : wdata <+: wdata') (h₄ : rgray <+: rgray')
    (h₅ : orcw <+: orcw') :
    wGray lat stl su wclk winc wdata rgray orcw <+: wGray lat stl su wclk' winc' wdata' rgray' orcw' :=
  moore_mono _ _ _ (wLen_mono lat wclk winc wdata rgray orcw h₁ h₂ h₃ h₄ h₅)
    (winp_congr lat su wclk winc wdata rgray orcw h₁ h₂ h₃ h₄ h₅)
theorem wFull_mono {wclk' winc' : List Bool} {wdata' : List α} {rgray' : List (BitVec (n+1))} {orcw' : List (Orc n)}
    (h₁ : wclk <+: wclk') (h₂ : winc <+: winc') (h₃ : wdata <+: wdata') (h₄ : rgray <+: rgray')
    (h₅ : orcw <+: orcw') :
    wFull lat stl su wclk winc wdata rgray orcw <+: wFull lat stl su wclk' winc' wdata' rgray' orcw' :=
  moore_mono _ _ _ (wLen_mono lat wclk winc wdata rgray orcw h₁ h₂ h₃ h₄ h₅)
    (winp_congr lat su wclk winc wdata rgray orcw h₁ h₂ h₃ h₄ h₅)
theorem wMem_mono {wclk' winc' : List Bool} {wdata' : List α} {rgray' : List (BitVec (n+1))} {orcw' : List (Orc n)}
    (h₁ : wclk <+: wclk') (h₂ : winc <+: winc') (h₃ : wdata <+: wdata') (h₄ : rgray <+: rgray')
    (h₅ : orcw <+: orcw') :
    wMem lat stl su wclk winc wdata rgray orcw <+: wMem lat stl su wclk' winc' wdata' rgray' orcw' :=
  moore_mono _ _ _ (wLen_mono lat wclk winc wdata rgray orcw h₁ h₂ h₃ h₄ h₅)
    (winp_congr lat su wclk winc wdata rgray orcw h₁ h₂ h₃ h₄ h₅)

theorem rinp_congr {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orcr' : List (Orc n)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orcr <+: orcr') :
    ∀ t, t < rLen lat rclk rinc wgray orcr → rinp lat su rclk rinc wgray orcr t = rinp lat su rclk' rinc' wgray' orcr' t := by
  intro t ht
  have := rLen_le lat rclk rinc wgray orcr
  unfold rinp
  rw [riseAt_prefix h₁ (by lia), h₂.getD_eq_left (by lia), delayed_congr h₃ (by lia),
    delayed_congr h₃ (by lia), h₄.getD_eq_left (by lia)]

theorem rLen_mono {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orcr' : List (Orc n)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orcr <+: orcr') :
    rLen lat rclk rinc wgray orcr ≤ rLen lat rclk' rinc' wgray' orcr' := by
  have := h₁.length_le; have := h₂.length_le; have := h₃.length_le; have := h₄.length_le
  unfold rLen; omega

theorem rRun_congr {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orcr' : List (Orc n)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orcr <+: orcr')
    {t : Nat} (ht : t ≤ rLen lat rclk rinc wgray orcr) :
    rRun lat stl su rclk rinc wgray orcr t = rRun lat stl su rclk' rinc' wgray' orcr' t :=
  run_congr _ _ (rinp_congr lat su rclk rinc wgray orcr h₁ h₂ h₃ h₄) t ht

theorem rGray_mono {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orcr' : List (Orc n)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orcr <+: orcr') :
    rGray lat stl su rclk rinc wgray orcr <+: rGray lat stl su rclk' rinc' wgray' orcr' :=
  moore_mono _ _ _ (rLen_mono lat rclk rinc wgray orcr h₁ h₂ h₃ h₄) (rinp_congr lat su rclk rinc wgray orcr h₁ h₂ h₃ h₄)
theorem rEmpty_mono {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orcr' : List (Orc n)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orcr <+: orcr') :
    rEmpty lat stl su rclk rinc wgray orcr <+: rEmpty lat stl su rclk' rinc' wgray' orcr' :=
  moore_mono _ _ _ (rLen_mono lat rclk rinc wgray orcr h₁ h₂ h₃ h₄) (rinp_congr lat su rclk rinc wgray orcr h₁ h₂ h₃ h₄)

theorem rData_mono {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orcr' : List (Orc n)}
    {mem' : List (BitVec n → α)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orcr <+: orcr')
    (h₅ : mem <+: mem') :
    rData lat stl su rclk rinc wgray orcr mem <+: rData lat stl su rclk' rinc' wgray' orcr' mem' := by
  have hL := rLen_mono lat rclk rinc wgray orcr h₁ h₂ h₃ h₄
  have := h₅.length_le
  apply timeline_mono
  · unfold rDataLen; omega
  · intro t ht
    unfold rDataLen at ht
    unfold rval
    rw [h₅.getD_eq_left (by omega), rRun_congr lat stl su rclk rinc wgray orcr h₁ h₂ h₃ h₄ (by omega)]

end Machines


/-! ## Machine-level invariants

We now fix the streams stored in the composed circuit: the five inputs of the write
domain (`wclk winc wdata rgray_w orcw`) and the five of the read domain
(`rclk rinc wgray_r orcr mem_r`), and prove what one instant of each machine preserves
(`WInv.step`, `RInv.step`).  The global invariant and the FIFO theorem are in
`Invariant.lean`, stated against the relaxed wire relations of `Filtered.lean`.
-/

section Invariant

variable {α : Type} [Inhabited α] {n : Nat}
variable (lat stl su : Nat)
variable (wclk winc : List Bool) (wdata : List α) (rgray_w : List (BitVec (n+1))) (orcw : List (Orc n))
variable (rclk rinc : List Bool) (wgray_r : List (BitVec (n+1))) (orcr : List (Orc n)) (mem_r : List (BitVec n → α))

/-- Enqueue at instant `t`, as decided by the write machine. -/
def wEnq (t : Nat) : Bool :=
  (winp lat su wclk winc wdata rgray_w orcw t).rise && (winp lat su wclk winc wdata rgray_w orcw t).inc &&
    !(wRun lat stl su wclk winc wdata rgray_w orcw t).full

def wval (t : Nat) : α := wdata.getD t default

/-- Values enqueued before instant `T` (machine view). -/
def enqM (T : Nat) : List α := events (wEnq lat stl su wclk winc wdata rgray_w orcw) (wval wdata) T

/-- Dequeue at instant `t`, as decided by the read machine. -/
def rDeq (t : Nat) : Bool :=
  (rinp lat su rclk rinc wgray_r orcr t).rise && (rinp lat su rclk rinc wgray_r orcr t).inc &&
    !(rRun lat stl su rclk rinc wgray_r orcr t).empty

/-- Values dequeued before instant `T` (machine view). -/
def deqM (T : Nat) : List α :=
  events (rDeq lat stl su rclk rinc wgray_r orcr) (rval lat stl su rclk rinc wgray_r orcr mem_r) T


/-- The `since` register counts the instants since the last rising edge (starting at `stl`
before any edge, so that the first stage counts as settled initially). -/
def SinceInv (stl : Nat) (c : List Bool) (t since : Nat) : Prop :=
  (NoEdge c t ∧ since = stl + t) ∨ (∃ e, LastEdge c e t ∧ since + e + 1 = t)

theorem SinceInv.zero (stl : Nat) (c : List Bool) : SinceInv stl c 0 stl :=
  Or.inl ⟨fun e he => absurd he (Nat.not_lt_zero e), rfl⟩

theorem SinceInv.step_rise {stl : Nat} {c : List Bool} {t : Nat} (hr : riseAt c t = true) :
    SinceInv stl c (t + 1) 0 :=
  Or.inr ⟨t, ⟨Nat.lt_succ_self t, hr, fun e' h1 h2 => absurd (Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h2)) (Nat.lt_irrefl _)⟩, by lia⟩

theorem SinceInv.step_norise {stl : Nat} {c : List Bool} {t s : Nat} (h : SinceInv stl c t s)
    (hr : riseAt c t = false) : SinceInv stl c (t + 1) (s + 1) := by
  rcases h with ⟨hne, hs⟩ | ⟨e, ⟨he, hre, hlast⟩, hs⟩
  · left
    refine ⟨fun e he => ?_, by lia⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with h | h
    · exact hne e h
    · subst h; exact hr
  · right
    refine ⟨e, ⟨by lia, hre, fun e' h1 h2 => ?_⟩, by lia⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with h | h
    · exact hlast e' h1 h
    · subst h; exact hr

/-- At a rising edge, under the clock-period assumption, the first stage has settled. -/
theorem SinceInv.settled {stl P : Nat} {c : List Bool} {t s : Nat} (h : SinceInv stl c t s)
    (hr : riseAt c t = true) (hP : stl < P) (hok : ClockOK P c (t + 1)) : stl ≤ s := by
  rcases h with ⟨_, hs⟩ | ⟨e, ⟨he, hre, _⟩, hs⟩
  · lia
  · have := hok e t he (by lia) hre hr
    lia

/-- Events at rising edges of a clock whose edges are at least `P` apart: an interval of at
most `P` instants sees at most one of them. -/
theorem events_window {β : Type} {ev : Nat → Bool} {vals : Nat → β} {c : List Bool} {P a b : Nat}
    (hev : ∀ u, ev u = true → riseAt c u = true) (hok : ClockOK P c b) (hab : a ≤ b) (hw : b ≤ a + P) :
    (events ev vals b).length ≤ (events ev vals a).length + 1 := by
  -- strengthened statement: also, if nothing fired in `[a, a + d)`, the lengths are equal
  have key : ∀ d, a + d ≤ b → (events ev vals (a + d)).length ≤ (events ev vals a).length + 1 ∧
      ((∀ u, a ≤ u → u < a + d → ev u = false) → (events ev vals (a + d)).length = (events ev vals a).length) := by
    intro d
    induction d with
    | zero => intro _; exact ⟨by lia, fun _ => rfl⟩
    | succ d ih =>
      intro hd
      obtain ⟨ih1, ih2⟩ := ih (by lia)
      rw [← Nat.add_assoc, events_succ]
      by_cases hb : ev (a + d) = true
      · -- something fires at `a + d`: nothing else fired in `[a, a + d)`
        have hnone : ∀ u, a ≤ u → u < a + d → ev u = false := by
          intro u hu hud
          by_cases hu' : ev u = true
          · have := hok u (a + d) hud (by lia) (hev u hu') (hev _ hb)
            exact absurd this (by lia)
          · simpa using hu'
        simp only [hb, if_true, List.length_append, List.length_singleton]
        rw [ih2 hnone]
        refine ⟨Nat.le_refl _, fun h => ?_⟩
        have := h (a + d) (by lia) (by lia)
        simp [this] at hb
      · have hb' : ev (a + d) = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, if_false, List.append_nil]
        exact ⟨ih1, fun hnone => ih2 fun u hu hud => hnone u hu (by lia)⟩
  have := (key (b - a) (by lia)).1
  rwa [Nat.add_sub_cancel' hab] at this

/-- Write-side invariant at one instant.  `E` are the values enqueued so far, `dp` a lower
bound on the number of values dequeued as seen through the wire at the last edge, and `d`
the number dequeued so far. -/
structure WInv (sw : WReg α n) (E : List α) (dp d : Nat) : Prop where
  ptr : sw.ptr = BitVec.ofNat (n+1) E.length
  mem : ∀ i, d ≤ i → i < E.length → sw.mem (BitVec.ofNat n i) = E.getD i default
  sync : ∃ k₁ k₂, sw.q1 = gray (BitVec.ofNat (n+1) k₁) ∧ sw.q2 = gray (BitVec.ofNat (n+1) k₂) ∧
    k₂ ≤ k₁ ∧ k₁ ≤ dp ∧ E.length ≤ k₂ + 2 ^ n ∧ (sw.full = false → E.length < k₂ + 2 ^ n)

/-- Read-side invariant at one instant.  `D` are the values dequeued so far, `ep` a bound on
the number of values enqueued as seen through the wire at the last edge (first stage), and
`ep2` the bound for the second stage, which saw the wire one edge earlier. -/
structure RInv (sr : RReg n) (D : List α) (ep ep2 : Nat) : Prop where
  ptr : sr.ptr = BitVec.ofNat (n+1) D.length
  sync : ∃ j₁ j₂, sr.q1 = gray (BitVec.ofNat (n+1) j₁) ∧ sr.q2 = gray (BitVec.ofNat (n+1) j₂) ∧
    j₂ ≤ j₁ ∧ j₁ ≤ ep ∧ j₂ ≤ ep2 ∧ D.length ≤ j₂ ∧ (sr.empty = false → D.length < j₂)

theorem WInv.mono_d {sw : WReg α n} {E : List α} {dp d d' : Nat} (h : WInv sw E dp d) (hd : d ≤ d') :
    WInv sw E dp d' :=
  ⟨h.ptr, fun i hi hiE => h.mem i (by lia) hiE, h.sync⟩

theorem WInv.cap_d {sw : WReg α n} {E : List α} {dp d : Nat} (h : WInv sw E dp d) (hdp : dp ≤ d) :
    E.length ≤ d + 2 ^ n := by
  obtain ⟨k₁, k₂, _, _, _, _, hcap, _⟩ := h.sync
  lia

theorem wstep_rise {stl : Nat} {sw : WReg α n} {i : WIn α n} (hr : i.rise = true) :
    wstep stl sw i =
      { ptr := if i.inc && !sw.full then sw.ptr + 1#(n+1) else sw.ptr
        full := (if i.inc && !sw.full then sw.ptr + 1#(n+1) else sw.ptr) ==
                  ungray sw.q2 + BitVec.ofNat (n+1) (2 ^ n)
        mem := if i.inc && !sw.full then (fun a => if a = sw.ptr.setWidth n then i.data else sw.mem a)
               else sw.mem
        q1 := mix i.orc.sel i.rgNew i.rgOld
        q2 := if stl ≤ sw.since then sw.q1 else i.orc.junk
        since := 0 } := by
  simp [wstep, hr]

theorem wstep_norise {stl : Nat} {sw : WReg α n} {i : WIn α n} (hr : i.rise = false) :
    wstep stl sw i = { sw with since := sw.since + 1 } := by
  simp [wstep, hr]

theorem rstep_rise {stl : Nat} {sr : RReg n} {i : RIn n} (hr : i.rise = true) :
    rstep stl sr i =
      { ptr := if i.inc && !sr.empty then sr.ptr + 1#(n+1) else sr.ptr
        empty := (if i.inc && !sr.empty then sr.ptr + 1#(n+1) else sr.ptr) == ungray sr.q2
        q1 := mix i.orc.sel i.wgNew i.wgOld
        q2 := if stl ≤ sr.since then sr.q1 else i.orc.junk
        since := 0 } := by
  simp [rstep, hr]

theorem rstep_norise {stl : Nat} {sr : RReg n} {i : RIn n} (hr : i.rise = false) :
    rstep stl sr i = { sr with since := sr.since + 1 } := by
  simp [rstep, hr]

theorem two_pow_succ' (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- One instant of the write domain preserves the write-side invariant, provided the first
stage has settled whenever there is an edge (`hset`) and, at an edge, the sampled count `k₀`
lies between the old bound and the new one. -/
theorem WInv.step {sw : WReg α n} {E : List α} {dp dp' d : Nat} {i : WIn α n} {k₀ : Nat}
    (h : WInv sw E dp d) (hdp : dp ≤ dp') (hdp' : dp' ≤ d) (hdE : d ≤ E.length)
    (hset : i.rise = true → stl ≤ sw.since)
    (hq : i.rise = true → mix i.orc.sel i.rgNew i.rgOld = gray (BitVec.ofNat (n+1) k₀))
    (hk₀l : i.rise = true → dp ≤ k₀) (hk₀u : i.rise = true → k₀ ≤ dp') :
    WInv (wstep stl sw i) (E ++ (if i.rise && i.inc && !sw.full then [i.data] else [])) dp' d := by
  obtain ⟨hptr, hmem, k₁, k₂, hq1, hq2, hk, hk₁, hcap, hfull⟩ := h
  have hk₂d : k₂ ≤ d := by lia
  have h2n := two_pow_succ' n
  have h2p := Nat.two_pow_pos n
  by_cases hr : i.rise = true
  · rw [wstep_rise hr]
    have hs := hset hr
    have hq := hq hr
    have hk₀l := hk₀l hr
    have hk₀u := hk₀u hr
    by_cases hok : (i.inc && !sw.full) = true
    · -- a write happens
      have hev : (i.rise && i.inc && !sw.full) = true := by simp_all
      have hnf : sw.full = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok; exact hok.2
      have hlt := hfull hnf
      simp only [hok, hev, hs, if_true]
      refine ⟨?_, ?_, ?_⟩
      · simp only; rw [hptr, ← ofNat_succ]; simp
      · intro j hj hjE
        simp only [List.length_append, List.length_singleton] at hjE
        simp only
        rw [hptr, setWidth_ofNat_succ]
        by_cases hjE' : j < E.length
        · rw [if_neg (ofNat_ne_ofNat_of_lt hjE' (by lia)), hmem j hj hjE']
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjE']
        · have : j = E.length := by lia
          subst this
          simp [List.getD_eq_getElem?_getD]
      · refine ⟨k₀, k₁, hq, hq1, by lia, hk₀u, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]; lia
        · intro hf
          simp only [List.length_append, List.length_singleton]
          simp only [hq2, ungray_gray, hptr, ← ofNat_succ, beq_eq_false_iff_ne, ne_eq] at hf
          rw [ofNat_eq_add_twoPow_iff (by lia) (by lia)] at hf
          lia
    · -- no write
      have hok' : (i.inc && !sw.full) = false := by simpa using hok
      have hev : (i.rise && i.inc && !sw.full) = false := by
        simp only [hr, Bool.true_and]; exact hok'
      simp only [hok', hev, hs, Bool.false_eq_true, if_false, if_true, List.append_nil]
      refine ⟨hptr, hmem, ?_⟩
      refine ⟨k₀, k₁, hq, hq1, by lia, hk₀u, by lia, ?_⟩
      intro hf
      simp only [hq2, ungray_gray, hptr, beq_eq_false_iff_ne, ne_eq] at hf
      rw [ofNat_eq_add_twoPow_iff (by lia) (by lia)] at hf
      lia
  · have hr' : i.rise = false := by simpa using hr
    rw [wstep_norise hr']
    have hev : (i.rise && i.inc && !sw.full) = false := by simp [hr']
    simp only [hev, Bool.false_eq_true, if_false, List.append_nil]
    exact ⟨hptr, fun j hj hjE => hmem j (by lia) hjE, k₁, k₂, hq1, hq2, hk, by lia, hcap, hfull⟩

/-- A dequeue reads the right value: the read side never runs ahead of the write side. -/
theorem RInv.step_prefix {sr : RReg n} {D E : List α} {ep ep2 : Nat} {i : RIn n} {memv : BitVec n → α}
    (h : RInv sr D ep ep2) (_hep : ep ≤ E.length) (hDE : D <+: E)
    (hmem : (i.rise && i.inc && !sr.empty) = true → memv (sr.ptr.setWidth n) = E.getD D.length default) :
    D ++ (if i.rise && i.inc && !sr.empty then [memv (sr.ptr.setWidth n)] else []) <+: E := by
  by_cases hd : (i.rise && i.inc && !sr.empty) = true
  · rw [if_pos hd]
    have hne : sr.empty = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hd; exact hd.2
    obtain ⟨j₁, j₂, _, _, hj, hj₁, _, hDj, hlt⟩ := h.sync
    have hlt := hlt hne
    have hDE' : D.length < E.length := by lia
    rw [hmem hd]
    exact prefix_append_getD hDE hDE' default
  · rw [if_neg hd]; simpa using hDE

/-- The number of the entry read at a dequeue is the number of values dequeued so far. -/
theorem RInv.read_index {sr : RReg n} {D : List α} {ep ep2 : Nat} (h : RInv sr D ep ep2) :
    sr.ptr.setWidth n = BitVec.ofNat n D.length := by
  rw [h.ptr, setWidth_ofNat_succ]

/-- One instant of the read domain preserves the read-side invariant, provided the first
stage has settled whenever there is an edge. -/
theorem RInv.step {sr : RReg n} {D E : List α} {ep ep' ep2 ep2' : Nat} {i : RIn n} {k₀ : Nat} {memv : BitVec n → α}
    (h : RInv sr D ep ep2) (hep : ep ≤ ep') (hep' : ep' ≤ E.length) (hDE : D <+: E)
    (hep2 : ep2 ≤ ep2') (hep2' : i.rise = true → ep ≤ ep2')
    (hcap : E.length ≤ D.length + 2 ^ n)
    (hset : i.rise = true → stl ≤ sr.since)
    (hq : i.rise = true → mix i.orc.sel i.wgNew i.wgOld = gray (BitVec.ofNat (n+1) k₀))
    (hk₀l : i.rise = true → ep ≤ k₀) (hk₀u : i.rise = true → k₀ ≤ ep') :
    RInv (rstep stl sr i) (D ++ (if i.rise && i.inc && !sr.empty then [memv (sr.ptr.setWidth n)] else []))
      ep' ep2' := by
  obtain ⟨hptr, j₁, j₂, hq1, hq2, hj, hj₁, hj₂, hDj, hempty⟩ := h
  have hDE' := hDE.length_le
  have h2n := two_pow_succ' n
  have h2p := Nat.two_pow_pos n
  by_cases hr : i.rise = true
  · rw [rstep_rise hr]
    have hs := hset hr
    have hq := hq hr
    have hk₀l := hk₀l hr
    have hk₀u := hk₀u hr
    have hep2' := hep2' hr
    by_cases hok : (i.inc && !sr.empty) = true
    · have hev : (i.rise && i.inc && !sr.empty) = true := by simp_all
      have hne : sr.empty = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok; exact hok.2
      have hlt := hempty hne
      simp only [hok, hev, hs, if_true]
      refine ⟨?_, ?_⟩
      · simp only; rw [hptr, ← ofNat_succ]; simp
      · refine ⟨k₀, j₁, hq, hq1, by lia, hk₀u, by lia, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]; lia
        · intro hf
          simp only [List.length_append, List.length_singleton]
          simp only [hq2, ungray_gray, hptr, ← ofNat_succ, beq_eq_false_iff_ne, ne_eq] at hf
          rw [eq_comm, ofNat_eq_ofNat_iff_of_le (by lia) (by lia)] at hf
          lia
    · have hok' : (i.inc && !sr.empty) = false := by simpa using hok
      have hev : (i.rise && i.inc && !sr.empty) = false := by
        simp only [hr, Bool.true_and]; exact hok'
      simp only [hok', hev, hs, Bool.false_eq_true, if_false, if_true, List.append_nil]
      refine ⟨hptr, k₀, j₁, hq, hq1, by lia, hk₀u, by lia, by lia, ?_⟩
      intro hf
      simp only [hq2, ungray_gray, hptr, beq_eq_false_iff_ne, ne_eq] at hf
      rw [eq_comm, ofNat_eq_ofNat_iff_of_le (by lia) (by lia)] at hf
      lia
  · have hr' : i.rise = false := by simpa using hr
    rw [rstep_norise hr']
    have hev : (i.rise && i.inc && !sr.empty) = false := by simp [hr']
    simp only [hev, Bool.false_eq_true, if_false, List.append_nil]
    exact ⟨hptr, j₁, j₂, hq1, hq2, hj, by lia, by lia, hDj, hempty⟩

/-- Enqueues extend the machine view by one element exactly at write events. -/
theorem enqM_succ (t : Nat) :
    enqM lat stl su wclk winc wdata rgray_w orcw (t + 1) =
      enqM lat stl su wclk winc wdata rgray_w orcw t ++
        (if (winp lat su wclk winc wdata rgray_w orcw t).rise && (winp lat su wclk winc wdata rgray_w orcw t).inc &&
            !(wRun lat stl su wclk winc wdata rgray_w orcw t).full
         then [(winp lat su wclk winc wdata rgray_w orcw t).data] else []) := by
  unfold enqM; rw [events_succ]; rfl

theorem deqM_succ (t : Nat) :
    deqM lat stl su rclk rinc wgray_r orcr mem_r (t + 1) =
      deqM lat stl su rclk rinc wgray_r orcr mem_r t ++
        (if (rinp lat su rclk rinc wgray_r orcr t).rise && (rinp lat su rclk rinc wgray_r orcr t).inc &&
            !(rRun lat stl su rclk rinc wgray_r orcr t).empty
         then [(mem_r.getD t (fun _ => default)) ((rRun lat stl su rclk rinc wgray_r orcr t).ptr.setWidth n)]
         else []) := by
  unfold deqM; rw [events_succ]; rfl

theorem gray_zero : gray (0#(n+1)) = 0#(n+1) := by simp [gray]

/-- Dequeues only happen at rising edges of the read clock. -/
theorem rDeq_rise {t : Nat} (h : rDeq lat stl su rclk rinc wgray_r orcr t = true) : riseAt rclk t = true := by
  unfold rDeq rinp at h; simp only [Bool.and_eq_true] at h; exact h.1.1

/-- Enqueues only happen at rising edges of the write clock. -/
theorem wEnq_rise {t : Nat} (h : wEnq lat stl su wclk winc wdata rgray_w orcw t = true) : riseAt wclk t = true := by
  unfold wEnq winp at h; simp only [Bool.and_eq_true] at h; exact h.1.1

/-- An enqueue at instant `e` is a write of entry `ptr mod 2^n`, whose number is the number of
values enqueued before `e`. -/
theorem wEnq_iff (t : Nat) :
    wEnq lat stl su wclk winc wdata rgray_w orcw t = true ↔
      riseAt wclk t = true ∧ (winc.getD t false && !(wRun lat stl su wclk winc wdata rgray_w orcw t).full) = true := by
  unfold wEnq winp; simp [Bool.and_assoc]

end Invariant


end Graphiti.AsyncFifo
