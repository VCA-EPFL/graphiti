/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Domains

/-!
# Filtered (timing-aware) specifications of the two clock domains

The register-level machines of `Domains.lean` produce exact output streams.  A timed
implementation (`Timed.lean`) cannot match them exactly: after every clock edge its
registers are in their clk-to-q window, and after a violated timing assumption anything
may happen.  Following Kobler's report, the specification of a domain therefore *says
nothing* at those instants: the relations below constrain an output stream only

* at instants before the first violation of the domain's timing assumptions (`WFilter`:
  clock period `P` respected, synchronous inputs stable for `S` instants before each edge,
  no edge before the reset time `R`),
* and, for registered outputs, outside the clk-to-q window `kq` after the last edge
  (`Settled`); inside the window the Gray pointer register is only required to be
  glitch-free (each bit old or new), the memory only for entries not being written.

Every relation bounds the stream by the Level-0 horizon `wLen + 1` / `rLen + 1`: a stream
may not carry values the machine cannot yet compute.  This is what makes the relations
monotone in the driver's inputs (`WGrayF.mono` …), which the FIFO-level proof needs, and
what the timed blocks' length conventions in `Timed.lean` are chosen to respect.

The exact machines satisfy the relaxed relations (`WGrayF.of_exact` …), so the exact domains
refine the filtered ones.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

open Gray

/-- Register outputs are meaningful `kq` instants after the last edge, and before any edge. -/
def Settled (kq : Nat) (clk : List Bool) (t : Nat) : Prop :=
  NoEdge clk t ∨ ∃ e, LastEdge clk e t ∧ e + kq ≤ t

theorem NoEdge_congr {clk clk' : List Bool} (h : clk <+: clk') {t : Nat} (ht : t ≤ clk.length) :
    NoEdge clk t ↔ NoEdge clk' t := by
  unfold NoEdge
  constructor <;> intro hn e he
  · rw [← riseAt_prefix h (by lia)]; exact hn e he
  · rw [riseAt_prefix h (by lia)]; exact hn e he

/-- Beyond the end of a stream there are no edges: the padding is low. -/
theorem riseAt_of_ge {clk : List Bool} {u : Nat} (h : clk.length ≤ u) : riseAt clk u = false := by
  unfold riseAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- An edge of a stream is an edge of any prefix of it that is long enough to show it.  Unlike
`NoEdge_congr` this needs no bound on `t`: past the end of `clk` the padding is low, so extra
instants cannot hide an edge. -/
theorem NoEdge_of_prefix {clk clk' : List Bool} (h : clk <+: clk') {t : Nat}
    (hn : NoEdge clk' t) : NoEdge clk t := by
  intro e he
  by_cases hlt : e < clk.length
  · rw [riseAt_prefix h hlt]; exact hn e he
  · exact riseAt_of_ge (by omega)

theorem LastEdge_of_prefix {clk clk' : List Bool} (h : clk <+: clk') {e t : Nat}
    (hec : e < clk.length) (hl : LastEdge clk' e t) : LastEdge clk e t := by
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨h1, by rw [riseAt_prefix h hec]; exact h2, fun e' h4 h5 => ?_⟩
  by_cases hlt : e' < clk.length
  · rw [riseAt_prefix h hlt]; exact h3 e' h4 h5
  · exact riseAt_of_ge (by omega)

theorem LastEdge_congr {clk clk' : List Bool} (h : clk <+: clk') {e t : Nat} (ht : t ≤ clk.length) :
    LastEdge clk e t ↔ LastEdge clk' e t := by
  unfold LastEdge
  constructor <;> rintro ⟨h1, h2, h3⟩
  · refine ⟨h1, by rw [← riseAt_prefix h (by lia)]; exact h2, fun e' h4 h5 => ?_⟩
    rw [← riseAt_prefix h (by lia)]; exact h3 e' h4 h5
  · refine ⟨h1, by rw [riseAt_prefix h (by lia)]; exact h2, fun e' h4 h5 => ?_⟩
    rw [riseAt_prefix h (by lia)]; exact h3 e' h4 h5

theorem Settled_congr {kq : Nat} {clk clk' : List Bool} (h : clk <+: clk') {t : Nat} (ht : t ≤ clk.length) :
    Settled kq clk t ↔ Settled kq clk' t := by
  unfold Settled
  rw [NoEdge_congr h ht]
  constructor <;> rintro (hn | ⟨e, he, hk⟩)
  · exact Or.inl hn
  · exact Or.inr ⟨e, (LastEdge_congr h ht).mp he, hk⟩
  · exact Or.inl hn
  · exact Or.inr ⟨e, (LastEdge_congr h ht).mpr he, hk⟩

theorem Settled.zero {kq : Nat} {clk : List Bool} : Settled kq clk 0 := Or.inl (fun e he => absurd he (Nat.not_lt_zero e))

/-- If there is an edge before `t`, there is a last one. -/
theorem exists_lastEdge {clk : List Bool} {t : Nat} (h : ¬ NoEdge clk t) : ∃ e, LastEdge clk e t := by
  induction t with
  | zero => exact absurd (fun e he => absurd he (Nat.not_lt_zero e)) h
  | succ t ih =>
    by_cases hr : riseAt clk t = true
    · exact ⟨t, Nat.lt_succ_self t, hr, fun e' h1 h2 => absurd (Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h2)) (Nat.lt_irrefl _)⟩
    · have hr' : riseAt clk t = false := by simpa using hr
      have : ¬ NoEdge clk t := by
        intro hn; apply h; intro e he
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with h | h
        · exact hn e h
        · subst h; exact hr'
      obtain ⟨e, he, hre, hl⟩ := ih this
      refine ⟨e, by lia, hre, fun e' h1 h2 => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with h | h
      · exact hl e' h1 h
      · subst h; exact hr'

/-- Not settled: inside the clk-to-q window of the last edge. -/
theorem not_settled {kq : Nat} {clk : List Bool} {t : Nat} (h : ¬ Settled kq clk t) :
    ∃ e, LastEdge clk e t ∧ t < e + kq := by
  have hn : ¬ NoEdge clk t := fun hn => h (Or.inl hn)
  obtain ⟨e, he⟩ := exists_lastEdge hn
  refine ⟨e, he, ?_⟩
  by_cases hk : e + kq ≤ t
  · exact absurd (Or.inr ⟨e, he, hk⟩) h
  · lia

/-- At a rising edge of a clock respecting the period `P > kq`, the registers have settled. -/
theorem settled_at_edge {kq P : Nat} {clk : List Bool} {t : Nat} (hok : ClockOK P clk (t + 1)) (hkP : kq < P)
    (hr : riseAt clk t = true) : Settled kq clk t := by
  by_cases hn : NoEdge clk t
  · exact Or.inl hn
  · obtain ⟨e, he⟩ := exists_lastEdge hn
    have := hok e t he.1 (Nat.lt_succ_self t) he.2.1 hr
    exact Or.inr ⟨e, he, by lia⟩

/-! ### Write domain -/

section WriteF

variable {α : Type} [Inhabited α] {n : Nat}
variable (lat stl su kq P S R pw : Nat) (clk inc : List Bool) (data : List α) (rgray : List (BitVec (n+1))) (orc : List (Orc n))

/-- The write domain's timing assumptions hold for all edges before `t`.  The last one, on the
width of the clock's pulses, is what a netlist of gates needs and a register-level model does
not; it is a promise about the environment like the others. -/
def WFilter (t : Nat) : Prop :=
  ClockOK P clk t ∧ InOK S clk inc t ∧ InOK S clk data t ∧ ResetOK R clk t ∧ PulseOK pw clk t

/-- Relaxed Gray-pointer output: exact when settled, glitch-free inside the clk-to-q window. -/
def WGrayF (v : List (BitVec (n+1))) : Prop :=
  v.length ≤ wLen lat clk inc data rgray orc + 1 ∧
  ∀ t, t < v.length → WFilter P S R pw clk inc data t →
    (Settled kq clk t → v.getD t 0 = gray (wRun lat stl su clk inc data rgray orc t).ptr) ∧
    (∀ e, LastEdge clk e t → t < e + kq → ∀ i,
      (v.getD t 0).getLsbD i = (gray (wRun lat stl su clk inc data rgray orc t).ptr).getLsbD i ∨
      (v.getD t 0).getLsbD i = (gray (wRun lat stl su clk inc data rgray orc e).ptr).getLsbD i)

/-- Relaxed `full` output: exact when settled. -/
def WFullF (v : List Bool) : Prop :=
  v.length ≤ wLen lat clk inc data rgray orc + 1 ∧
  ∀ t, t < v.length → WFilter P S R pw clk inc data t → Settled kq clk t →
    v.getD t false = (wRun lat stl su clk inc data rgray orc t).full

/-- A write to entry `a` at (edge) instant `e`, as decided by the machine. -/
def WriteAt (a : BitVec n) (e : Nat) : Prop :=
  riseAt clk e = true ∧ (inc.getD e false && !(wRun lat stl su clk inc data rgray orc e).full) = true ∧
  (wRun lat stl su clk inc data rgray orc e).ptr.setWidth n = a

/-- Entry `a` is outside the clk-to-q window of any write to it. -/
def MemSettled (a : BitVec n) (t : Nat) : Prop :=
  ∀ e, e < t → WriteAt lat stl su clk inc data rgray orc a e → e + kq ≤ t

/-- Relaxed memory output: exact for entries not being written. -/
def WMemF (v : List (BitVec n → α)) : Prop :=
  v.length ≤ wLen lat clk inc data rgray orc + 1 ∧
  ∀ t, t < v.length → WFilter P S R pw clk inc data t → ∀ a, MemSettled lat stl su kq clk inc data rgray orc a t →
    (v.getD t (fun _ => default)) a = (wRun lat stl su clk inc data rgray orc t).mem a

variable {lat stl su kq P S R pw clk inc data rgray orc}

/-- Prefixes of the exact outputs satisfy the relaxed relations (for any `kq`). -/
theorem WGrayF.of_exact {v : List (BitVec (n+1))} (h : v <+: wGray lat stl su clk inc data rgray orc) :
    WGrayF lat stl su kq P S R pw clk inc data rgray orc v := by
  have hl := h.length_le
  simp only [wGray_length] at hl
  refine ⟨hl, fun t ht _ => ⟨fun _ => ?_, fun e _ _ i => Or.inl ?_⟩⟩
  · rw [h.getD_eq_left ht]; exact wGray_getD _ _ _ _ _ _ _ _ (by lia) _
  · rw [h.getD_eq_left ht, wGray_getD _ _ _ _ _ _ _ _ (by lia)]

theorem WFullF.of_exact {v : List Bool} (h : v <+: wFull lat stl su clk inc data rgray orc) :
    WFullF lat stl su kq P S R pw clk inc data rgray orc v := by
  have hl := h.length_le
  simp only [wFull_length] at hl
  refine ⟨hl, fun t ht _ _ => ?_⟩
  rw [h.getD_eq_left ht]; exact wFull_getD _ _ _ _ _ _ _ _ (by lia) _

theorem WMemF.of_exact {v : List (BitVec n → α)} (h : v <+: wMem lat stl su clk inc data rgray orc) :
    WMemF lat stl su kq P S R pw clk inc data rgray orc v := by
  have hl := h.length_le
  simp only [wMem_length] at hl
  refine ⟨hl, fun t ht _ a _ => ?_⟩
  rw [h.getD_eq_left ht, wMem_getD _ _ _ _ _ _ _ _ (by lia)]

/-- The relaxed relations are prefix-closed. -/
theorem WGrayF.of_prefix {v v' : List (BitVec (n+1))} (h : v' <+: v)
    (hv : WGrayF lat stl su kq P S R pw clk inc data rgray orc v) : WGrayF lat stl su kq P S R pw clk inc data rgray orc v' := by
  have hl := h.length_le
  have hl' := hv.1
  refine ⟨by lia, fun t ht hf => ?_⟩
  rw [h.getD_eq_left ht]; exact hv.2 t (by lia) hf

theorem WFullF.of_prefix {v v' : List Bool} (h : v' <+: v)
    (hv : WFullF lat stl su kq P S R pw clk inc data rgray orc v) : WFullF lat stl su kq P S R pw clk inc data rgray orc v' := by
  have hl := h.length_le
  have hl' := hv.1
  refine ⟨by lia, fun t ht hf hs => ?_⟩
  rw [h.getD_eq_left ht]; exact hv.2 t (by lia) hf hs

theorem WMemF.of_prefix {v v' : List (BitVec n → α)} (h : v' <+: v)
    (hv : WMemF lat stl su kq P S R pw clk inc data rgray orc v) : WMemF lat stl su kq P S R pw clk inc data rgray orc v' := by
  have hl := h.length_le
  have hl' := hv.1
  refine ⟨by lia, fun t ht hf a hm => ?_⟩
  rw [h.getD_eq_left ht]; exact hv.2 t (by lia) hf a hm

/-- The filter and the derived notions only look at instants before `t`, so they agree on
prefixes covering `t`. -/
theorem WFilter_congr {clk' inc' : List Bool} {data' : List α}
    (h₁ : clk <+: clk') (h₂ : inc <+: inc') (h₃ : data <+: data') {t : Nat}
    (l₁ : t ≤ clk.length) (l₂ : t ≤ inc.length) (l₃ : t ≤ data.length) :
    WFilter P S R pw clk' inc' data' t → WFilter P S R pw clk inc data t := by
  rintro ⟨hc, hi, hd, hr, hp⟩
  exact ⟨hc.congr h₁ l₁, InOK.congr h₁ h₂ l₁ l₂ hi, InOK.congr h₁ h₃ l₁ l₃ hd, hr.congr h₁ l₁,
    hp.congr h₁ l₁⟩

theorem WriteAt_congr {clk' inc' : List Bool} {data' : List α} {rgray' : List (BitVec (n+1))} {orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : inc <+: inc') (h₃ : data <+: data') (h₄ : rgray <+: rgray') (h₅ : orc <+: orc')
    {a : BitVec n} {e : Nat} (he : e < wLen lat clk inc data rgray orc) :
    WriteAt lat stl su clk inc data rgray orc a e ↔ WriteAt lat stl su clk' inc' data' rgray' orc' a e := by
  have hwl := wLen_le lat clk inc data rgray orc
  unfold WriteAt
  rw [riseAt_prefix h₁ (by lia), h₂.getD_eq_left (by lia), wRun_congr lat stl su clk inc data rgray orc h₁ h₂ h₃ h₄ h₅ (by lia)]

/-- Monotonicity of the relaxed relations in the driver's inputs. -/
theorem WGrayF.mono {clk' inc' : List Bool} {data' : List α} {rgray' : List (BitVec (n+1))} {orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : inc <+: inc') (h₃ : data <+: data') (h₄ : rgray <+: rgray') (h₅ : orc <+: orc')
    {v : List (BitVec (n+1))} (hv : WGrayF lat stl su kq P S R pw clk inc data rgray orc v) :
    WGrayF lat stl su kq P S R pw clk' inc' data' rgray' orc' v := by
  have hwl := wLen_le lat clk inc data rgray orc
  have hL := wLen_mono lat clk inc data rgray orc h₁ h₂ h₃ h₄ h₅
  obtain ⟨hlen, hv⟩ := hv
  refine ⟨by lia, fun t ht hf => ?_⟩
  have hf' := WFilter_congr h₁ h₂ h₃ (by lia) (by lia) (by lia) hf
  obtain ⟨hs, hw⟩ := hv t ht hf'
  rw [← wRun_congr lat stl su clk inc data rgray orc h₁ h₂ h₃ h₄ h₅ (by lia)]
  refine ⟨fun hset => hs ((Settled_congr h₁ (by lia)).mpr hset), fun e he hk i => ?_⟩
  have he' := (LastEdge_congr h₁ (by lia)).mpr he
  have het := he'.1
  rw [← wRun_congr lat stl su clk inc data rgray orc h₁ h₂ h₃ h₄ h₅ (t := e) (by lia)]
  exact hw e he' hk i

theorem WFullF.mono {clk' inc' : List Bool} {data' : List α} {rgray' : List (BitVec (n+1))} {orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : inc <+: inc') (h₃ : data <+: data') (h₄ : rgray <+: rgray') (h₅ : orc <+: orc')
    {v : List Bool} (hv : WFullF lat stl su kq P S R pw clk inc data rgray orc v) :
    WFullF lat stl su kq P S R pw clk' inc' data' rgray' orc' v := by
  have hwl := wLen_le lat clk inc data rgray orc
  have hL := wLen_mono lat clk inc data rgray orc h₁ h₂ h₃ h₄ h₅
  obtain ⟨hlen, hv⟩ := hv
  refine ⟨by lia, fun t ht hf hset => ?_⟩
  have hf' := WFilter_congr h₁ h₂ h₃ (by lia) (by lia) (by lia) hf
  rw [← wRun_congr lat stl su clk inc data rgray orc h₁ h₂ h₃ h₄ h₅ (by lia)]
  exact hv t ht hf' ((Settled_congr h₁ (by lia)).mpr hset)

theorem WMemF.mono {clk' inc' : List Bool} {data' : List α} {rgray' : List (BitVec (n+1))} {orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : inc <+: inc') (h₃ : data <+: data') (h₄ : rgray <+: rgray') (h₅ : orc <+: orc')
    {v : List (BitVec n → α)} (hv : WMemF lat stl su kq P S R pw clk inc data rgray orc v) :
    WMemF lat stl su kq P S R pw clk' inc' data' rgray' orc' v := by
  have hwl := wLen_le lat clk inc data rgray orc
  have hL := wLen_mono lat clk inc data rgray orc h₁ h₂ h₃ h₄ h₅
  obtain ⟨hlen, hv⟩ := hv
  refine ⟨by lia, fun t ht hf a hm => ?_⟩
  have hf' := WFilter_congr h₁ h₂ h₃ (by lia) (by lia) (by lia) hf
  rw [← wRun_congr lat stl su clk inc data rgray orc h₁ h₂ h₃ h₄ h₅ (by lia)]
  refine hv t ht hf' a fun e he hw => hm e he ?_
  exact (WriteAt_congr h₁ h₂ h₃ h₄ h₅ (by lia)).mp hw

end WriteF

/-! ### Read domain -/

section ReadF

variable {α : Type} [Inhabited α] {n : Nat}
variable (lat stl su kq rdly P S R pw : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n))
  (mem : List (BitVec n → α))

def RFilter (t : Nat) : Prop :=
  ClockOK P rclk t ∧ InOK S rclk rinc t ∧ ResetOK R rclk t ∧ PulseOK pw rclk t

def RGrayF (v : List (BitVec (n+1))) : Prop :=
  v.length ≤ rLen lat rclk rinc wgray orc + 1 ∧
  ∀ t, t < v.length → RFilter P S R pw rclk rinc t →
    (Settled kq rclk t → v.getD t 0 = gray (rRun lat stl su rclk rinc wgray orc t).ptr) ∧
    (∀ e, LastEdge rclk e t → t < e + kq → ∀ i,
      (v.getD t 0).getLsbD i = (gray (rRun lat stl su rclk rinc wgray orc t).ptr).getLsbD i ∨
      (v.getD t 0).getLsbD i = (gray (rRun lat stl su rclk rinc wgray orc e).ptr).getLsbD i)

def REmptyF (v : List Bool) : Prop :=
  v.length ≤ rLen lat rclk rinc wgray orc + 1 ∧
  ∀ t, t < v.length → RFilter P S R pw rclk rinc t → Settled kq rclk t →
    v.getD t false = (rRun lat stl su rclk rinc wgray orc t).empty

/-- Entry `a` held its value over the read port's window `d`.  This is what an asynchronous read
port needs of the memory, and all it needs: a write to any *other* entry is invisible to it. -/
def MemHold (d : Nat) (m : List (BitVec n → α)) (a : BitVec n) (t : Nat) : Prop :=
  ∀ u, t - d ≤ u → u ≤ t → (m.getD u (fun _ => default)) a = (m.getD t (fun _ => default)) a

/-- Relaxed read data: the memory word at the read address, once the pointer has settled *and*
the read port's own window `rdly` has passed.  The port is combinational, so it needs two things
its neighbours do not: the address settled `rdly` longer than a register would (`kq + rdly`), and
the entry it addresses held over that window --- the one place a read-domain output depends on
the write domain's timing. -/
def RDataF (v : List α) : Prop :=
  v.length ≤ rDataLen lat rclk rinc wgray orc mem ∧
  ∀ t, rdly ≤ t → t < v.length → RFilter P S R pw rclk rinc t → Settled (kq + rdly) rclk t →
    MemHold rdly mem ((rRun lat stl su rclk rinc wgray orc t).ptr.setWidth n) t →
    v.getD t default = rval lat stl su rclk rinc wgray orc mem t

variable {lat stl su kq rdly P S R pw rclk rinc wgray orc mem}

theorem RGrayF.of_exact {v : List (BitVec (n+1))} (h : v <+: rGray lat stl su rclk rinc wgray orc) :
    RGrayF lat stl su kq P S R pw rclk rinc wgray orc v := by
  have hl := h.length_le
  simp only [rGray_length] at hl
  refine ⟨hl, fun t ht _ => ⟨fun _ => ?_, fun e _ _ i => Or.inl ?_⟩⟩
  · rw [h.getD_eq_left ht]; exact rGray_getD _ _ _ _ _ _ _ (by lia) _
  · rw [h.getD_eq_left ht, rGray_getD _ _ _ _ _ _ _ (by lia)]

theorem REmptyF.of_exact {v : List Bool} (h : v <+: rEmpty lat stl su rclk rinc wgray orc) :
    REmptyF lat stl su kq P S R pw rclk rinc wgray orc v := by
  have hl := h.length_le
  simp only [rEmpty_length] at hl
  refine ⟨hl, fun t ht _ _ => ?_⟩
  rw [h.getD_eq_left ht]; exact rEmpty_getD _ _ _ _ _ _ _ (by lia) _

theorem RDataF.of_exact {v : List α} (h : v <+: rData lat stl su rclk rinc wgray orc mem) :
    RDataF lat stl su kq rdly P S R pw rclk rinc wgray orc mem v := by
  have hl := h.length_le
  simp only [rData_length] at hl
  refine ⟨hl, fun t _ ht _ _ _ => ?_⟩
  rw [h.getD_eq_left ht]; exact rData_getD _ _ _ _ _ _ _ _ (by lia) _

theorem RGrayF.of_prefix {v v' : List (BitVec (n+1))} (h : v' <+: v)
    (hv : RGrayF lat stl su kq P S R pw rclk rinc wgray orc v) : RGrayF lat stl su kq P S R pw rclk rinc wgray orc v' := by
  have hl := h.length_le
  have hl' := hv.1
  refine ⟨by lia, fun t ht hf => ?_⟩
  rw [h.getD_eq_left ht]; exact hv.2 t (by lia) hf

theorem REmptyF.of_prefix {v v' : List Bool} (h : v' <+: v)
    (hv : REmptyF lat stl su kq P S R pw rclk rinc wgray orc v) : REmptyF lat stl su kq P S R pw rclk rinc wgray orc v' := by
  have hl := h.length_le
  have hl' := hv.1
  refine ⟨by lia, fun t ht hf hs => ?_⟩
  rw [h.getD_eq_left ht]; exact hv.2 t (by lia) hf hs

theorem RDataF.of_prefix {v v' : List α} (h : v' <+: v)
    (hv : RDataF lat stl su kq rdly P S R pw rclk rinc wgray orc mem v) :
    RDataF lat stl su kq rdly P S R pw rclk rinc wgray orc mem v' := by
  have hl := h.length_le
  have hl' := hv.1
  refine ⟨by lia, fun t htd ht hf hs hmh => ?_⟩
  rw [h.getD_eq_left ht]; exact hv.2 t htd (by lia) hf hs hmh

theorem RFilter_congr {rclk' rinc' : List Bool} (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') {t : Nat}
    (l₁ : t ≤ rclk.length) (l₂ : t ≤ rinc.length) :
    RFilter P S R pw rclk' rinc' t → RFilter P S R pw rclk rinc t := by
  rintro ⟨hc, hi, hr, hp⟩
  exact ⟨hc.congr h₁ l₁, InOK.congr h₁ h₂ l₁ l₂ hi, hr.congr h₁ l₁, hp.congr h₁ l₁⟩

theorem RGrayF.mono {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orc' : List (Orc n)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orc <+: orc')
    {v : List (BitVec (n+1))} (hv : RGrayF lat stl su kq P S R pw rclk rinc wgray orc v) :
    RGrayF lat stl su kq P S R pw rclk' rinc' wgray' orc' v := by
  have hrl := rLen_le lat rclk rinc wgray orc
  have hL := rLen_mono lat rclk rinc wgray orc h₁ h₂ h₃ h₄
  obtain ⟨hlen, hv⟩ := hv
  refine ⟨by lia, fun t ht hf => ?_⟩
  have hf' := RFilter_congr h₁ h₂ (by lia) (by lia) hf
  obtain ⟨hs, hw⟩ := hv t ht hf'
  rw [← rRun_congr lat stl su rclk rinc wgray orc h₁ h₂ h₃ h₄ (by lia)]
  refine ⟨fun hset => hs ((Settled_congr h₁ (by lia)).mpr hset), fun e he hk i => ?_⟩
  have he' := (LastEdge_congr h₁ (by lia)).mpr he
  have het := he'.1
  rw [← rRun_congr lat stl su rclk rinc wgray orc h₁ h₂ h₃ h₄ (t := e) (by lia)]
  exact hw e he' hk i

theorem REmptyF.mono {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orc' : List (Orc n)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orc <+: orc')
    {v : List Bool} (hv : REmptyF lat stl su kq P S R pw rclk rinc wgray orc v) :
    REmptyF lat stl su kq P S R pw rclk' rinc' wgray' orc' v := by
  have hrl := rLen_le lat rclk rinc wgray orc
  have hL := rLen_mono lat rclk rinc wgray orc h₁ h₂ h₃ h₄
  obtain ⟨hlen, hv⟩ := hv
  refine ⟨by lia, fun t ht hf hset => ?_⟩
  have hf' := RFilter_congr h₁ h₂ (by lia) (by lia) hf
  rw [← rRun_congr lat stl su rclk rinc wgray orc h₁ h₂ h₃ h₄ (by lia)]
  exact hv t ht hf' ((Settled_congr h₁ (by lia)).mpr hset)

theorem RDataF.mono {rclk' rinc' : List Bool} {wgray' : List (BitVec (n+1))} {orc' : List (Orc n)}
    {mem' : List (BitVec n → α)}
    (h₁ : rclk <+: rclk') (h₂ : rinc <+: rinc') (h₃ : wgray <+: wgray') (h₄ : orc <+: orc') (h₅ : mem <+: mem')
    {v : List α} (hv : RDataF lat stl su kq rdly P S R pw rclk rinc wgray orc mem v) :
    RDataF lat stl su kq rdly P S R pw rclk' rinc' wgray' orc' mem' v := by
  have hrl := rLen_le lat rclk rinc wgray orc
  have hL := rLen_mono lat rclk rinc wgray orc h₁ h₂ h₃ h₄
  have hm := h₅.length_le
  obtain ⟨hlen, hv⟩ := hv
  unfold rDataLen at hlen
  have ht₀ : v.length ≤ rLen lat rclk rinc wgray orc + 1 ∧ v.length ≤ mem.length := by omega
  refine ⟨by unfold rDataLen; omega, fun t htd ht hf hset hmh => ?_⟩
  have ht'' : t ≤ rLen lat rclk rinc wgray orc := by lia
  have hf' := RFilter_congr h₁ h₂ (by lia) (by lia) hf
  have hmh' : MemHold rdly mem ((rRun lat stl su rclk rinc wgray orc t).ptr.setWidth n) t := by
    intro u hu1 hu2
    rw [h₅.getD_eq_left (by lia), h₅.getD_eq_left (by lia)]
    rw [rRun_congr lat stl su rclk rinc wgray orc h₁ h₂ h₃ h₄ ht'']
    exact hmh u hu1 hu2
  rw [hv t htd ht hf' ((Settled_congr h₁ (by lia)).mpr hset) hmh']
  unfold rval
  rw [h₅.getD_eq_left (by lia), rRun_congr lat stl su rclk rinc wgray orc h₁ h₂ h₃ h₄ ht'']

end ReadF

end Graphiti.AsyncFifo
