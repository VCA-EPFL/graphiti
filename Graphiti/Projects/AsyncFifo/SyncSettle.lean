/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.BusRegTiming

/-!
# The synchroniser's bus assumption, derived from the per-bit one

`Timed.syncReg` is where this development writes down the metastability assumption, and it
writes it at the *bus* level: an oracle stream supplies, at every instant, which bits of the
sample resolved to the new value (`Orc.sel`) and what is observed while the stage is still
settling (`Orc.junk`), and `syncOut` is the resulting deterministic stream.  That is more than
the physics asks for -- it grants two freedoms at bus granularity, about a three-bit register.

This file shows the bus-level statement is *not* an extra assumption.  Given three bits, each
meeting `Timed.SettleOut` --- one clause about one bit, "from `stl` instants after an edge the
bit does not move, and it is one of the two values the data showed at the ends of the aperture"
--- the packed bus **is** `syncOut` for an oracle read off those three bits (`settle_orc`):

* `sel` at an edge `e`: bit `i` is set exactly when that bit settled to the value the wire
  showed at `e` rather than to the one it showed `su + 1` instants earlier;
* `junk` at `t`: whatever the three bits actually show at `t`.

So what is assumed reduces to three instances of `SettleOut`, and `Dff.dffOut_settleOut` proves
that clause is a *theorem* for our netlist whenever its data is stable over the aperture.  What
is left assumed is exactly the failure of that one hypothesis, for the flip-flops of the first
synchroniser stage and nowhere else --- which is what `Metastability.lean` argues cannot be
discharged in a deterministic Boolean model.

Nothing here weakens `syncReg`: the theorem produces the oracle, it does not consume one.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.SyncSettle

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff Graphiti.AsyncFifo.BusReg

/-! ### `mix`, bit by bit -/

/-- `mix` selects per bit: this is the computational form of `mix_choice`. -/
theorem mix_getLsbD {w : Nat} (sel a b : BitVec w) (i : Nat) :
    (mix sel a b).getLsbD i = if sel.getLsbD i then a.getLsbD i else b.getLsbD i := by
  simp only [mix, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases hi : i < w
  · cases hs : sel.getLsbD i <;> simp [hi]
  · have h1 := BitVec.getLsbD_of_ge a i (by lia)
    have h2 := BitVec.getLsbD_of_ge b i (by lia)
    have h3 := BitVec.getLsbD_of_ge sel i (by lia)
    simp_all

/-! ### The synchroniser stage's register, between edges -/

section Run

variable {n : Nat} {lat su stl : Nat} {clk : List Bool} {d : List (BitVec (n+1))}
  {orc : List (Orc n)}

theorem syncStep_rise {s : SyncReg n} {i : SyncIn n} (h : i.rise = true) :
    syncStep s i = ⟨mix i.orc.sel i.dNew i.dOld, 0⟩ := by simp [syncStep, h]

theorem syncStep_norise {s : SyncReg n} {i : SyncIn n} (h : i.rise = false) :
    syncStep s i = ⟨s.val, s.since + 1⟩ := by simp [syncStep, h]

/-- The `since` counter of the stage is the counter of `SinceInv`. -/
theorem syncRun_since (t : Nat) :
    SinceInv stl clk t (syncRun lat su stl clk d orc t).since := by
  induction t with
  | zero => exact SinceInv.zero _ _
  | succ t ih =>
    show SinceInv stl clk (t + 1)
      (syncStep (syncRun lat su stl clk d orc t) (syncInp lat su clk d orc t)).since
    by_cases hr : riseAt clk t = true
    · rw [syncStep_rise (i := syncInp lat su clk d orc t) hr]
      exact SinceInv.step_rise hr
    · have hr' : riseAt clk t = false := by simpa using hr
      rw [syncStep_norise (i := syncInp lat su clk d orc t) hr']
      exact ih.step_norise hr'

/-- Before the first edge the stage holds its initial value. -/
theorem syncRun_noedge {t : Nat} (h : NoEdge clk t) :
    syncRun lat su stl clk d orc t = ⟨0#(n+1), stl + t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h' : NoEdge clk t := fun e he => h e (by lia)
    have hr : riseAt clk t = false := h t (Nat.lt_succ_self t)
    show syncStep (syncRun lat su stl clk d orc t) (syncInp lat su clk d orc t) = _
    rw [syncStep_norise (i := syncInp lat su clk d orc t) hr, ih h']
    rfl

/-- At an edge the stage captures a per-bit mixture of the two ends of the aperture. -/
theorem syncRun_at_edge {e : Nat} (hre : riseAt clk e = true) :
    syncRun lat su stl clk d orc (e + 1) =
      ⟨mix (orc.getD e default).sel (delayed lat d e) (delayed lat d (e - su - 1)), 0⟩ := by
  show syncStep (syncRun lat su stl clk d orc e) (syncInp lat su clk d orc e) = _
  rw [syncStep_rise (i := syncInp lat su clk d orc e) hre]
  rfl

/-- Between edges only the counter moves. -/
theorem syncRun_lastEdge {e t : Nat} (h : LastEdge clk e t) :
    syncRun lat su stl clk d orc t =
      ⟨(syncRun lat su stl clk d orc (e + 1)).val, t - e - 1⟩ := by
  obtain ⟨het, hre, hno⟩ := h
  induction t with
  | zero => exact absurd het (Nat.not_lt_zero e)
  | succ t ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ het) with hlt | heq
    · have hr : riseAt clk t = false := hno t hlt (Nat.lt_succ_self t)
      show syncStep (syncRun lat su stl clk d orc t) (syncInp lat su clk d orc t) = _
      rw [syncStep_norise (i := syncInp lat su clk d orc t) hr,
        ih hlt (fun e' h1 h2 => hno e' h1 (by lia))]
      show SyncReg.mk _ _ = SyncReg.mk _ _
      congr 1
      lia
    · subst heq
      have h0 : (syncRun lat su stl clk d orc (e + 1)).since = 0 := by
        rw [syncRun_at_edge hre]
      have he0 : e + 1 - e - 1 = 0 := by lia
      rw [he0]
      generalize syncRun lat su stl clk d orc (e + 1) = r at *
      obtain ⟨val, since⟩ := r
      simp only at h0
      subst h0
      rfl

end Run

/-! ### The oracle, read off the bits -/

variable {kq su stl lat : Nat} {clk : List Bool} {d : List (BitVec 3)} {Q : Nat → List Bool}

/-- **The bus-level assumption is the per-bit one.**  Three bits each meeting `SettleOut`,
packed into a bus, are exactly what `Timed.syncReg` promises --- for any oracle that reports,
per bit, which end of the aperture that bit settled to, and reports as junk what the bits
actually show.  `orcOf` below is such an oracle, so one always exists. -/
theorem settle_orc_of {v : List (BitVec 3)} {orc : List (Orc 2)}
    (horclen : v.length ≤ orc.length)
    (hlen : v.length ≤ min clk.length (d.length + lat))
    (hQlen : ∀ i, i < 3 → v.length ≤ (Q i).length)
    (hbit : ∀ i, i < 3 →
      SettleOut kq su stl clk (fun u => (delayed lat d u).getLsbD i) (d.length + lat) (Q i))
    (hpack : ∀ t, t < v.length →
      v.getD t 0#3 = bv3 ((Q 0).getD t false) ((Q 1).getD t false) ((Q 2).getD t false))
    (hjunk : ∀ t, t < v.length → (orc.getD t default).junk =
      bv3 ((Q 0).getD t false) ((Q 1).getD t false) ((Q 2).getD t false))
    (hsel : ∀ t, t < v.length → ∀ i, i < 3 → ((orc.getD t default).sel).getLsbD i =
      decide ((Q i).getD (t + stl) false = (delayed lat d t).getLsbD i))
    (horcl : orc.length = v.length) :
    v = syncOut lat su stl clk d orc := by
  have hsl : syncLen lat clk d orc = v.length := by
    unfold syncLen
    rw [horcl]
    exact Nat.min_eq_right hlen
  have houtlen : (syncOut lat su stl clk d orc).length = v.length := by
    unfold syncOut; rw [timeline_length, hsl]
  have hQt : ∀ i, i < 3 → ∀ t, t < v.length → t < (Q i).length :=
    fun i hi t ht => Nat.lt_of_lt_of_le ht (hQlen i hi)
  have hval : ∀ t, t < v.length → v.getD t 0#3 =
      (if (syncRun lat su stl clk d orc t).since < stl
       then (orc.getD t default).junk else (syncRun lat su stl clk d orc t).val) := by
    intro t ht
    rcases syncRun_since (lat := lat) (su := su) (stl := stl) (d := d) (orc := orc) t with
      ⟨hno, hs⟩ | ⟨e, he, hs⟩
    · have hnot : ¬ ((syncRun lat su stl clk d orc t).since < stl) := by rw [hs]; lia
      rw [if_neg hnot, syncRun_noedge hno]
      show v.getD t 0#3 = 0#3
      have hz : ∀ i, i < 3 → (Q i).getD t false = false :=
        fun i hi => ((hbit i hi).1.2 t (hQt i hi t ht)).1 hno
      rw [hpack t ht, hz 0 (by lia), hz 1 (by lia), hz 2 (by lia)]
      rfl
    · have het := he.1
      have hsince : (syncRun lat su stl clk d orc t).since = t - e - 1 := by lia
      by_cases hj : t - e - 1 < stl
      · rw [hsince, if_pos hj, hpack t ht, hjunk t ht]
      · rw [hsince, if_neg hj, syncRun_lastEdge he, syncRun_at_edge he.2.1]
        show v.getD t 0#3 = mix _ _ _
        have hst : e + stl ≤ t := by lia
        have hel : e < v.length := by lia
        have key : ∀ i, i < 3 → (Q i).getD t false =
            (mix (orc.getD e default).sel (delayed lat d e)
              (delayed lat d (e - su - 1))).getLsbD i := by
          intro i hi
          obtain ⟨hstay, hchoice⟩ := (hbit i hi).2 t (hQt i hi t ht) e he hst
          rw [mix_getLsbD, hsel e hel i hi, hstay]
          cases hd : decide ((Q i).getD (e + stl) false = (delayed lat d e).getLsbD i) with
          | true => rw [if_pos rfl]; exact of_decide_eq_true hd
          | false =>
            rw [if_neg (by simp)]
            exact hchoice.resolve_left (of_decide_eq_false hd)
        rw [hpack t ht, key 0 (by lia), key 1 (by lia), key 2 (by lia)]
        exact bv3_bits _
  refine ((prefix_iff_length_getD (0#3)).mpr ⟨by omega, fun t ht => ?_⟩).eq_of_length (by omega)
  rw [hval t ht]
  unfold syncOut
  rw [timeline_getD _ (by rw [hsl]; exact ht)]

/-- The oracle a settled stage determines: at each instant, which bits took the value the wire
showed at the last edge, and what the bits actually show while the stage settles. -/
def orcOf (lat su stl : Nat) (d : List (BitVec 3)) (Q : Nat → List Bool) (L : Nat) : List (Orc 2) :=
  timeline (fun t =>
    ⟨bv3 (decide ((Q 0).getD (t + stl) false = (delayed lat d t).getLsbD 0))
         (decide ((Q 1).getD (t + stl) false = (delayed lat d t).getLsbD 1))
         (decide ((Q 2).getD (t + stl) false = (delayed lat d t).getLsbD 2)),
     bv3 ((Q 0).getD t false) ((Q 1).getD t false) ((Q 2).getD t false)⟩) L

@[simp] theorem orcOf_length (L : Nat) : (orcOf lat su stl d Q L).length = L := timeline_length _ _

theorem orcOf_getD {L t : Nat} (ht : t < L) :
    (orcOf lat su stl d Q L).getD t default =
      ⟨bv3 (decide ((Q 0).getD (t + stl) false = (delayed lat d t).getLsbD 0))
           (decide ((Q 1).getD (t + stl) false = (delayed lat d t).getLsbD 1))
           (decide ((Q 2).getD (t + stl) false = (delayed lat d t).getLsbD 2)),
       bv3 ((Q 0).getD t false) ((Q 1).getD t false) ((Q 2).getD t false)⟩ :=
  timeline_getD _ ht _

/-- **Three settling bits are a metastable synchroniser stage.** -/
theorem settle_orc {v : List (BitVec 3)}
    (hlen : v.length ≤ min clk.length (d.length + lat))
    (hQlen : ∀ i, i < 3 → v.length ≤ (Q i).length)
    (hbit : ∀ i, i < 3 →
      SettleOut kq su stl clk (fun u => (delayed lat d u).getLsbD i) (d.length + lat) (Q i))
    (hpack : ∀ t, t < v.length →
      v.getD t 0#3 = bv3 ((Q 0).getD t false) ((Q 1).getD t false) ((Q 2).getD t false)) :
    v = syncOut lat su stl clk d (orcOf lat su stl d Q v.length) := by
  refine settle_orc_of (by rw [orcOf_length]) hlen hQlen hbit hpack
    (fun t ht => by rw [orcOf_getD ht]) (fun t ht i hi => ?_) (orcOf_length _)
  rw [orcOf_getD ht]
  rcases (by lia : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    simp only [bv3_getLsbD_zero, bv3_getLsbD_one, bv3_getLsbD_two]

/-- The same, as the statement that the oracle *exists*: the bus-level nondeterminism of
`syncReg` is exhausted by three settling bits. -/
theorem settle_exists_orc {v : List (BitVec 3)}
    (hlen : v.length ≤ min clk.length (d.length + lat))
    (hQlen : ∀ i, i < 3 → v.length ≤ (Q i).length)
    (hbit : ∀ i, i < 3 →
      SettleOut kq su stl clk (fun u => (delayed lat d u).getLsbD i) (d.length + lat) (Q i))
    (hpack : ∀ t, t < v.length →
      v.getD t 0#3 = bv3 ((Q 0).getD t false) ((Q 1).getD t false) ((Q 2).getD t false)) :
    ∃ orc : List (Orc 2), orc.length = v.length ∧ v = syncOut lat su stl clk d orc :=
  ⟨orcOf lat su stl d Q v.length, orcOf_length _, settle_orc hlen hQlen hbit hpack⟩

/-! ### The stage as three flip-flops

`settle_orc` is about three bit streams; these are the three the netlist actually produces.  The
stage's data is the other domain's Gray pointer as it arrives on a wire of latency `lat`. -/

/-- The other domain's bus as it arrives on the wire. -/
def wireOf (lat : Nat) (d : List (BitVec 3)) : List (BitVec 3) :=
  timeline (delayed lat d) (d.length + lat)

@[simp] theorem wireOf_length (lat : Nat) (d : List (BitVec 3)) :
    (wireOf lat d).length = d.length + lat := timeline_length _ _

/-- The wire only grows: what it has already carried it keeps carrying. -/
theorem wireOf_mono {lat : Nat} {d d' : List (BitVec 3)} (h : d <+: d') :
    wireOf lat d <+: wireOf lat d' :=
  timeline_mono (by have := h.length_le; omega) (fun _ ht => delayed_congr h ht)

/-- The wire shows the delayed bus at every instant: inside its horizon by construction, and
beyond it both are `0`. -/
theorem wireOf_getD (lat : Nat) (d : List (BitVec 3)) (u : Nat) :
    (wireOf lat d).getD u 0#3 = delayed lat d u := by
  by_cases h : u < d.length + lat
  · exact timeline_getD _ h _
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wireOf_length]; omega)]
    unfold delayed
    rw [if_neg (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]

theorem wireOf_bit (lat : Nat) (d : List (BitVec 3)) (i u : Nat) :
    (bitsOf i (wireOf lat d)).getD u false = (delayed lat d u).getLsbD i := by
  rw [bitsOf_getD_all, wireOf_getD]

/-- **The factored assumption.**  Three flip-flops sharing a clock and a clear, each assumed
only to *settle* --- `SettleOut`, one clause about one bit --- are a metastable synchroniser
stage in the sense of `Timed.syncReg`.  The oracle is not assumed, it is computed.

`v` is a prefix of what the register reports because `syncReg` reports one instant less than a
register does: `syncLen` has no `+ 1`. -/
theorem stage_settles {lat su stl kq : Nat} {clk crn : List Bool} {d : List (BitVec 3)}
    {v : List (BitVec 3)}
    (hbit : ∀ i, i < 3 → SettleOut kq su stl clk (fun u => (delayed lat d u).getLsbD i)
      (d.length + lat) (dffOut clk (bitsOf i (wireOf lat d)) crn))
    (hv : v <+: busOut clk (wireOf lat d) crn)
    (hlen : v.length ≤ min clk.length (d.length + lat)) :
    ∃ orc : List (Orc 2), orc.length = v.length ∧ v = syncOut lat su stl clk d orc := by
  have hvl := hv.length_le
  rw [busOut_length] at hvl
  refine settle_exists_orc (Q := fun i => dffOut clk (bitsOf i (wireOf lat d)) crn)
    hlen (fun i _ => ?_) hbit (fun t ht => ?_)
  · rw [dffOut_length, dffLen_bits]
    omega
  · rw [hv.getD_eq_left ht, busOut_getD (by omega)]

/-- ... and the settling clause is a *theorem* for our netlist wherever its data is stable over
the aperture (`Dff.dffOut_settleOut`).  So the assumption is exactly the failure of `haperture`,
and only for the first synchroniser stage: everywhere else `TimedProof.edge_value` discharges it
from the clock period. -/
theorem stage_settles_of_aperture {lat R : Nat} {clk crn : List Bool} {d : List (BitVec 3)}
    {v : List (BitVec 3)} (hR : 2 ≤ R)
    (hclear : ClearOK R crn (busLen clk (wireOf lat d) crn))
    (hreset : ResetOK (R + 3) clk (busLen clk (wireOf lat d) crn))
    (hpulse : PulseOK 3 clk (busLen clk (wireOf lat d) crn))
    (haperture : ∀ i, i < 3 → ∀ e, e < busLen clk (wireOf lat d) crn → riseAt clk e = true →
      StableOn (fun u => (delayed lat d u).getLsbD i) (d.length + lat) (e - 1 - 1) e)
    (hv : v <+: busOut clk (wireOf lat d) crn)
    (hlen : v.length ≤ min clk.length (d.length + lat)) :
    ∃ orc : List (Orc 2), orc.length = v.length ∧ v = syncOut lat 1 4 clk d orc := by
  refine stage_settles (kq := 4) (fun i hi => ?_) hv hlen
  have hd := dffOut_settleOut (d := bitsOf i (wireOf lat d)) (R := R) hR
    (by rwa [dffLen_bits]) (by rwa [dffLen_bits]) (by rwa [dffLen_bits])
    (fun e he hre => by
      rw [dffLen_bits] at he
      refine ⟨by rw [bitsOf_length, wireOf_length]; exact (haperture i hi e he hre).1, fun u h1 h2 => ?_⟩
      simp only [wireOf_bit]
      exact (haperture i hi e he hre).2 u h1 h2)
  exact hd.mono List.prefix_rfl (fun u _ => wireOf_bit lat d i u)
    (by rw [bitsOf_length, wireOf_length])

end Graphiti.AsyncFifo.SyncSettle
