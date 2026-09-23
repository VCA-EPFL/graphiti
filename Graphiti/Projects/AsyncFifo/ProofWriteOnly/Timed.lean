/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Filtered
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncOutMono
import Graphiti.Projects.AsyncFifo.components.level6.WriteBank
import Graphiti.Projects.AsyncFifo.components.level6.ReadBank
import Graphiti.Projects.AsyncFifo.components.level4.WriteNext
import Graphiti.Projects.AsyncFifo.components.level4.ReadNext
import Graphiti.Projects.AsyncFifo.components.level5.SyncStage
import Graphiti.Projects.AsyncFifo.components.level4.ReadPort

/-!
# Timed contracts: the lemmas

The monotonicity and congruence lemmas of the contracts in `components/level3/Contracts.lean`,
the unguarded contracts (`RegOut`, `BusRegOut`, `MemOut`) that only the proofs use, the two
timed clock-domain modules `wdomTimed` / `rdomTimed`, and the graphs that carry the timed
implementations.  Nothing here is named by the statement of the main theorem.
-/

namespace Graphiti.AsyncFifo.Timed

open Graphiti.AsyncFifo.Contracts


/-- Output relation of an edge-triggered register with clk-to-q window `kq`, setup `su` and
initial value `init`. -/
def RegOut {β : Type} [Inhabited β] (kq su : Nat) (init : β) (clk : List Bool) (d : Nat → β) (dlen : Nat)
    (q : List β) : Prop :=
  q.length ≤ min clk.length dlen + 1 ∧ ∀ t, t < q.length → RegAt kq su init clk d dlen q t

/-- A register whose output crosses into another clock domain: additionally, inside the
clk-to-q window every bit is the new bit or the bit shown at the edge. -/
def BusRegOut {w : Nat} (kq su : Nat) (clk : List Bool) (d : Nat → BitVec w) (dlen : Nat)
    (q : List (BitVec w)) : Prop :=
  RegOut kq su 0#w clk d dlen q ∧ ∀ t, t < q.length → BusWinAt kq su clk d dlen q t

def MemOut {ι α : Type} [DecidableEq ι] [Inhabited α] (kq su : Nat) (clk : List Bool) (we : Nat → Bool)
    (addr : Nat → ι) (data : Nat → α) (dlen : Nat) (mem : List (ι → α)) : Prop :=
  mem.length ≤ min clk.length dlen + 1 ∧
  ∀ t, t < mem.length → MemAt kq su clk we addr data dlen mem t

end Graphiti.AsyncFifo.Timed

namespace Graphiti.AsyncFifo.Contracts

open Graphiti.AsyncFifo.Timed

/-! ### Monotonicity of the contracts in the block's inputs

A contract established when the block held shorter input streams still holds for longer
ones: every clause only looks at instants before the one it constrains. -/

theorem StableOn.mono {κ : Type} {x x' : Nat → κ} {len len' a b : Nat} (hl : len ≤ len')
    (hx : ∀ u, u < len → x u = x' u) (h : StableOn x len a b) : StableOn x' len' a b := by
  obtain ⟨hb, h⟩ := h
  refine ⟨by lia, fun u hu1 hu2 => ?_⟩
  rw [← hx u (by lia), ← hx b hb]; exact h u hu1 hu2

theorem StableOn.of_mono {κ : Type} {x x' : Nat → κ} {len len' a b : Nat} (hb : b < len)
    (hx : ∀ u, u < len → x u = x' u) (h : StableOn x' len' a b) : StableOn x len a b := by
  obtain ⟨_, h⟩ := h
  refine ⟨hb, fun u hu1 hu2 => ?_⟩
  rw [hx u (by lia), hx b hb]; exact h u hu1 hu2

theorem ReadOut.mono {α : Type} [Inhabited α] {ι : Type} {dmin dmax : Nat} {addr addr' : Nat → ι}
    {mem mem' : Nat → ι → α} {len len' : Nat} {v : List α} (hl : len ≤ len')
    (ha : ∀ u, u < len → addr u = addr' u) (hm : ∀ u, u < len → mem u = mem' u)
    (h : ReadOut dmin dmax addr mem len v) : ReadOut dmin dmax addr' mem' len' v := by
  obtain ⟨hlen, h⟩ := h
  refine ⟨by omega, fun t hdt ht hs hw => ?_⟩
  have hb : t - dmin < len := by omega
  have hs' : StableOn addr len (t - dmax) (t - dmin) := StableOn.of_mono hb ha hs
  rw [h t hdt ht hs' (fun u hu1 hu2 => by
      rw [hm u (by omega), hm (t - dmin) hb, ha (t - dmin) hb]; exact hw u hu1 hu2),
    hm (t - dmin) hb, ha (t - dmin) hb]

theorem CombOut.mono {κ ο : Type} [Inhabited ο] {dep dep' : Nat → κ} {g : κ → ο} {len len' dmin dmax : Nat}
    {v : List ο} (hl : len ≤ len') (hdep : ∀ u, u < len → dep u = dep' u)
    (h : CombOut dep g len dmin dmax v) : CombOut dep' g len' dmin dmax v := by
  obtain ⟨hlen, h⟩ := h
  refine ⟨by lia, fun t hdt ht hs => ?_⟩
  rw [h t hdt ht (hs.of_mono (by lia) hdep), hdep (t - dmax) (by lia)]

theorem _root_.Graphiti.AsyncFifo.Timed.RegOut.mono {β : Type} [Inhabited β] {kq su : Nat} {init : β} {clk clk' : List Bool} {d d' : Nat → β}
    {dlen dlen' : Nat} {q : List β} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (hl : dlen ≤ dlen')
    (h : RegOut kq su init clk d dlen q) : RegOut kq su init clk' d' dlen' q := by
  obtain ⟨hlen, h⟩ := h
  have hcl := hc.length_le
  refine ⟨by omega, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht
  have htc : t ≤ clk.length := by omega
  have htd : t ≤ dlen := by omega
  refine ⟨fun hn => h1 ((NoEdge_congr hc htc).mpr hn), fun e he hs hk => ?_⟩
  have he' := (LastEdge_congr hc htc).mpr he
  have he1 := he.1
  rw [h2 e he' (hs.of_mono (by lia) hd) hk, hd e (by lia)]

theorem _root_.Graphiti.AsyncFifo.Timed.BusRegOut.mono {w : Nat} {kq su : Nat} {clk clk' : List Bool} {d d' : Nat → BitVec w}
    {dlen dlen' : Nat} {q : List (BitVec w)} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (hl : dlen ≤ dlen')
    (h : BusRegOut kq su clk d dlen q) : BusRegOut kq su clk' d' dlen' q := by
  obtain ⟨hreg, hwin⟩ := h
  have hlen := hreg.1
  have hcl := hc.length_le
  refine ⟨hreg.mono hc hd hl, fun t ht hclean e he hk i => ?_⟩
  have htc : t ≤ clk.length := by omega
  have he' := (LastEdge_congr hc htc).mpr he
  have he1 := he.1
  rw [← hd e (by omega)]
  refine hwin t ht (fun e' he2 hr' => ?_) e he' hk i
  exact (hclean e' he2 (by rw [← riseAt_prefix hc (by omega)]; exact hr')).of_mono (by omega) hd

theorem WriteEdge.congr {ι α : Type} {a : ι} {clk clk' : List Bool} {we we' : Nat → Bool} {addr addr' : Nat → ι}
    {data data' : Nat → α} {dlen dlen' su e : Nat} (hc : clk <+: clk') (hl : dlen ≤ dlen')
    (hwe : ∀ u, u < dlen → we u = we' u) (haddr : ∀ u, u < dlen → addr u = addr' u)
    (hdata : ∀ u, u < dlen → data u = data' u) (he : e < dlen) (hec : e < clk.length) :
    WriteEdge a clk we addr data dlen su e ↔ WriteEdge a clk' we' addr' data' dlen' su e := by
  unfold WriteEdge
  rw [riseAt_prefix hc hec, hwe e he, haddr e he]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2.mono hl hwe, h3.mono hl haddr, h4.mono hl hdata, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2.of_mono he hwe, h3.of_mono he haddr, h4.of_mono he hdata, h5, h6⟩

theorem CleanWrites.of_mono {ι α : Type} {clk clk' : List Bool} {we we' : Nat → Bool} {addr addr' : Nat → ι}
    {data data' : Nat → α} {dlen dlen' su t : Nat} (hc : clk <+: clk') (hwe : ∀ u, u < dlen → we u = we' u)
    (haddr : ∀ u, u < dlen → addr u = addr' u) (hdata : ∀ u, u < dlen → data u = data' u)
    (ht : t ≤ dlen) (htc : t ≤ clk.length) (h : CleanWrites clk' we' addr' data' dlen' su t) :
    CleanWrites clk we addr data dlen su t := by
  intro e he hre
  have hre' : riseAt clk' e = true := by rw [← riseAt_prefix hc (by lia)]; exact hre
  obtain ⟨h1, h2⟩ := h e he hre'
  refine ⟨h1.of_mono (by lia) hwe, fun hw => ?_⟩
  obtain ⟨h3, h4⟩ := h2 (by rw [← hwe e (by lia)]; exact hw)
  exact ⟨h3.of_mono (by lia) haddr, h4.of_mono (by lia) hdata⟩

theorem GateOK.mono {P pw Rr Rc : Nat} {clk crn : List Bool} {t t' : Nat}
    (h : GateOK P pw Rr Rc clk crn t') (ht : t ≤ t') : GateOK P pw Rr Rc clk crn t :=
  ⟨h.period.mono ht, h.pulse.mono ht, h.reset.mono ht, h.clear.mono ht⟩

/-- A guard read off longer streams still holds of the prefixes the block stores. -/
theorem GateOK.congr {P pw Rr Rc : Nat} {clk clk' crn crn' : List Bool} {t : Nat}
    (hc : clk <+: clk') (hr : crn <+: crn') (ht : t ≤ clk.length) (ht' : t ≤ crn.length)
    (h : GateOK P pw Rr Rc clk' crn' t) : GateOK P pw Rr Rc clk crn t :=
  ⟨ClockOK.congr hc ht h.period, PulseOK.congr hc ht h.pulse, ResetOK.congr hc ht h.reset,
   ClearOK.congr hr ht' h.clear⟩

theorem _root_.Graphiti.AsyncFifo.Timed.MemOut.mono {ι α : Type} [DecidableEq ι] [Inhabited α] {kq su : Nat} {clk clk' : List Bool}
    {we we' : Nat → Bool} {addr addr' : Nat → ι} {data data' : Nat → α} {dlen dlen' : Nat} {mem : List (ι → α)}
    (hc : clk <+: clk') (hl : dlen ≤ dlen')
    (hwe : ∀ u, u < dlen → we u = we' u) (haddr : ∀ u, u < dlen → addr u = addr' u)
    (hdata : ∀ u, u < dlen → data u = data' u)
    (h : MemOut kq su clk we addr data dlen mem) : MemOut kq su clk' we' addr' data' dlen' mem := by
  obtain ⟨hlen, h⟩ := h
  have hcl := hc.length_le
  refine ⟨by omega, fun t ht hcw a => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht (hcw.of_mono hc hwe haddr hdata (by omega) (by omega)) a
  have hW : ∀ e, e < t → (WriteEdge a clk we addr data dlen su e ↔ WriteEdge a clk' we' addr' data' dlen' su e) :=
    fun e he => WriteEdge.congr hc hl hwe haddr hdata (by omega) (by omega)
  refine ⟨fun hn => h1 (fun e he hw => hn e he ((hW e he).mp hw)), fun e he hw hlast hk => ?_⟩
  rw [h2 e he ((hW e he).mpr hw) (fun e' h1 h2 hw' => hlast e' h1 h2 ((hW e' h2).mp hw')) hk, hdata e (by omega)]

/-! ### Monotonicity of the per-instant clauses and of the guarded contracts -/

theorem RegAt.mono {β : Type} [Inhabited β] {kq su : Nat} {init : β} {clk clk' : List Bool} {d d' : Nat → β}
    {dlen dlen' t : Nat} {q : List β} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u)
    (hl : dlen ≤ dlen') (htc : t ≤ clk.length) (htd : t ≤ dlen)
    (h : RegAt kq su init clk d dlen q t) : RegAt kq su init clk' d' dlen' q t := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hn => h1 ((NoEdge_congr hc htc).mpr hn), fun e he hs hk => ?_⟩
  have he' := (LastEdge_congr hc htc).mpr he
  have he1 := he.1
  rw [h2 e he' (hs.of_mono (by lia) hd) hk, hd e (by lia)]

theorem CleanEdges.of_mono {β : Type} {clk clk' : List Bool} {d d' : Nat → β} {dlen dlen' su t : Nat}
    (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (htc : t ≤ clk.length) (htd : t ≤ dlen)
    (h : CleanEdges clk' d' dlen' su t) : CleanEdges clk d dlen su t := by
  intro e he hr
  exact (h e he (by rw [← riseAt_prefix hc (by omega)]; exact hr)).of_mono (by omega) hd

theorem BusWinAt.mono {w : Nat} {kq su : Nat} {clk clk' : List Bool} {d d' : Nat → BitVec w}
    {dlen dlen' t : Nat} {q : List (BitVec w)} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u)
    (hl : dlen ≤ dlen') (htc : t ≤ clk.length) (htd : t ≤ dlen)
    (h : BusWinAt kq su clk d dlen q t) : BusWinAt kq su clk' d' dlen' q t := by
  intro hclean e he hk i
  have he' := (LastEdge_congr hc htc).mpr he
  have he1 := he.1
  rw [← hd e (by lia)]
  exact h (hclean.of_mono hc hd htc htd) e he' hk i

theorem MemAt.mono {ι α : Type} [DecidableEq ι] [Inhabited α] {kq su : Nat} {clk clk' : List Bool}
    {we we' : Nat → Bool} {addr addr' : Nat → ι} {data data' : Nat → α} {dlen dlen' t : Nat}
    {mem : List (ι → α)} (hc : clk <+: clk') (hl : dlen ≤ dlen')
    (hwe : ∀ u, u < dlen → we u = we' u) (haddr : ∀ u, u < dlen → addr u = addr' u)
    (hdata : ∀ u, u < dlen → data u = data' u) (htc : t ≤ clk.length) (htd : t ≤ dlen)
    (h : MemAt kq su clk we addr data dlen mem t) : MemAt kq su clk' we' addr' data' dlen' mem t := by
  intro hcw a
  obtain ⟨h1, h2⟩ := h (hcw.of_mono hc hwe haddr hdata (by omega) (by omega)) a
  have hW : ∀ e, e < t → (WriteEdge a clk we addr data dlen su e ↔ WriteEdge a clk' we' addr' data' dlen' su e) :=
    fun e he => WriteEdge.congr hc hl hwe haddr hdata (by omega) (by omega)
  refine ⟨fun hn => h1 (fun e he hw => hn e he ((hW e he).mp hw)), fun e he hw hlast hk => ?_⟩
  rw [h2 e he ((hW e he).mpr hw) (fun e' k1 k2 hw' => hlast e' k1 k2 ((hW e' k2).mp hw')) hk, hdata e (by omega)]

/-! A per-instant clause looks at the block's report only at the instants it constrains, so two
reports that agree there satisfy it together.  This is what lets a contract proved of the
stream a block computes be read off any prefix of it. -/

theorem RegAt.congr_out {β : Type} [Inhabited β] {kq su : Nat} {init : β} {clk : List Bool}
    {dd : Nat → β} {dlen t : Nat} {q q' : List β} (h : q.getD t default = q'.getD t default)
    (hq : RegAt kq su init clk dd dlen q t) : RegAt kq su init clk dd dlen q' t :=
  ⟨fun hn => by rw [← h]; exact hq.1 hn, fun e he hs hk => by rw [← h]; exact hq.2 e he hs hk⟩

theorem BusWinAt.congr_out {w : Nat} {kq su : Nat} {clk : List Bool} {dd : Nat → BitVec w}
    {dlen t : Nat} {q q' : List (BitVec w)} (h : ∀ u, u ≤ t → q.getD u 0#w = q'.getD u 0#w)
    (hq : BusWinAt kq su clk dd dlen q t) : BusWinAt kq su clk dd dlen q' t := by
  intro hclean e he hk i
  have he1 := he.1
  rw [← h t (Nat.le_refl t), ← h e (by omega)]
  exact hq hclean e he hk i

theorem MemAt.congr_out {ι α : Type} [DecidableEq ι] [Inhabited α] {kq su : Nat} {clk : List Bool}
    {we : Nat → Bool} {addr : Nat → ι} {data : Nat → α} {dlen t : Nat} {mem mem' : List (ι → α)}
    (h : mem.getD t (fun _ => default) = mem'.getD t (fun _ => default))
    (hq : MemAt kq su clk we addr data dlen mem t) :
    MemAt kq su clk we addr data dlen mem' t := by
  intro hcw a
  obtain ⟨h1, h2⟩ := hq hcw a
  rw [← h]
  exact ⟨h1, h2⟩

/-! A longer setup window is a stronger hypothesis on the data, so a contract proved with a
short one implies the same contract with a long one.  That is how blocks with different setup
windows --- the registers' one instant, the register file's eight --- meet in one bank. -/

theorem RegAt.weaken_su {β : Type} [Inhabited β] {kq su su' : Nat} {init : β} {clk : List Bool}
    {dd : Nat → β} {dlen t : Nat} {q : List β} (h : su ≤ su')
    (hq : RegAt kq su init clk dd dlen q t) : RegAt kq su' init clk dd dlen q t :=
  ⟨hq.1, fun e he hs hk => hq.2 e he ⟨hs.1, fun u hu1 hu2 => hs.2 u (by omega) hu2⟩ hk⟩

theorem BusWinAt.weaken_su {w : Nat} {kq su su' : Nat} {clk : List Bool} {dd : Nat → BitVec w}
    {dlen t : Nat} {q : List (BitVec w)} (h : su ≤ su')
    (hq : BusWinAt kq su clk dd dlen q t) : BusWinAt kq su' clk dd dlen q t :=
  fun hclean e he hk i =>
    hq (fun e' he' hr' => (fun hs => ⟨hs.1, fun u hu1 hu2 => hs.2 u (by omega) hu2⟩)
      (hclean e' he' hr')) e he hk i

theorem RegOutG.weaken_su {β : Type} [Inhabited β] {kq su su' : Nat} {init : β} {G : Nat → Prop}
    {clk : List Bool} {dd : Nat → β} {dlen len : Nat} {q : List β} (h : su ≤ su')
    (hq : RegOutG kq su init G clk dd dlen len q) : RegOutG kq su' init G clk dd dlen len q :=
  ⟨hq.1, fun t ht hg => (hq.2 t ht hg).weaken_su h⟩

theorem BusRegOutG.weaken_su {w : Nat} {kq su su' : Nat} {G : Nat → Prop} {clk : List Bool}
    {dd : Nat → BitVec w} {dlen len : Nat} {q : List (BitVec w)} (h : su ≤ su')
    (hq : BusRegOutG kq su G clk dd dlen len q) : BusRegOutG kq su' G clk dd dlen len q :=
  ⟨hq.1.weaken_su h, fun t ht hg => (hq.2 t ht hg).weaken_su h⟩

theorem RegOutG.mono {β : Type} [Inhabited β] {kq su : Nat} {init : β} {G G' : Nat → Prop}
    {clk clk' : List Bool} {d d' : Nat → β} {dlen dlen' len len' : Nat} {q : List β}
    (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (hl : dlen ≤ dlen')
    (hlc : len ≤ clk.length) (hld : len ≤ dlen) (hlen : len ≤ len')
    (hG : ∀ t, t < q.length → G' t → G t)
    (h : RegOutG kq su init G clk d dlen len q) : RegOutG kq su init G' clk' d' dlen' len' q := by
  obtain ⟨hq, h⟩ := h
  exact ⟨by omega, fun t ht hg =>
    (h t ht (hG t ht hg)).mono hc hd hl (by omega) (by omega)⟩

theorem BusRegOutG.mono {w : Nat} {kq su : Nat} {G G' : Nat → Prop} {clk clk' : List Bool}
    {d d' : Nat → BitVec w} {dlen dlen' len len' : Nat} {q : List (BitVec w)}
    (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (hl : dlen ≤ dlen')
    (hlc : len ≤ clk.length) (hld : len ≤ dlen) (hlen : len ≤ len')
    (hG : ∀ t, t < q.length → G' t → G t)
    (h : BusRegOutG kq su G clk d dlen len q) : BusRegOutG kq su G' clk' d' dlen' len' q := by
  obtain ⟨hreg, hwin⟩ := h
  have hq := hreg.1
  exact ⟨hreg.mono hc hd hl hlc hld hlen hG, fun t ht hg =>
    (hwin t ht (hG t ht hg)).mono hc hd hl (by omega) (by omega)⟩

theorem MemOutG.mono {ι α : Type} [DecidableEq ι] [Inhabited α] {kq su : Nat} {G G' : Nat → Prop}
    {clk clk' : List Bool} {we we' : Nat → Bool} {addr addr' : Nat → ι} {data data' : Nat → α}
    {dlen dlen' len len' : Nat} {mem : List (ι → α)}
    (hc : clk <+: clk') (hl : dlen ≤ dlen')
    (hwe : ∀ u, u < dlen → we u = we' u) (haddr : ∀ u, u < dlen → addr u = addr' u)
    (hdata : ∀ u, u < dlen → data u = data' u)
    (hlc : len ≤ clk.length) (hld : len ≤ dlen) (hlen : len ≤ len')
    (hG : ∀ t, t < mem.length → G' t → G t)
    (h : MemOutG kq su G clk we addr data dlen len mem) :
    MemOutG kq su G' clk' we' addr' data' dlen' len' mem := by
  obtain ⟨hq, h⟩ := h
  exact ⟨by omega, fun t ht hg =>
    (h t ht (hG t ht hg)).mono hc hl hwe haddr hdata (by omega) (by omega)⟩

end Graphiti.AsyncFifo.Contracts

namespace Graphiti.AsyncFifo.Timed

open Graphiti.AsyncFifo.Contracts

/-! ### The settling contract: the one assumption -/

/-- **What a flip-flop does when its data does *not* meet the setup window.**  This is the one
thing in the development that is assumed rather than derived, and it is deliberately one clause
about one bit.

The first half is `RegOut` --- exactly what a netlist of gates gives, and `Dff.dffOut_regOut`
proves it.  The second half is the assumption: from `stl` instants after an edge until the next
one the output is *a value* --- it does not move, and it is one of the two the data showed at
the ends of the aperture.  Nothing at all is said about the `stl` instants themselves, so a
stage still inside its metastable window may report anything.

`Dff.dffOut_settleOut` proves the netlist satisfies this whenever its data *is* stable over the
aperture, with `stl = kq = 4`.  So what is assumed is exactly the failure of that hypothesis,
for the flip-flops of the first synchroniser stage and nowhere else: everywhere else the setup
window is discharged from the clock period (`TimedProof.edge_value`) and this contract is a
theorem.  `Metastability.lean` says why it cannot be a theorem here. -/
def SettleOut (kq su stl : Nat) (clk : List Bool) (d : Nat → Bool) (dlen : Nat) (q : List Bool) : Prop :=
  RegOut kq su false clk d dlen q ∧
  ∀ t, t < q.length → ∀ e, LastEdge clk e t → e + stl ≤ t →
    q.getD t false = q.getD (e + stl) false ∧
      (q.getD (e + stl) false = d e ∨ q.getD (e + stl) false = d (e - su - 1))

theorem SettleOut.mono {kq su stl : Nat} {clk clk' : List Bool} {d d' : Nat → Bool}
    {dlen dlen' : Nat} {q : List Bool} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u)
    (hl : dlen ≤ dlen') (h : SettleOut kq su stl clk d dlen q) :
    SettleOut kq su stl clk' d' dlen' q := by
  obtain ⟨hreg, hset⟩ := h
  have hlen := hreg.1
  have hcl := hc.length_le
  refine ⟨hreg.mono hc hd hl, fun t ht e hle hk => ?_⟩
  have he1 := hle.1
  obtain ⟨h1, h2⟩ := hset t ht e ((LastEdge_congr hc (by omega)).mpr hle) hk
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl (by rw [h2, hd e (by omega)])
  · exact Or.inr (by rw [h2, hd (e - su - 1) (by omega)])

/-- The block a settling flip-flop is: the ports of the netlist, and `SettleOut` as its
contract.  It stores what it has reported so that its reports only grow. -/
structure SettleSt where
  clk : List Bool
  d : List Bool
  crn : List Bool
  q : List Bool

@[drcomponents]
def settlingDff (kq su stl : Nat) : StringModule SettleSt :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.clk ⊏ v ∧ s' = { s with clk := v }⟩)
              , (↑"d", ⟨List Bool, fun s v s' => s.d ⊏ v ∧ s' = { s with d := v }⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.crn ⊏ v ∧ s' = { s with crn := v }⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s.q <+: v ∧
                    SettleOut kq su stl s.clk (fun u => s.d.getD u false) s.d.length v ∧
                    s' = { s with q := v }⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], []⟩ }


section WriteBlocks

variable (α : Type) [Inhabited α]
variable (n lat kq su stl dmin dmax P pw Rr Rc : Nat)



@[drenv] theorem wenv_clkF : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "clkF" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem wenv_regs : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "WriteBank" = .some ⟨_, WriteBank.bankSpec α (n := n) kq su P pw Rr Rc⟩ := rfl
@[drenv] theorem wenv_clrS : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "clearSrc" = .some ⟨_, clearSrc Rc⟩ := rfl
@[drenv] theorem wenv_next : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "WriteNext" = .some ⟨_, WriteNext.nextSpec α (n := n) dmin dmax⟩ := rfl
@[drenv] theorem wenv_sync : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "SyncStage" = .some ⟨_, SyncStage.syncSpec (n := n) lat su stl⟩ := rfl

seal wenv in
def_module wdomTimedT' : Type :=
  [T| wdomLowered, (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

/-- The state of the timed write domain, as produced by lowering the graph: the clear source,
the synchroniser (`clk`, `d`, `orc`), the clock fork, the next-state block and the register
bank. -/
abbrev wdomTimedT : Type :=
  List Bool × (List Bool × List (BitVec (n+1)) × List (Orc n) × List (BitVec (n+1))) ×
    List Bool × WriteNext.NextSt α n × WriteBank.RegSt α n

omit [Inhabited α] in
/-- A compiled check, not a step of any proof: the type `def_module` reduces the graph to
is the one written by hand above, so the hand-written `abbrev` — which every statement below
names — cannot drift from the graph. -/
theorem wdomTimedT_eq : wdomTimedT' α n = wdomTimedT α n := rfl

seal wenv in
def_module wdomTimed : StringModule (wdomTimedT α n) :=
  [e| wdomLowered, (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? ]

end WriteBlocks

section ReadBlocks

variable (α : Type) [Inhabited α]
variable (n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc : Nat)



@[drenv] theorem renv_clkF : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "clkF" =
  .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem renv_regs : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "ReadBank" =
  .some ⟨_, ReadBank.bankSpec (n := n) kq su P pw Rr Rc⟩ := rfl
@[drenv] theorem renv_clrS : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "clearSrc" =
  .some ⟨_, clearSrc Rc⟩ := rfl
@[drenv] theorem renv_next : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "ReadNext" =
  .some ⟨_, ReadNext.nextSpec (n := n) dmin dmax⟩ := rfl
@[drenv] theorem renv_sync : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "SyncStage" =
  .some ⟨_, SyncStage.syncSpec (n := n) lat su stl⟩ := rfl
@[drenv] theorem renv_stF : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "stF" =
  .some ⟨_, fork2 (RSt n)⟩ := rfl
@[drenv] theorem renv_rdat : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "ReadPort" =
  .some ⟨_, ReadPort.readSpec α (n := n) ddmin ddmax⟩ := rfl

seal renv in
def_module rdomTimedT' : Type :=
  [T| rdomLowered, (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

/-- The state of the timed read domain, as produced by lowering the graph: the clear source,
the state fork, the synchroniser, the clock fork, the next-state block, the read port and the
register bank. -/
abbrev rdomTimedT : Type :=
  List Bool × List (RSt n) × (List Bool × List (BitVec (n+1)) × List (Orc n) × List (BitVec (n+1))) ×
    List Bool × ReadNext.RNextSt n × ReadPort.RDataSt α n × ReadBank.RRegSt n

omit [Inhabited α] in
/-- A compiled check, not a step of any proof: the type `def_module` reduces the graph to
is the one written by hand above, so the hand-written `abbrev` — which every statement below
names — cannot drift from the graph. -/
theorem rdomTimedT_eq : rdomTimedT' α n = rdomTimedT α n := rfl

seal renv in
def_module rdomTimed : StringModule (rdomTimedT α n) :=
  [e| rdomLowered, (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? ]

end ReadBlocks

end Graphiti.AsyncFifo.Timed
