/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.TimedProofR
import Graphiti.Projects.AsyncFifo.Modules

/-!
# The timed read domain refines the filtered one

`rdomTimed_refines`, the read domain's counterpart of `TimedRefinement.wdomTimed_refines`.  The
simulation relation says the specification's streams are the domain's, that each block's stored
wires are prefixes of what drives them, and that the three outputs carry the contracts
`TimedProofR.lean` turns into the filtered relations.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Timed

open Graphiti.AsyncFifo

variable {α : Type} [Inhabited α]
  {n lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc : Nat}

instance : MatchInterface (rdomTimed α n lat kq su stl dmin dmax ddmin ddmax Pg pwg Rg Rc)
    (readDomainF α n lat stl su kq rdly P S R pw) := by
  dsimp [rdomTimed, readDomainF]
  solve_match_interface

/-! ### Monotonicity in the bank's inputs -/

theorem rnextLen_mono {s s' : RNextSt n} (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc)
    (h3 : s.q1 <+: s'.q1) : rnextLen s ≤ rnextLen s' := by
  have := h1.length_le; have := h2.length_le; have := h3.length_le
  unfold rnextLen; omega

theorem rnextDep_congr {s s' : RNextSt n} (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc)
    (h3 : s.q1 <+: s'.q1) {u : Nat} (hu : u < rnextLen s) : rnextDep s u = rnextDep s' u := by
  unfold rnextLen at hu
  simp only [Nat.lt_min] at hu
  unfold rnextDep
  rw [h1.getD_eq_left (by omega), h2.getD_eq_left (by omega), h3.getD_eq_left (by omega)]

theorem CombOut.rmono_next {s s' : RNextSt n} (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc)
    (h3 : s.q1 <+: s'.q1) {v : List (RNext n)}
    (h : CombOut (rnextDep s) rnextFun (rnextLen s) dmin dmax v) :
    CombOut (rnextDep s') rnextFun (rnextLen s') dmin dmax v :=
  h.mono (rnextLen_mono h1 h2 h3) (fun u hu => rnextDep_congr h1 h2 h3 hu)

theorem RegOutG.rmono_bus {G : Nat → Prop} {rclk rclk' : List Bool} {rd rd' : List (RNext n)}
    {q : List (RSt n)} (hc : rclk <+: rclk') (hd : rd <+: rd')
    (h : RegOutG kq su default G rclk (fun u => (rd.getD u default).st) rd.length
          (min rclk.length rd.length) q) :
    RegOutG kq su default G rclk' (fun u => (rd'.getD u default).st) rd'.length
      (min rclk'.length rd'.length) q := by
  have h1 := hc.length_le; have h2 := hd.length_le
  exact h.mono hc (fun u hu => by rw [hd.getD_eq_left hu]) h2 (by omega) (by omega) (by omega)
    (fun _ _ hg => hg)

theorem BusRegOutG.rmono_bus {G : Nat → Prop} {rclk rclk' : List Bool} {rd rd' : List (RNext n)}
    {q : List (BitVec (n+1))} (hc : rclk <+: rclk') (hd : rd <+: rd')
    (h : BusRegOutG kq su G rclk (fun u => (rd.getD u default).gnext) rd.length
          (min rclk.length rd.length) q) :
    BusRegOutG kq su G rclk' (fun u => (rd'.getD u default).gnext) rd'.length
      (min rclk'.length rd'.length) q := by
  have h1 := hc.length_le; have h2 := hd.length_le
  exact h.mono hc (fun u hu => by rw [hd.getD_eq_left hu]) h2 (by omega) (by omega) (by omega)
    (fun _ _ hg => hg)

theorem RegOutG.rmono_guard {G G' : Nat → Prop} {rclk : List Bool} {rd : List (RNext n)}
    {q : List (RSt n)} (hG : ∀ t, t ≤ min rclk.length rd.length → G' t → G t)
    (h : RegOutG kq su default G rclk (fun u => (rd.getD u default).st) rd.length
          (min rclk.length rd.length) q) :
    RegOutG kq su default G' rclk (fun u => (rd.getD u default).st) rd.length
      (min rclk.length rd.length) q := by
  have hq := h.1
  exact h.mono List.prefix_rfl (fun _ _ => rfl) (Nat.le_refl _) (by omega) (by omega)
    (Nat.le_refl _) (fun t ht hg => hG t (by omega) hg)

theorem BusRegOutG.rmono_guard {G G' : Nat → Prop} {rclk : List Bool} {rd : List (RNext n)}
    {q : List (BitVec (n+1))} (hG : ∀ t, t ≤ min rclk.length rd.length → G' t → G t)
    (h : BusRegOutG kq su G rclk (fun u => (rd.getD u default).gnext) rd.length
          (min rclk.length rd.length) q) :
    BusRegOutG kq su G' rclk (fun u => (rd.getD u default).gnext) rd.length
      (min rclk.length rd.length) q := by
  have hq := h.1.1
  exact h.mono List.prefix_rfl (fun _ _ => rfl) (Nat.le_refl _) (by omega) (by omega)
    (Nat.le_refl _) (fun t ht hg => hG t (by omega) hg)

/-! ### The simulation relation -/

/-- The simulation relation, on the streams of the timed read domain: the clear, the
synchroniser (`sclk sd sorc`), the clock fork `F`, the state fork `stf`, the next-state block
(`nst ninc nq1 nd`), the read port (`mst rmem rq`) and the register bank (`rclk rd stq emq gq`). -/
structure RPsi (lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc : Nat) (crn : List Bool)
    (sclk : List Bool) (sd : List (BitVec (n+1))) (sorc : List (Orc n)) (F : List Bool)
    (stf nst : List (RSt n)) (ninc : List Bool) (nq1 : List (BitVec (n+1))) (nd : List (RNext n))
    (mst : List (RSt n)) (rmem : List (BitVec n → α)) (rq : List α)
    (rclk : List Bool) (rd : List (RNext n)) (stq : List (RSt n)) (emq : List Bool)
    (gq : List (BitVec (n+1))) (s : RStateF α n) : Prop where
  clk : F = s.clk
  inc : ninc = s.inc
  wgray : sd = s.wgray
  orc : sorc = s.orc
  mem : rmem = s.mem
  gray_q : s.gray_q = gq
  empty_q : s.empty_q = emq
  rdata_q : s.rdata_q = rq
  crn_ok : ClearOK Rc crn crn.length
  sclk_F : sclk <+: F
  rclk_F : rclk <+: F
  q1_sync : nq1 <+: syncOut lat su stl sclk sd sorc
  stf_q : stf <+: stq
  st_stf : nst <+: stf
  mst_stf : mst <+: stf
  d_link : rd <+: nd
  st_ok : RegOutG kq su default (RFilter P S R pw F ninc) rclk
    (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) stq
  d_ok : CombOut (rnextDep ⟨nst, ninc, nq1, nd⟩) rnextFun (rnextLen ⟨nst, ninc, nq1, nd⟩) dmin dmax nd
  empty_ok : ∃ q, RegOutG kq su default (RFilter P S R pw F ninc) rclk
      (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q ∧
    emq = q.map (fun st => st.empty)
  gray_ok : BusRegOutG kq su (RFilter P S R pw F ninc) rclk
    (fun u => (rd.getD u default).gnext) rd.length (min rclk.length rd.length) gq
  rdata_ok : ReadOut ddmin ddmax (fun u => (mst.getD u default).ptr.setWidth n)
    (fun u => rmem.getD u (fun _ => default)) (min mst.length rmem.length) rq

section Rel
variable {crn sclk : List Bool} {sd : List (BitVec (n+1))} {sorc : List (Orc n)} {F : List Bool}
  {stf nst : List (RSt n)} {ninc : List Bool} {nq1 : List (BitVec (n+1))} {nd : List (RNext n)}
  {mst : List (RSt n)} {rmem : List (BitVec n → α)} {rq : List α} {rclk : List Bool}
  {rd : List (RNext n)} {stq : List (RSt n)} {emq : List Bool} {gq : List (BitVec (n+1))}
  {s : RStateF α n}
  (H : RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc nq1 nd
    mst rmem rq rclk rd stq emq gq s)
include H

/-- The links the delay analysis asks for, assembled from the relation's flat fields. -/
theorem RPsi.toLinks :
    RLinks kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc ninc nst mst nq1 nd rd rmem s.mem stq :=
  { sclk_F := H.sclk_F, rclk_F := H.rclk_F, q1_sync := H.q1_sync
    st_link := H.st_stf.trans H.stf_q, mst_link := H.mst_stf.trans H.stf_q
    mem_link := H.mem ▸ List.prefix_rfl, d_link := H.d_link
    st_ok := H.st_ok, d_ok := H.d_ok }

/-- **Where the netlist's assumptions meet the domain's**, as on the write side. -/
theorem RPsi.gate_of (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) :
    ∀ t, t ≤ min (min rclk.length rd.length) crn.length →
      RFilter P S R pw F ninc t → GateOK Pg pwg Rg Rc rclk crn t := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩ := H.toLinks.lens
  intro t ht hf
  exact ⟨(ClockOK.congr H.rclk_F (by omega) hf.1).weaken hPg,
         (PulseOK.congr H.rclk_F (by omega) hf.2.2.2).weaken hpwg,
         (ResetOK.congr H.rclk_F (by omega) hf.2.2.1).weaken hRg,
         H.crn_ok.mono (by omega)⟩

theorem RPsi.reg_of (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) {v : List (RSt n)}
    (h : RegOutG kq su default (GateOK Pg pwg Rg Rc rclk crn) rclk
      (fun u => (rd.getD u default).st) rd.length (min (min rclk.length rd.length) crn.length) v) :
    RegOutG kq su default (RFilter P S R pw F ninc) rclk (fun u => (rd.getD u default).st)
      rd.length (min rclk.length rd.length) v := by
  have hq := h.1
  exact h.mono List.prefix_rfl (fun _ _ => rfl) (Nat.le_refl _) (by omega) (by omega) (by omega)
    (fun t ht hg => H.gate_of hPg hpwg hRg t (by omega) hg)

theorem RPsi.busreg_of (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) {v : List (BitVec (n+1))}
    (h : BusRegOutG kq su (GateOK Pg pwg Rg Rc rclk crn) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min (min rclk.length rd.length) crn.length) v) :
    BusRegOutG kq su (RFilter P S R pw F ninc) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min rclk.length rd.length) v := by
  have hq := h.1.1
  exact h.mono List.prefix_rfl (fun _ _ => rfl) (Nat.le_refl _) (by omega) (by omega) (by omega)
    (fun t ht hg => H.gate_of hPg hpwg hRg t (by omega) hg)

/-- The filter is read off the domain's own streams, so when they grow the guard has to be
pulled back along the growth. -/
theorem RPsi.guard_mono {F' ninc' : List Bool} (h1 : F <+: F') (h2 : ninc <+: ninc') :
    ∀ t, t ≤ min rclk.length rd.length →
      RFilter P S R pw F' ninc' t → RFilter P S R pw F ninc t := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩ := H.toLinks.lens
  exact fun t ht => RFilter_congr h1 h2 (by omega) (by omega)

/-! ### The transitions -/

-- Inputs

theorem rin_clk (v : List Bool) (h : F ⊏ v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc v stf nst ninc nq1 nd
      mst rmem rq rclk rd stq emq gq { s with clk := v } :=
  { H with
    clk := rfl
    sclk_F := H.sclk_F.trans h.isPrefix
    rclk_F := H.rclk_F.trans h.isPrefix
    st_ok := H.st_ok.rmono_guard (H.guard_mono h.isPrefix List.prefix_rfl)
    empty_ok := H.empty_ok.imp (fun q hq =>
      And.intro (hq.1.rmono_guard (H.guard_mono h.isPrefix List.prefix_rfl)) hq.2)
    gray_ok := H.gray_ok.rmono_guard (H.guard_mono h.isPrefix List.prefix_rfl) }

theorem rin_inc (v : List Bool) (h : ninc ⊏ v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst v nq1 nd
      mst rmem rq rclk rd stq emq gq { s with inc := v } :=
  { H with
    inc := rfl
    d_ok := H.d_ok.rmono_next (s := ⟨nst, ninc, nq1, nd⟩) (s' := ⟨nst, v, nq1, nd⟩)
      List.prefix_rfl h.isPrefix List.prefix_rfl
    st_ok := H.st_ok.rmono_guard (H.guard_mono List.prefix_rfl h.isPrefix)
    empty_ok := H.empty_ok.imp (fun q hq =>
      And.intro (hq.1.rmono_guard (H.guard_mono List.prefix_rfl h.isPrefix)) hq.2)
    gray_ok := H.gray_ok.rmono_guard (H.guard_mono List.prefix_rfl h.isPrefix) }

theorem rin_wgray (v : List (BitVec (n+1))) (h : sd ⊏ v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk v sorc F stf nst ninc nq1 nd
      mst rmem rq rclk rd stq emq gq { s with wgray := v } :=
  { H with
    wgray := rfl
    q1_sync := H.q1_sync.trans (syncOut_mono List.prefix_rfl h.isPrefix List.prefix_rfl) }

theorem rin_orc (v : List (Orc n)) (h : sorc ⊏ v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd v F stf nst ninc nq1 nd
      mst rmem rq rclk rd stq emq gq { s with orc := v } :=
  { H with
    orc := rfl
    q1_sync := H.q1_sync.trans (syncOut_mono List.prefix_rfl List.prefix_rfl h.isPrefix) }

theorem rin_mem (v : List (BitVec n → α)) (h : rmem ⊏ v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc nq1 nd
      mst v rq rclk rd stq emq gq { s with mem := v } :=
  { H with
    mem := rfl
    rdata_ok := H.rdata_ok.mono (by have := h.isPrefix.length_le; omega) (fun _ _ => rfl)
      (fun u hu => by rw [h.isPrefix.getD_eq_left (by omega)]) }

-- Internal wires

theorem rint_clk_regs (h : rclk ⊏ F) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc nq1 nd
      mst rmem rq F rd stq emq gq s :=
  { H with
    rclk_F := List.prefix_rfl
    st_ok := H.st_ok.rmono_bus h.isPrefix List.prefix_rfl
    empty_ok := H.empty_ok.imp (fun q hq =>
      And.intro (hq.1.rmono_bus h.isPrefix List.prefix_rfl) hq.2)
    gray_ok := H.gray_ok.rmono_bus h.isPrefix List.prefix_rfl }

theorem rint_clear (v : List Bool) (h1 : crn ⊏ v) (h2 : ClearOK Rc v v.length) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc v sclk sd sorc F stf nst ninc nq1 nd
      mst rmem rq rclk rd stq emq gq s :=
  { H with crn_ok := h2 }

theorem rint_clk_sync (h : sclk ⊏ F) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn F sd sorc F stf nst ninc nq1 nd
      mst rmem rq rclk rd stq emq gq s :=
  { H with
    sclk_F := List.prefix_rfl
    q1_sync := H.q1_sync.trans (syncOut_mono h.isPrefix List.prefix_rfl List.prefix_rfl) }

theorem rint_sync_next {out : List (BitVec (n+1))}
    (hout : out <+: syncOut lat su stl sclk sd sorc) (h : nq1 ⊏ out) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc
      out nd mst rmem rq rclk rd stq emq gq s :=
  { H with
    q1_sync := hout
    d_ok := H.d_ok.rmono_next (s := ⟨nst, ninc, nq1, nd⟩)
      (s' := ⟨nst, ninc, out, nd⟩)
      List.prefix_rfl List.prefix_rfl h.isPrefix }

theorem rint_regs_stf (v : List (RSt n)) (h1 : stq <+: v)
    (h2 : RegOutG kq su default (RFilter P S R pw F ninc) rclk (fun u => (rd.getD u default).st)
      rd.length (min rclk.length rd.length) v) (h3 : stf ⊏ v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F v nst ninc nq1 nd
      mst rmem rq rclk rd v emq gq s :=
  { H with
    stf_q := List.prefix_rfl
    st_stf := H.st_stf.trans h3.isPrefix
    mst_stf := H.mst_stf.trans h3.isPrefix
    st_ok := h2 }

theorem rint_stf_next (h : nst ⊏ stf) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf stf ninc nq1 nd
      mst rmem rq rclk rd stq emq gq s :=
  { H with
    st_stf := List.prefix_rfl
    d_ok := H.d_ok.rmono_next (s := ⟨nst, ninc, nq1, nd⟩) (s' := ⟨stf, ninc, nq1, nd⟩)
      h.isPrefix List.prefix_rfl List.prefix_rfl }

theorem rint_stf_rdat (h : mst ⊏ stf) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc nq1 nd
      stf rmem rq rclk rd stq emq gq s :=
  { H with
    mst_stf := List.prefix_rfl
    rdata_ok := H.rdata_ok.mono (by have := h.isPrefix.length_le; omega)
      (fun u hu => by rw [h.isPrefix.getD_eq_left (by omega)]) (fun _ _ => rfl) }

theorem rint_next_regs (v : List (RNext n)) (h1 : nd <+: v)
    (h2 : CombOut (rnextDep ⟨nst, ninc, nq1, nd⟩) rnextFun (rnextLen ⟨nst, ninc, nq1, nd⟩) dmin dmax v)
    (h3 : rd ⊏ v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc nq1 v
      mst rmem rq rclk v stq emq gq s :=
  { H with
    d_link := List.prefix_rfl
    d_ok := h2.rmono_next (s := ⟨nst, ninc, nq1, nd⟩) (s' := ⟨nst, ninc, nq1, v⟩)
      List.prefix_rfl List.prefix_rfl List.prefix_rfl
    st_ok := H.st_ok.rmono_bus List.prefix_rfl h3.isPrefix
    empty_ok := H.empty_ok.imp (fun q hq =>
      And.intro (hq.1.rmono_bus List.prefix_rfl h3.isPrefix) hq.2)
    gray_ok := H.gray_ok.rmono_bus List.prefix_rfl h3.isPrefix }

-- Outputs

theorem rout_gray (v : List (BitVec (n+1)))
    (h : BusRegOutG kq su (RFilter P S R pw F ninc) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min rclk.length rd.length) v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc nq1 nd
      mst rmem rq rclk rd stq emq v { s with gray_q := v } :=
  { H with gray_q := rfl, gray_ok := h }

theorem rout_empty (v : List Bool)
    (h : ∃ q, RegOutG kq su default (RFilter P S R pw F ninc) rclk
      (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q ∧
      v = q.map (fun st => st.empty)) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc nq1 nd
      mst rmem rq rclk rd stq v gq { s with empty_q := v } :=
  { H with empty_q := rfl, empty_ok := h }

theorem rout_rdata (v : List α)
    (h : ReadOut ddmin ddmax (fun u => (mst.getD u default).ptr.setWidth n)
      (fun u => rmem.getD u (fun _ => default)) (min mst.length rmem.length) v) :
    RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc crn sclk sd sorc F stf nst ninc nq1 nd
      mst rmem v rclk rd stq emq gq { s with rdata_q := v } :=
  { H with rdata_q := rfl, rdata_ok := h }

/-- The specification's view of the relaxed relations, transported along the relation. -/
theorem rout_gray_spec (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P)
    (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (v : List (BitVec (n+1)))
    (h : BusRegOutG kq su (RFilter P S R pw F ninc) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min rclk.length rd.length) v) :
    RGrayF lat stl su kq P S R pw s.clk s.inc s.wgray s.orc v := by
  rw [← H.clk, ← H.inc, ← H.wgray, ← H.orc]
  exact rgray_correct H.toLinks hP1 hP2 hS hdd hR h

theorem rout_empty_spec (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P)
    (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (v : List Bool)
    (h : ∃ q, RegOutG kq su default (RFilter P S R pw F ninc) rclk
      (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q ∧
      v = q.map (fun st => st.empty)) :
    REmptyF lat stl su kq P S R pw s.clk s.inc s.wgray s.orc v := by
  rw [← H.clk, ← H.inc, ← H.wgray, ← H.orc]
  exact rempty_correct H.toLinks hP1 hP2 hS hdd hR h

theorem rout_rdata_spec (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P)
    (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (hkq : 0 < kq)
    (hrr : ddmin ≤ ddmax) (hrw : ddmax ≤ rdly) (v : List α)
    (h : ReadOut ddmin ddmax (fun u => (mst.getD u default).ptr.setWidth n)
      (fun u => rmem.getD u (fun _ => default)) (min mst.length rmem.length) v) :
    RDataF lat stl su kq rdly P S R pw s.clk s.inc s.wgray s.orc s.mem v := by
  rw [← H.clk, ← H.inc, ← H.wgray, ← H.orc]
  exact rdata_correct H.toLinks hP1 hP2 hS hdd hR hkq hrr hrw h

end Rel

def rpsi (lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc : Nat) (i : rdomTimedT α n)
    (s : RStateF α n) : Prop :=
  RPsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc i.2.2.2.2.2.2.crn
    i.2.2.1.1 i.2.2.1.2.1 i.2.2.1.2.2.1 i.2.2.2.1
    i.2.1 i.2.2.2.2.1.st i.2.2.2.2.1.inc i.2.2.2.2.1.q1 i.2.2.2.2.1.d
    i.2.2.2.2.2.1.st i.2.2.2.2.2.1.mem i.2.2.2.2.2.1.q
    i.2.2.2.2.2.2.clk i.2.2.2.2.2.2.d i.2.2.2.2.2.2.st_q i.2.2.2.2.2.2.empty_q
    i.2.2.2.2.2.2.gray_q s

theorem RPsi.init : RPsi (α := α) (n := n) lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc
    [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] ⟨[], [], [], [], [], [], [], []⟩ where
  clk := rfl
  inc := rfl
  wgray := rfl
  orc := rfl
  mem := rfl
  gray_q := rfl
  empty_q := rfl
  rdata_q := rfl
  crn_ok := ⟨fun u _ => rfl, fun u _ h => absurd h (Nat.not_lt_zero u)⟩
  sclk_F := List.nil_prefix
  rclk_F := List.nil_prefix
  q1_sync := List.nil_prefix
  stf_q := List.nil_prefix
  st_stf := List.nil_prefix
  mst_stf := List.nil_prefix
  d_link := List.nil_prefix
  st_ok := ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  d_ok := ⟨Nat.zero_le _, fun t _ ht => absurd ht (Nat.not_lt_zero t)⟩
  empty_ok := ⟨[], ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩, rfl⟩
  gray_ok := ⟨⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩,
    fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  rdata_ok := ⟨Nat.zero_le _, fun t _ ht => absurd ht (Nat.not_lt_zero t)⟩

/-! ### The specification's rules -/

section SpecRules
variable (sp : RStateF α n)

theorem rspec_in_clk (v : List Bool) (h : sp.clk ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"clk").2 sp v { sp with clk := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem rspec_in_inc (v : List Bool) (h : sp.inc ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"inc").2 sp v { sp with inc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem rspec_in_wgray (v : List (BitVec (n+1))) (h : sp.wgray ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"wgray").2 sp v { sp with wgray := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem rspec_in_orc (v : List (Orc n)) (h : sp.orc ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"orc").2 sp v { sp with orc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem rspec_in_mem (v : List (BitVec n → α)) (h : sp.mem ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"mem").2 sp v { sp with mem := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem rspec_out_gray (v : List (BitVec (n+1))) (h1 : sp.gray_q <+: v)
    (h2 : RGrayF lat stl su kq P S R pw sp.clk sp.inc sp.wgray sp.orc v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).outputs.getIO ↑"gray").2 sp v { sp with gray_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
theorem rspec_out_empty (v : List Bool) (h1 : sp.empty_q <+: v)
    (h2 : REmptyF lat stl su kq P S R pw sp.clk sp.inc sp.wgray sp.orc v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).outputs.getIO ↑"empty").2 sp v { sp with empty_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
theorem rspec_out_rdata (v : List α) (h1 : sp.rdata_q <+: v)
    (h2 : RDataF lat stl su kq rdly P S R pw sp.clk sp.inc sp.wgray sp.orc sp.mem v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).outputs.getIO ↑"rdata").2 sp v { sp with rdata_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 2000000 in
theorem rrefines_psi (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P)
    (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (hkq : 0 < kq)
    (hrr : ddmin ≤ ddmax) (hrw : ddmax ≤ rdly)
    (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) :
    rdomTimed α n lat kq su stl dmin dmax ddmin ddmax Pg pwg Rg Rc ⊑_{rpsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc} readDomainF α n lat stl su kq rdly P S R pw := by
  intro i s Hψ
  obtain ⟨csrc, stf, ⟨sclk, sd, sorc, sq⟩, F, ⟨nst, ninc, nq1, nd⟩, ⟨mst, rmem, rq⟩, ⟨rclk, rd, crn, stq, emq, gq⟩⟩ := i
  dsimp only [rpsi] at Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨csrc', stf', ⟨sclk', sd', sorc', sq'⟩, F', ⟨nst', ninc', nq1', nd'⟩, ⟨mst', rmem', rq'⟩, ⟨rclk', rd', crn', stq', emq', gq'⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs (rdomTimed α n lat kq su stl dmin dmax ddmin ddmax Pg pwg Rg Rc), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [rdomTimed] at Hcontains
    rcases Hcontains with h | h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, RNextSt.mk.injEq, RDataSt.mk.injEq, RRegSt.mk.injEq,
      and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨_, _, rspec_in_clk s _ (by rw [← Hψ.clk]; assumption), existSR_reflexive,
          rin_clk Hψ _ ‹_›⟩
      | exact ⟨_, _, rspec_in_inc s _ (by rw [← Hψ.inc]; assumption), existSR_reflexive,
          rin_inc Hψ _ ‹_›⟩
      | exact ⟨_, _, rspec_in_wgray s _ (by rw [← Hψ.wgray]; assumption), existSR_reflexive,
          rin_wgray Hψ _ ‹_›⟩
      | exact ⟨_, _, rspec_in_orc s _ (by rw [← Hψ.orc]; assumption), existSR_reflexive,
          rin_orc Hψ _ ‹_›⟩
      | exact ⟨_, _, rspec_in_mem s _ (by rw [← Hψ.mem]; assumption), existSR_reflexive,
          rin_mem Hψ _ ‹_›⟩
  · intro ident mid_i v Hrule
    obtain ⟨csrc', stf', ⟨sclk', sd', sorc', sq'⟩, F', ⟨nst', ninc', nq1', nd'⟩, ⟨mst', rmem', rq'⟩, ⟨rclk', rd', crn', stq', emq', gq'⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs (rdomTimed α n lat kq su stl dmin dmax ddmin ddmax Pg pwg Rg Rc), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [rdomTimed] at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, RNextSt.mk.injEq, RDataSt.mk.injEq, RRegSt.mk.injEq,
      and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | (have hc := Hψ.busreg_of hPg hpwg hRg h
         exact ⟨s, _, existSR_reflexive, rspec_out_gray s _ (by rw [Hψ.gray_q]; assumption)
           (rout_gray_spec Hψ hP1 hP2 hS hdd hR _ hc), rout_gray Hψ _ hc⟩)
      | (have hc := h.imp (fun q hq => And.intro (Hψ.reg_of hPg hpwg hRg hq.1) hq.2)
         exact ⟨s, _, existSR_reflexive, rspec_out_empty s _ (by rw [Hψ.empty_q]; assumption)
           (rout_empty_spec Hψ hP1 hP2 hS hdd hR _ hc), rout_empty Hψ _ hc⟩)
      | exact ⟨s, _, existSR_reflexive, rspec_out_rdata s _ (by rw [Hψ.rdata_q]; assumption)
          (rout_rdata_spec Hψ hP1 hP2 hS hdd hR hkq hrr hrw _ ‹_›), rout_rdata Hψ _ ‹_›⟩
  · intro rule mid_i Hin Hrule
    obtain ⟨csrc', stf', ⟨sclk', sd', sorc', sq'⟩, F', ⟨nst', ninc', nq1', nd'⟩, ⟨mst', rmem', rq'⟩, ⟨rclk', rd', crn', stq', emq', gq'⟩⟩ := mid_i
    simp only [rdomTimed, List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h
    all_goals subst h
    all_goals simp only [forall_const, and_true, not_true_eq_false, false_implies] at Hrule
    all_goals obtain ⟨⟨c0, c1, ⟨c2, c3, c4, c4'⟩, c5, ⟨c6, c7, c8, c9⟩, ⟨c10, c11, c12⟩, ⟨c13, c14, c15, c16, c17, c18⟩⟩, out, Hrule⟩ := Hrule
    all_goals simp only [Prod.mk.injEq, RNextSt.mk.injEq, RDataSt.mk.injEq, RRegSt.mk.injEq,
      and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨s, existSR_reflexive, rint_clk_regs Hψ ‹_›⟩
      | exact ⟨s, existSR_reflexive, rint_clear Hψ _ ‹_› ‹_›⟩
      | exact ⟨s, existSR_reflexive, rint_clk_sync Hψ ‹_›⟩
      | exact ⟨s, existSR_reflexive, rint_sync_next Hψ ‹_› ‹_›⟩
      | exact ⟨s, existSR_reflexive, rint_regs_stf Hψ _ ‹_› (Hψ.reg_of hPg hpwg hRg ‹_›) ‹_›⟩
      | exact ⟨s, existSR_reflexive, rint_stf_next Hψ ‹_›⟩
      | exact ⟨s, existSR_reflexive, rint_stf_rdat Hψ ‹_›⟩
      | exact ⟨s, existSR_reflexive, rint_next_regs Hψ _ ‹_› ‹_› ‹_›⟩

theorem rrefines_initial :
    Module.refines_initial (rdomTimed α n lat kq su stl dmin dmax ddmin ddmax Pg pwg Rg Rc) (readDomainF α n lat stl su kq rdly P S R pw)
      (rpsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc) := by
  intro i hi
  obtain ⟨csrc, stf, ⟨sclk, sd, sorc, sq⟩, F, ⟨nst, ninc, nq1, nd⟩, ⟨mst, rmem, rq⟩, ⟨rclk, rd, crn, stq, emq, gq⟩⟩ := i
  simp only [rdomTimed, Prod.mk.injEq, RNextSt.mk.injEq, RDataSt.mk.injEq, RRegSt.mk.injEq,
    and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩ := hi
  exact ⟨⟨[], [], [], [], [], [], [], []⟩, rfl, RPsi.init⟩

/-- **The timed read domain refines the filtered read domain.** -/
theorem rdomTimed_refines (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P)
    (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (hkq : 0 < kq)
    (hrr : ddmin ≤ ddmax) (hrw : ddmax ≤ rdly)
    (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) :
    rdomTimed α n lat kq su stl dmin dmax ddmin ddmax Pg pwg Rg Rc ⊑ readDomainF α n lat stl su kq rdly P S R pw :=
  ⟨inferInstance, rpsi lat kq su stl dmin dmax ddmin ddmax rdly P S R pw Pg pwg Rg Rc,
   rrefines_psi hP1 hP2 hS hdd hR hkq hrr hrw hPg hpwg hRg, rrefines_initial⟩

end Graphiti.AsyncFifo.Timed
