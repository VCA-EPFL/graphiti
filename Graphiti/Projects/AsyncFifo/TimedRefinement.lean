/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.TimedProof
import Graphiti.Projects.AsyncFifo.Modules

/-!
# The timed write domain refines the filtered write domain

`wdomTimed_refines`: the write domain built from timed blocks (clock fork, metastable
synchroniser stage, next-state logic with delay window `[dmin, dmax]`, register bank with
clk-to-q window `kq` and setup `su`) refines the filtered register-level write domain
`writeDomainF` with clock-period filter `P` and input-setup filter `S`, whenever

    kq + su + dmax + 2 ≤ P,   stl + su + dmax + 2 ≤ P,   su + dmax + 1 ≤ S,   dmin ≤ dmax,   dmax + su + 1 ≤ R.

The simulation relation `Psi` records that the specification's input streams are the ones
stored by the blocks they feed, that its output histories are the register bank's, and the
`Links` between the blocks (wires are prefixes of what drives them, contracts hold for the
blocks' current inputs).  The contracts are monotone in the inputs, so `Psi` survives every
internal transition; the delay analysis of `TimedProof.lean` turns the register bank's
contracts into the relaxed relations the specification demands.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Timed

open Graphiti.AsyncFifo

variable {α : Type} [Inhabited α] {n lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc : Nat}

instance : MatchInterface (wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc) (writeDomainF α n lat stl su kq P S R pw) := by
  dsimp [wdomTimed, writeDomainF]
  solve_match_interface

/-! ### Monotonicity of the next-state contract in the block's inputs -/

theorem nextLen_mono {s s' : NextSt α n} (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data)
    (h4 : s.q1 <+: s'.q1) : nextLen α s ≤ nextLen α s' := by
  have := h1.length_le; have := h2.length_le; have := h3.length_le; have := h4.length_le
  unfold nextLen; omega

theorem nextDep_congr {s s' : NextSt α n} (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data)
    (h4 : s.q1 <+: s'.q1) {u : Nat} (hu : u < nextLen α s) : nextDep α s u = nextDep α s' u := by
  unfold nextLen at hu
  unfold nextDep
  rw [h1.getD_eq_left (by omega), h2.getD_eq_left (by omega), h3.getD_eq_left (by omega), h4.getD_eq_left (by omega)]

theorem CombOut.mono_next {s s' : NextSt α n} (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data)
    (h4 : s.q1 <+: s'.q1) {v : List (WNext α n)}
    (h : CombOut (nextDep α s) (nextFun α) (nextLen α s) dmin dmax v) :
    CombOut (nextDep α s') (nextFun α) (nextLen α s') dmin dmax v :=
  h.mono (nextLen_mono h1 h2 h3 h4) (fun u hu => nextDep_congr h1 h2 h3 h4 hu)

/-- Register-bank contracts survive a growth of the bank's inputs. -/
theorem RegOutG.mono_bus {kq su : Nat} {G : Nat → Prop} {rclk rclk' : List Bool}
    {rd rd' : List (WNext α n)} {q : List (WSt n)} (hc : rclk <+: rclk') (hd : rd <+: rd')
    (h : RegOutG kq su default G rclk (fun u => (rd.getD u default).st) rd.length
          (min rclk.length rd.length) q) :
    RegOutG kq su default G rclk' (fun u => (rd'.getD u default).st) rd'.length
      (min rclk'.length rd'.length) q := by
  have h1 := hc.length_le; have h2 := hd.length_le
  exact h.mono hc (fun u hu => by rw [hd.getD_eq_left hu]) h2 (by omega) (by omega) (by omega)
    (fun _ _ hg => hg)

theorem BusRegOutG.mono_bus {kq su : Nat} {G : Nat → Prop} {rclk rclk' : List Bool}
    {rd rd' : List (WNext α n)} {q : List (BitVec (n+1))} (hc : rclk <+: rclk') (hd : rd <+: rd')
    (h : BusRegOutG kq su G rclk (fun u => (rd.getD u default).gnext) rd.length
          (min rclk.length rd.length) q) :
    BusRegOutG kq su G rclk' (fun u => (rd'.getD u default).gnext) rd'.length
      (min rclk'.length rd'.length) q := by
  have h1 := hc.length_le; have h2 := hd.length_le
  exact h.mono hc (fun u hu => by rw [hd.getD_eq_left hu]) h2 (by omega) (by omega) (by omega)
    (fun _ _ hg => hg)

theorem MemOutG.mono_bus {kq su : Nat} {G : Nat → Prop} {rclk rclk' : List Bool}
    {rd rd' : List (WNext α n)} {q : List (BitVec n → α)} (hc : rclk <+: rclk') (hd : rd <+: rd')
    (h : MemOutG kq su G rclk (fun u => (rd.getD u default).we) (fun u => (rd.getD u default).addr)
      (fun u => (rd.getD u default).data) rd.length (min rclk.length rd.length) q) :
    MemOutG kq su G rclk' (fun u => (rd'.getD u default).we) (fun u => (rd'.getD u default).addr)
      (fun u => (rd'.getD u default).data) rd'.length (min rclk'.length rd'.length) q := by
  have h1 := hc.length_le; have h2 := hd.length_le
  exact h.mono hc h2 (fun u hu => by rw [hd.getD_eq_left hu]) (fun u hu => by rw [hd.getD_eq_left hu])
    (fun u hu => by rw [hd.getD_eq_left hu]) (by omega) (by omega) (by omega) (fun _ _ hg => hg)

/-- Only the guard changes: the domain's inputs grew, so the filter at each instant is the one
read off the shorter streams. -/
theorem RegOutG.mono_guard {kq su : Nat} {G G' : Nat → Prop} {rclk : List Bool}
    {rd : List (WNext α n)} {q : List (WSt n)} (hG : ∀ t, t ≤ min rclk.length rd.length → G' t → G t)
    (h : RegOutG kq su default G rclk (fun u => (rd.getD u default).st) rd.length
          (min rclk.length rd.length) q) :
    RegOutG kq su default G' rclk (fun u => (rd.getD u default).st) rd.length
      (min rclk.length rd.length) q := by
  have hq := h.1
  exact h.mono List.prefix_rfl (fun _ _ => rfl) (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)
    (fun t ht hg => hG t (by omega) hg)

theorem BusRegOutG.mono_guard {kq su : Nat} {G G' : Nat → Prop} {rclk : List Bool}
    {rd : List (WNext α n)} {q : List (BitVec (n+1))} (hG : ∀ t, t ≤ min rclk.length rd.length → G' t → G t)
    (h : BusRegOutG kq su G rclk (fun u => (rd.getD u default).gnext) rd.length
          (min rclk.length rd.length) q) :
    BusRegOutG kq su G' rclk (fun u => (rd.getD u default).gnext) rd.length
      (min rclk.length rd.length) q := by
  have hq := h.1.1
  exact h.mono List.prefix_rfl (fun _ _ => rfl) (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)
    (fun t ht hg => hG t (by omega) hg)

theorem MemOutG.mono_guard {kq su : Nat} {G G' : Nat → Prop} {rclk : List Bool}
    {rd : List (WNext α n)} {q : List (BitVec n → α)} (hG : ∀ t, t ≤ min rclk.length rd.length → G' t → G t)
    (h : MemOutG kq su G rclk (fun u => (rd.getD u default).we) (fun u => (rd.getD u default).addr)
      (fun u => (rd.getD u default).data) rd.length (min rclk.length rd.length) q) :
    MemOutG kq su G' rclk (fun u => (rd.getD u default).we) (fun u => (rd.getD u default).addr)
      (fun u => (rd.getD u default).data) rd.length (min rclk.length rd.length) q := by
  have hq := h.1
  exact h.mono List.prefix_rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by omega) (by omega) (Nat.le_refl _) (fun t ht hg => hG t (by omega) hg)

/-! ### The simulation relation -/

/-- The simulation relation, on the fifteen streams of the timed design (synchroniser
`sclk sd sorc`, fork `F`, next-state block `nst ninc ndata nq1 nd`, register bank
`rclk rd stq fq gq mq`) and the specification state. -/
structure Psi (lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc : Nat) (crn : List Bool)
    (sclk : List Bool) (sd : List (BitVec (n+1))) (sorc : List (Orc n))
    (F : List Bool) (nst : List (WSt n)) (ninc : List Bool) (ndata : List α) (nq1 : List (BitVec (n+1)))
    (nd : List (WNext α n)) (rclk : List Bool) (rd : List (WNext α n)) (stq : List (WSt n)) (fq : List Bool)
    (gq : List (BitVec (n+1))) (mq : List (BitVec n → α)) (s : WStateF α n) : Prop where
  clk : F = s.clk
  inc : ninc = s.inc
  data : ndata = s.data
  rgray : sd = s.rgray
  orc : sorc = s.orc
  gray_q : s.gray_q = gq
  full_q : s.full_q = fq
  mem_q : s.mem_q = mq
  crn_ok : ClearOK Rc crn crn.length
  links : Links kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc ninc ndata nst nq1 nd rd stq
  full_ok : ∃ q, RegOutG kq su default (WFilter P S R pw F ninc ndata) rclk
      (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q ∧
    fq = q.map (fun st => st.full)
  gray_ok : BusRegOutG kq su (WFilter P S R pw F ninc ndata) rclk
    (fun u => (rd.getD u default).gnext) rd.length (min rclk.length rd.length) gq
  mem_ok : MemOutG kq su (WFilter P S R pw F ninc ndata) rclk (fun u => (rd.getD u default).we)
    (fun u => (rd.getD u default).addr) (fun u => (rd.getD u default).data) rd.length
    (min rclk.length rd.length) mq

def ψ (lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc : Nat) (i : wdomTimedT α n) (s : WStateF α n) : Prop :=
  Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc i.2.2.2.2.crn
    i.2.1.1 i.2.1.2.1 i.2.1.2.2.1 i.2.2.1 i.2.2.2.1.st i.2.2.2.1.inc i.2.2.2.1.data i.2.2.2.1.q1 i.2.2.2.1.d
    i.2.2.2.2.clk i.2.2.2.2.d i.2.2.2.2.st_q i.2.2.2.2.full_q i.2.2.2.2.gray_q i.2.2.2.2.mem_q s

theorem Psi.init : Psi (α := α) (n := n) lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc
    [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
    ⟨[], [], [], [], [], [], [], []⟩ where
  clk := rfl
  inc := rfl
  data := rfl
  rgray := rfl
  orc := rfl
  gray_q := rfl
  full_q := rfl
  mem_q := rfl
  crn_ok := ⟨fun u _ => rfl, fun u _ h => absurd h (Nat.not_lt_zero u)⟩
  links :=
    { sclk_F := List.nil_prefix, rclk_F := List.nil_prefix, q1_sync := List.nil_prefix, st_link := List.nil_prefix
      d_link := List.nil_prefix
      st_ok := ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
      d_ok := ⟨Nat.zero_le _, fun t _ ht => absurd ht (Nat.not_lt_zero t)⟩ }
  full_ok := ⟨[], ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩, rfl⟩
  gray_ok := ⟨⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  mem_ok := ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩

/-! ### The specification's rules -/

section SpecRules
variable (s : WStateF α n)

theorem spec_in_clk (v : List Bool) (h : s.clk ⊏ v) :
    ((writeDomainF α n lat stl su kq P S R pw).inputs.getIO ↑"clk").2 s v { s with clk := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_inc (v : List Bool) (h : s.inc ⊏ v) :
    ((writeDomainF α n lat stl su kq P S R pw).inputs.getIO ↑"inc").2 s v { s with inc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_data (v : List α) (h : s.data ⊏ v) :
    ((writeDomainF α n lat stl su kq P S R pw).inputs.getIO ↑"data").2 s v { s with data := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_rgray (v : List (BitVec (n+1))) (h : s.rgray ⊏ v) :
    ((writeDomainF α n lat stl su kq P S R pw).inputs.getIO ↑"rgray").2 s v { s with rgray := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_orc (v : List (Orc n)) (h : s.orc ⊏ v) :
    ((writeDomainF α n lat stl su kq P S R pw).inputs.getIO ↑"orc").2 s v { s with orc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_gray (v : List (BitVec (n+1))) (h1 : s.gray_q <+: v)
    (h2 : WGrayF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v) :
    ((writeDomainF α n lat stl su kq P S R pw).outputs.getIO ↑"gray").2 s v { s with gray_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
theorem spec_out_full (v : List Bool) (h1 : s.full_q <+: v)
    (h2 : WFullF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v) :
    ((writeDomainF α n lat stl su kq P S R pw).outputs.getIO ↑"full").2 s v { s with full_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
theorem spec_out_mem (v : List (BitVec n → α)) (h1 : s.mem_q <+: v)
    (h2 : WMemF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v) :
    ((writeDomainF α n lat stl su kq P S R pw).outputs.getIO ↑"mem").2 s v { s with mem_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

end SpecRules

/-! ### The transitions -/

section Cases

variable {crn : List Bool}
  {sclk : List Bool} {sd : List (BitVec (n+1))} {sorc : List (Orc n)} {F : List Bool} {nst : List (WSt n)}
  {ninc : List Bool} {ndata : List α} {nq1 : List (BitVec (n+1))} {nd : List (WNext α n)} {rclk : List Bool}
  {rd : List (WNext α n)} {stq : List (WSt n)} {fq : List Bool} {gq : List (BitVec (n+1))} {mq : List (BitVec n → α)}
  {s : WStateF α n}
  (Hψ : Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst ninc ndata nq1 nd rclk rd stq fq gq mq s)
include Hψ

/-- The filter is read off the domain's own streams, so when they grow the guard the bank's
contracts carry has to be pulled back along the growth.  Everything the pullback needs about
lengths is in the lens. -/
theorem Psi.guard_mono {F' ninc' : List Bool} {ndata' : List α}
    (h1 : F <+: F') (h2 : ninc <+: ninc') (h3 : ndata <+: ndata') :
    ∀ t, t ≤ min rclk.length rd.length →
      WFilter P S R pw F' ninc' ndata' t → WFilter P S R pw F ninc ndata t := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14⟩ := Hψ.links.lens
  exact fun t ht => WFilter_congr h1 h2 h3 (by omega) (by omega) (by omega)

-- Inputs

theorem in_rgray (v : List (BitVec (n+1))) (h : sd ⊏ v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk v sorc F nst ninc ndata nq1 nd rclk rd stq fq gq mq { s with rgray := v } :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, rfl, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       q1_sync := Hψ.links.q1_sync.trans (syncOut_mono List.prefix_rfl h.isPrefix List.prefix_rfl) },
   Hψ.full_ok, Hψ.gray_ok, Hψ.mem_ok⟩

theorem in_orc (v : List (Orc n)) (h : sorc ⊏ v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd v F nst ninc ndata nq1 nd rclk rd stq fq gq mq { s with orc := v } :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, rfl, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       q1_sync := Hψ.links.q1_sync.trans (syncOut_mono List.prefix_rfl List.prefix_rfl h.isPrefix) },
   Hψ.full_ok, Hψ.gray_ok, Hψ.mem_ok⟩

theorem in_clk (v : List Bool) (h : F ⊏ v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc v nst ninc ndata nq1 nd rclk rd stq fq gq mq { s with clk := v } :=
  ⟨rfl, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       sclk_F := Hψ.links.sclk_F.trans h.isPrefix
       rclk_F := Hψ.links.rclk_F.trans h.isPrefix
       st_ok := Hψ.links.st_ok.mono_guard (Hψ.guard_mono h.isPrefix List.prefix_rfl List.prefix_rfl) },
   (let ⟨q, hq, e⟩ := Hψ.full_ok; ⟨q, hq.mono_guard (Hψ.guard_mono h.isPrefix List.prefix_rfl List.prefix_rfl), e⟩),
   Hψ.gray_ok.mono_guard (Hψ.guard_mono h.isPrefix List.prefix_rfl List.prefix_rfl), Hψ.mem_ok.mono_guard (Hψ.guard_mono h.isPrefix List.prefix_rfl List.prefix_rfl)⟩

theorem in_inc (v : List Bool) (h : ninc ⊏ v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst v ndata nq1 nd rclk rd stq fq gq mq { s with inc := v } :=
  ⟨Hψ.clk, rfl, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       d_ok := (Hψ.links.d_ok.mono_next (s := ⟨nst, ninc, ndata, nq1, nd⟩) (s' := ⟨nst, v, ndata, nq1, nd⟩) List.prefix_rfl h.isPrefix
                 List.prefix_rfl List.prefix_rfl)
       st_ok := Hψ.links.st_ok.mono_guard (Hψ.guard_mono List.prefix_rfl h.isPrefix List.prefix_rfl) },
   (let ⟨q, hq, e⟩ := Hψ.full_ok; ⟨q, hq.mono_guard (Hψ.guard_mono List.prefix_rfl h.isPrefix List.prefix_rfl), e⟩),
   Hψ.gray_ok.mono_guard (Hψ.guard_mono List.prefix_rfl h.isPrefix List.prefix_rfl), Hψ.mem_ok.mono_guard (Hψ.guard_mono List.prefix_rfl h.isPrefix List.prefix_rfl)⟩

theorem in_data (v : List α) (h : ndata ⊏ v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst ninc v nq1 nd rclk rd stq fq gq mq { s with data := v } :=
  ⟨Hψ.clk, Hψ.inc, rfl, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       d_ok := (Hψ.links.d_ok.mono_next (s := ⟨nst, ninc, ndata, nq1, nd⟩) (s' := ⟨nst, ninc, v, nq1, nd⟩) List.prefix_rfl List.prefix_rfl
                 h.isPrefix List.prefix_rfl)
       st_ok := Hψ.links.st_ok.mono_guard (Hψ.guard_mono List.prefix_rfl List.prefix_rfl h.isPrefix) },
   (let ⟨q, hq, e⟩ := Hψ.full_ok; ⟨q, hq.mono_guard (Hψ.guard_mono List.prefix_rfl List.prefix_rfl h.isPrefix), e⟩),
   Hψ.gray_ok.mono_guard (Hψ.guard_mono List.prefix_rfl List.prefix_rfl h.isPrefix), Hψ.mem_ok.mono_guard (Hψ.guard_mono List.prefix_rfl List.prefix_rfl h.isPrefix)⟩

/-- **Where the netlist's assumptions meet the domain's.**  The bank promises under `GateOK` ---
a clock whose pulses are wide enough and whose first edge is late enough, and a clear that has
been released --- while the domain assumes `WFilter`.  This is the only place the two are
compared, and the comparison is three weakenings and the clear source's own guarantee. -/
theorem Psi.gate_of (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) :
    ∀ t, t ≤ min (min rclk.length rd.length) crn.length →
      WFilter P S R pw F ninc ndata t → GateOK Pg pwg Rg Rc rclk crn t := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14⟩ := Hψ.links.lens
  intro t ht hf
  exact ⟨(ClockOK.congr Hψ.links.rclk_F (by omega) hf.1).weaken hPg,
         (PulseOK.congr Hψ.links.rclk_F (by omega) hf.2.2.2.2).weaken hpwg,
         (ResetOK.congr Hψ.links.rclk_F (by omega) hf.2.2.2.1).weaken hRg,
         Hψ.crn_ok.mono (by omega)⟩

theorem Psi.reg_of (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) {v : List (WSt n)}
    (h : RegOutG kq su default (GateOK Pg pwg Rg Rc rclk crn) rclk (fun u => (rd.getD u default).st)
      rd.length (min (min rclk.length rd.length) crn.length) v) :
    RegOutG kq su default (WFilter P S R pw F ninc ndata) rclk (fun u => (rd.getD u default).st)
      rd.length (min rclk.length rd.length) v := by
  have hq := h.1
  exact h.mono List.prefix_rfl (fun _ _ => rfl) (Nat.le_refl _) (by omega) (by omega) (by omega)
    (fun t ht hg => Hψ.gate_of hPg hpwg hRg t (by omega) hg)

theorem Psi.busreg_of (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) {v : List (BitVec (n+1))}
    (h : BusRegOutG kq su (GateOK Pg pwg Rg Rc rclk crn) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min (min rclk.length rd.length) crn.length) v) :
    BusRegOutG kq su (WFilter P S R pw F ninc ndata) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min rclk.length rd.length) v := by
  have hq := h.1.1
  exact h.mono List.prefix_rfl (fun _ _ => rfl) (Nat.le_refl _) (by omega) (by omega) (by omega)
    (fun t ht hg => Hψ.gate_of hPg hpwg hRg t (by omega) hg)

theorem Psi.mem_of (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) {v : List (BitVec n → α)}
    (h : MemOutG kq su (GateOK Pg pwg Rg Rc rclk crn) rclk (fun u => (rd.getD u default).we)
      (fun u => (rd.getD u default).addr) (fun u => (rd.getD u default).data) rd.length
      (min (min rclk.length rd.length) crn.length) v) :
    MemOutG kq su (WFilter P S R pw F ninc ndata) rclk (fun u => (rd.getD u default).we)
      (fun u => (rd.getD u default).addr) (fun u => (rd.getD u default).data) rd.length
      (min rclk.length rd.length) v := by
  have hq := h.1
  exact h.mono List.prefix_rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by omega) (by omega) (by omega) (fun t ht hg => Hψ.gate_of hPg hpwg hRg t (by omega) hg)

-- Outputs

theorem out_gray (v : List (BitVec (n+1))) (h : BusRegOutG kq su (WFilter P S R pw F ninc ndata) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min rclk.length rd.length) v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst ninc ndata nq1 nd rclk rd stq fq v mq { s with gray_q := v } :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, rfl, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok, Hψ.links, Hψ.full_ok, h, Hψ.mem_ok⟩

theorem out_full (v : List Bool)
    (h : ∃ q, RegOutG kq su default (WFilter P S R pw F ninc ndata) rclk
        (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q ∧
      v = q.map (fun st => st.full)) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst ninc ndata nq1 nd rclk rd stq v gq mq { s with full_q := v } :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, rfl, Hψ.mem_q, Hψ.crn_ok, Hψ.links, h, Hψ.gray_ok, Hψ.mem_ok⟩

theorem out_mem (v : List (BitVec n → α))
    (h : MemOutG kq su (WFilter P S R pw F ninc ndata) rclk (fun u => (rd.getD u default).we)
      (fun u => (rd.getD u default).addr) (fun u => (rd.getD u default).data) rd.length
      (min rclk.length rd.length) v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst ninc ndata nq1 nd rclk rd stq fq gq v { s with mem_q := v } :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, rfl, Hψ.crn_ok, Hψ.links, Hψ.full_ok, Hψ.gray_ok, h⟩

/-- The specification's view of the relaxed relations, transported along `Psi`. -/
theorem out_gray_spec (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (v : List (BitVec (n+1)))
    (h : BusRegOutG kq su (WFilter P S R pw F ninc ndata) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min rclk.length rd.length) v) :
    WGrayF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v := by
  rw [← Hψ.clk, ← Hψ.inc, ← Hψ.data, ← Hψ.rgray, ← Hψ.orc]
  exact gray_correct Hψ.links hP1 hP2 hS hdd hR h

theorem out_full_spec (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (v : List Bool)
    (h : ∃ q, RegOutG kq su default (WFilter P S R pw F ninc ndata) rclk
        (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q ∧
      v = q.map (fun st => st.full)) :
    WFullF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v := by
  rw [← Hψ.clk, ← Hψ.inc, ← Hψ.data, ← Hψ.rgray, ← Hψ.orc]
  exact full_correct Hψ.links hP1 hP2 hS hdd hR h

theorem out_mem_spec (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (v : List (BitVec n → α))
    (h : MemOutG kq su (WFilter P S R pw F ninc ndata) rclk (fun u => (rd.getD u default).we)
      (fun u => (rd.getD u default).addr) (fun u => (rd.getD u default).data) rd.length
      (min rclk.length rd.length) v) :
    WMemF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v := by
  rw [← Hψ.clk, ← Hψ.inc, ← Hψ.data, ← Hψ.rgray, ← Hψ.orc]
  exact mem_correct Hψ.links hP1 hP2 hS hdd hR h

-- Internal wires

/-- The clear reaches the register bank.  The value comes from the clear source, whose output
rule is what guarantees `ClearOK`; nothing else in the domain constrains it. -/
theorem int_clear (v : List Bool) (h1 : crn ⊏ v) (h2 : ClearOK Rc v v.length) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc v sclk sd sorc F nst ninc ndata nq1 nd rclk rd stq fq gq mq s :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, h2,
   Hψ.links, Hψ.full_ok, Hψ.gray_ok, Hψ.mem_ok⟩

/-- The clock reaches the register bank. -/
theorem int_clk_regs (h : rclk ⊏ F) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst ninc ndata nq1 nd F rd stq fq gq mq s :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       rclk_F := List.prefix_rfl
       st_ok := Hψ.links.st_ok.mono_bus h.isPrefix List.prefix_rfl },
   (let ⟨q, hq, e⟩ := Hψ.full_ok; ⟨q, hq.mono_bus h.isPrefix List.prefix_rfl, e⟩),
   Hψ.gray_ok.mono_bus h.isPrefix List.prefix_rfl, Hψ.mem_ok.mono_bus h.isPrefix List.prefix_rfl⟩

/-- The clock reaches the synchroniser. -/
theorem int_clk_sync (h : sclk ⊏ F) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn F sd sorc F nst ninc ndata nq1 nd rclk rd stq fq gq mq s :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       sclk_F := List.prefix_rfl
       q1_sync := Hψ.links.q1_sync.trans (syncOut_mono h.isPrefix List.prefix_rfl List.prefix_rfl) },
   Hψ.full_ok, Hψ.gray_ok, Hψ.mem_ok⟩

/-- The synchroniser's output reaches the next-state logic.  The stage reports a prefix of what
its oracle determines, and that prefix is what the next-state block stores. -/
theorem int_sync_next {out : List (BitVec (n+1))}
    (hout : out <+: syncOut lat su stl sclk sd sorc) (h : nq1 ⊏ out) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst ninc ndata out nd rclk rd stq fq gq mq s :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       q1_sync := hout
       d_ok := (Hψ.links.d_ok.mono_next (s := ⟨nst, ninc, ndata, nq1, nd⟩) (s' := ⟨nst, ninc, ndata, out, nd⟩) List.prefix_rfl
                 List.prefix_rfl List.prefix_rfl h.isPrefix) },
   Hψ.full_ok, Hψ.gray_ok, Hψ.mem_ok⟩

/-- The state register reaches the next-state logic. -/
theorem int_regs_next (v : List (WSt n)) (h1 : stq <+: v)
    (h2 : RegOutG kq su default (WFilter P S R pw F ninc ndata) rclk
      (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) v) (h3 : nst ⊏ v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F v ninc ndata nq1 nd rclk rd v fq gq mq s :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       st_link := List.prefix_rfl
       st_ok := h2
       d_ok := (Hψ.links.d_ok.mono_next (s := ⟨nst, ninc, ndata, nq1, nd⟩) (s' := ⟨v, ninc, ndata, nq1, nd⟩) h3.isPrefix List.prefix_rfl List.prefix_rfl
                 List.prefix_rfl) },
   Hψ.full_ok, Hψ.gray_ok, Hψ.mem_ok⟩

/-- The next-state bus reaches the register bank. -/
theorem int_next_regs (v : List (WNext α n)) (h1 : nd <+: v)
    (h2 : CombOut (nextDep α ⟨nst, ninc, ndata, nq1, nd⟩) (nextFun α) (nextLen α ⟨nst, ninc, ndata, nq1, nd⟩) dmin dmax v)
    (h3 : rd ⊏ v) :
    Psi lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc crn sclk sd sorc F nst ninc ndata nq1 v rclk v stq fq gq mq s :=
  ⟨Hψ.clk, Hψ.inc, Hψ.data, Hψ.rgray, Hψ.orc, Hψ.gray_q, Hψ.full_q, Hψ.mem_q, Hψ.crn_ok,
   { Hψ.links with
       d_link := List.prefix_rfl
       d_ok := (h2.mono_next (s := ⟨nst, ninc, ndata, nq1, nd⟩) (s' := ⟨nst, ninc, ndata, nq1, v⟩) List.prefix_rfl List.prefix_rfl List.prefix_rfl
                 List.prefix_rfl)
       st_ok := Hψ.links.st_ok.mono_bus List.prefix_rfl h3.isPrefix },
   (let ⟨q, hq, e⟩ := Hψ.full_ok; ⟨q, hq.mono_bus List.prefix_rfl h3.isPrefix, e⟩),
   Hψ.gray_ok.mono_bus List.prefix_rfl h3.isPrefix, Hψ.mem_ok.mono_bus List.prefix_rfl h3.isPrefix⟩

end Cases

/-- **Step part.** -/
theorem refines_ψ (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) :
    wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc ⊑_{ψ lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc} writeDomainF α n lat stl su kq P S R pw := by
  intro i s Hψ
  obtain ⟨csrc, ⟨sclk, sd, sorc, sq⟩, F, ⟨nst, ninc, ndata, nq1, nd⟩, ⟨rclk, rd, crn, stq, fq, gq, mq⟩⟩ := i
  dsimp only [ψ] at Hψ
  constructor
  · -- Input rules
    intro ident mid_i v Hrule
    obtain ⟨csrc', ⟨sclk', sd', sorc', sq'⟩, F', ⟨nst', ninc', ndata', nq1', nd'⟩, ⟨rclk', rd', crn', stq', fq', gq', mq'⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs (wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [wdomTimed] at Hcontains
    rcases Hcontains with h | h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, NextSt.mk.injEq, RegSt.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact ⟨_, _, spec_in_rgray s _ (by rw [← Hψ.rgray]; assumption), existSR_reflexive, in_rgray Hψ _ ‹_›⟩
    · exact ⟨_, _, spec_in_orc s _ (by rw [← Hψ.orc]; assumption), existSR_reflexive, in_orc Hψ _ ‹_›⟩
    · exact ⟨_, _, spec_in_clk s _ (by rw [← Hψ.clk]; assumption), existSR_reflexive, in_clk Hψ _ ‹_›⟩
    · exact ⟨_, _, spec_in_inc s _ (by rw [← Hψ.inc]; assumption), existSR_reflexive, in_inc Hψ _ ‹_›⟩
    · exact ⟨_, _, spec_in_data s _ (by rw [← Hψ.data]; assumption), existSR_reflexive, in_data Hψ _ ‹_›⟩
  · -- Output rules
    intro ident mid_i v Hrule
    obtain ⟨csrc', ⟨sclk', sd', sorc', sq'⟩, F', ⟨nst', ninc', ndata', nq1', nd'⟩, ⟨rclk', rd', crn', stq', fq', gq', mq'⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs (wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [wdomTimed] at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, NextSt.mk.injEq, RegSt.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · have hc := h.imp (fun q hq => And.intro (Hψ.reg_of hPg hpwg hRg hq.1) hq.2)
      exact ⟨s, _, existSR_reflexive, spec_out_full s _ (by rw [Hψ.full_q]; assumption)
        (out_full_spec Hψ hP1 hP2 hS hdd hR _ hc), out_full Hψ _ hc⟩
    · have hc := Hψ.busreg_of hPg hpwg hRg h
      exact ⟨s, _, existSR_reflexive, spec_out_gray s _ (by rw [Hψ.gray_q]; assumption)
        (out_gray_spec Hψ hP1 hP2 hS hdd hR _ hc), out_gray Hψ _ hc⟩
    · have hc := Hψ.mem_of hPg hpwg hRg h
      exact ⟨s, _, existSR_reflexive, spec_out_mem s _ (by rw [Hψ.mem_q]; assumption)
        (out_mem_spec Hψ hP1 hP2 hS hdd hR _ hc), out_mem Hψ _ hc⟩
  · -- Internal rules
    intro rule mid_i Hin Hrule
    obtain ⟨csrc', ⟨sclk', sd', sorc', sq'⟩, F', ⟨nst', ninc', ndata', nq1', nd'⟩, ⟨rclk', rd', crn', stq', fq', gq', mq'⟩⟩ := mid_i
    simp only [wdomTimed, List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h
    all_goals subst h
    all_goals simp only [forall_const, and_true, not_true_eq_false, false_implies] at Hrule
    all_goals obtain ⟨⟨c0, ⟨c1, c2, c3, c3'⟩, c4, ⟨c5, c6, c7, c8, c9⟩,
      ⟨c10, c11, c12, c13, c14, c15, c16⟩⟩, out, Hrule⟩ := Hrule
    all_goals simp only [Prod.mk.injEq, NextSt.mk.injEq, RegSt.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact ⟨s, existSR_reflexive, int_clk_regs Hψ ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_clear Hψ _ ‹_› ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_clk_sync Hψ ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_sync_next Hψ ‹_› ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_regs_next Hψ _ ‹_› (Hψ.reg_of hPg hpwg hRg ‹_›) ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_next_regs Hψ _ ‹_› ‹_› ‹_›⟩

/-- **Initial part.** -/
theorem refines_initial :
    Module.refines_initial (wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc) (writeDomainF α n lat stl su kq P S R pw)
      (ψ lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc) := by
  intro i hi
  obtain ⟨csrc, ⟨sclk, sd, sorc, sq⟩, F, ⟨nst, ninc, ndata, nq1, nd⟩, ⟨rclk, rd, crn, stq, fq, gq, mq⟩⟩ := i
  simp only [wdomTimed, Prod.mk.injEq, NextSt.mk.injEq, RegSt.mk.injEq] at hi
  obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ := hi
  exact ⟨⟨[], [], [], [], [], [], [], []⟩, rfl, Psi.init⟩

/-- **The timed write domain refines the filtered write domain.**  Clock period `P` must
accommodate a clk-to-q window, the next-state delay and a setup window (`kq + su + dmax + 2`),
and likewise the synchroniser's settling time (`stl + su + dmax + 2`); the synchronous inputs
must be stable for `su + dmax + 1` instants before each edge. -/
theorem wdomTimed_refines (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (hPg : Pg ≤ P) (hpwg : pwg ≤ pw) (hRg : Rg ≤ R) :
    wdomTimed α n lat kq su stl dmin dmax Pg pwg Rg Rc ⊑ writeDomainF α n lat stl su kq P S R pw :=
  ⟨inferInstance, ψ lat kq su stl dmin dmax P S R pw Pg pwg Rg Rc, refines_ψ hP1 hP2 hS hdd hR hPg hpwg hRg, refines_initial⟩

end Graphiti.AsyncFifo.Timed
