/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.TimedProof

/-!
# The delay analysis of the read domain

The same argument as `TimedProof.lean` makes for the write domain, for the read domain's
blocks.  It is shorter in one place and longer in another: there is no memory to write, and
there is a read port --- a combinational path from the *other* domain's memory to the data
output, which is the one block of a clock domain whose inputs are not its own.

The shape is unchanged.  `RLinks` says how the streams between the blocks are related and what
each block promises; `edge_value` computes the bus the register bank loads at an edge from the
register-level state; `st_correct` closes the loop by induction over instants; and the three
outputs follow.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Timed

open Graphiti.AsyncFifo Gray

variable {α : Type} [Inhabited α] {n : Nat}

/-- Projection of the register-level state onto the timed state register. -/
def rst (r : RReg n) : RSt n := ⟨r.ptr, r.empty, r.q2⟩

/-! ### Facts about the register-level machine -/

section Level0

variable (lat stl su : Nat) (F inc : List Bool) (sd : List (BitVec (n+1))) (sorc : List (Orc n))

theorem rRun_since (t : Nat) : SinceInv stl F t (rRun lat stl su F inc sd sorc t).since := by
  induction t with
  | zero => exact SinceInv.zero _ _
  | succ t ih =>
    show SinceInv stl F (t + 1) (rstep stl (rRun lat stl su F inc sd sorc t) (rinp lat su F inc sd sorc t)).since
    by_cases hr : (rinp lat su F inc sd sorc t).rise = true
    · rw [rstep_rise hr]; exact SinceInv.step_rise hr
    · have hr' : (rinp lat su F inc sd sorc t).rise = false := by simpa using hr
      rw [rstep_norise hr']; exact ih.step_norise hr'

/-- Before the first edge the machine holds its initial registers. -/
theorem rRun_noedge {t : Nat} (h : NoEdge F t) :
    rRun lat stl su F inc sd sorc t = { RReg.init n stl with since := stl + t } := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h' : NoEdge F t := fun e he => h e (by lia)
    have hr : (rinp lat su F inc sd sorc t).rise = false := h t (Nat.lt_succ_self t)
    show rstep stl (rRun lat stl su F inc sd sorc t) (rinp lat su F inc sd sorc t) = _
    rw [rstep_norise hr, ih h']
    rfl

/-- Between edges only the `since` counter moves. -/
theorem rRun_lastEdge {e t : Nat} (h : LastEdge F e t) :
    rRun lat stl su F inc sd sorc t =
      { rRun lat stl su F inc sd sorc (e + 1) with since := t - e - 1 } := by
  obtain ⟨het, hre, hno⟩ := h
  induction t with
  | zero => exact absurd het (Nat.not_lt_zero e)
  | succ t ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ het) with hlt | heq
    · have hr : (rinp lat su F inc sd sorc t).rise = false := hno t hlt (Nat.lt_succ_self t)
      show rstep stl (rRun lat stl su F inc sd sorc t) (rinp lat su F inc sd sorc t) = _
      rw [rstep_norise hr, ih hlt (fun e' h1 h2 => hno e' h1 (by lia))]
      show RReg.mk _ _ _ _ _ = RReg.mk _ _ _ _ _
      congr 1
      lia
    · subst heq
      have h0 : (rRun lat stl su F inc sd sorc (e + 1)).since = 0 := by
        show (rstep stl (rRun lat stl su F inc sd sorc e) (rinp lat su F inc sd sorc e)).since = 0
        rw [rstep_rise hre]
      have : e + 1 - e - 1 = 0 := by lia
      rw [this]
      generalize rRun lat stl su F inc sd sorc (e + 1) = r at *
      obtain ⟨p, em, q1, q2, s⟩ := r
      simp only at h0
      subst h0
      rfl

/-- The synchroniser stage of the timed design is the first-stage register of the machine. -/
theorem rsyncRun_eq {sclk : List Bool} (hs : sclk <+: F) {x : Nat} (hx : x ≤ sclk.length) :
    syncRun lat su stl sclk sd sorc x =
      ⟨(rRun lat stl su F inc sd sorc x).q1, (rRun lat stl su F inc sd sorc x).since⟩ := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have ih := ih (by lia)
    show syncStep (syncRun lat su stl sclk sd sorc x) (syncInp lat su sclk sd sorc x) = _
    rw [ih]
    show _ = (⟨(rstep stl (rRun lat stl su F inc sd sorc x) (rinp lat su F inc sd sorc x)).q1,
              (rstep stl (rRun lat stl su F inc sd sorc x) (rinp lat su F inc sd sorc x)).since⟩ : SyncReg n)
    have hr : riseAt sclk x = riseAt F x := riseAt_prefix hs (by lia)
    by_cases h : (rinp lat su F inc sd sorc x).rise = true
    · rw [rstep_rise h]
      have h' : riseAt F x = true := h
      simp [syncStep, syncInp, hr, h', rinp]
    · have h' : (rinp lat su F inc sd sorc x).rise = false := by simpa using h
      rw [rstep_norise h']
      have h'' : riseAt F x = false := h'
      simp [syncStep, syncInp, hr, h'']

end Level0

/-! ### The streams between the blocks -/

section Blocks

variable (kq su dmin dmax lat stl P S R pw rdly : Nat)
variable (F sclk rclk : List Bool) (sd : List (BitVec (n+1))) (sorc : List (Orc n)) (inc : List Bool)
  (nst mst : List (RSt n)) (nq1 : List (BitVec (n+1))) (nd rd : List (RNext n))
  (rmem mem : List (BitVec n → α)) (st_q : List (RSt n))

/-- How the streams of the timed read domain are linked: the clock fork, the synchroniser's
deterministic output, the two wires of the loop between the register bank and the next-state
logic, the two the read port sees, and the two contracts along the loop. -/
structure RLinks : Prop where
  sclk_F : sclk <+: F
  rclk_F : rclk <+: F
  q1_sync : nq1 <+: syncOut lat su stl sclk sd sorc
  st_link : nst <+: st_q
  mst_link : mst <+: st_q
  mem_link : rmem <+: mem
  d_link : rd <+: nd
  st_ok : RegOutG kq su default (RFilter P S R pw F inc) rclk (fun u => (rd.getD u default).st)
    rd.length (min rclk.length rd.length) st_q
  d_ok : CombOut (rnextDep ⟨nst, inc, nq1, nd⟩) rnextFun (rnextLen ⟨nst, inc, nq1, nd⟩) dmin dmax nd

variable {kq su dmin dmax lat stl P S R pw rdly F sclk rclk sd sorc inc nst mst nq1 nd rd rmem mem st_q}

theorem RLinks.lens (L : RLinks kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc nst mst nq1 nd rd rmem mem st_q) :
    rd.length ≤ nd.length ∧ nd.length ≤ nst.length ∧ nd.length ≤ inc.length ∧
    nd.length ≤ nq1.length ∧ nq1.length ≤ sclk.length ∧ nq1.length ≤ sd.length + lat ∧
    nq1.length ≤ sorc.length ∧ nst.length ≤ st_q.length ∧ mst.length ≤ st_q.length ∧
    rmem.length ≤ mem.length ∧ st_q.length ≤ rclk.length + 1 ∧ st_q.length ≤ rd.length + 1 ∧
    sclk.length ≤ F.length ∧ rclk.length ≤ F.length ∧ rd.length ≤ rLen lat F inc sd sorc := by
  have h1 := L.d_link.length_le
  have h2 := L.d_ok.1
  have h3 := L.q1_sync.length_le
  simp only [syncOut, timeline_length, syncLen] at h3
  simp only [rnextLen] at h2
  have h4 := L.st_link.length_le
  have h4' := L.mst_link.length_le
  have h4'' := L.mem_link.length_le
  have h5 := L.st_ok.1
  have h6 := L.sclk_F.length_le
  have h7 := L.rclk_F.length_le
  unfold rLen
  omega

/-- **The edge computation.**  At a rising edge `e` (with the filter holding up to it), the bus
loaded by the register bank is, over the whole setup window, the next-state function of the
register-level state before the edge, the input at the edge, and the synchroniser's first
stage. -/
theorem redge_value (L : RLinks kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc nst mst nq1 nd rd rmem mem st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R)
    {e : Nat} (hre : riseAt F e = true) (hed : e < rd.length) (hf : RFilter P S R pw F inc (e + 1))
    (hC : ∀ x, x ≤ e → x < st_q.length → RFilter P S R pw F inc x → Settled kq rclk x →
      st_q.getD x default = rst (rRun lat stl su F inc sd sorc x)) :
    ∀ u, e - su - 1 ≤ u → u ≤ e → rd.getD u default =
      rnextFun ((rst (rRun lat stl su F inc sd sorc e)), inc.getD e false,
        (rRun lat stl su F inc sd sorc e).q1) := by
  intro u hu1 hu2
  obtain ⟨hokF, hinc, hres, hpul⟩ := hf
  have heR : R ≤ e := hres e (Nat.lt_succ_self e) hre
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩ := L.lens
  have hdep : ∀ y, e - su - 1 - dmax ≤ y → y ≤ e - dmin →
      rnextDep ⟨nst, inc, nq1, nd⟩ y =
        ((rst (rRun lat stl su F inc sd sorc e)), inc.getD e false,
         (rRun lat stl su F inc sd sorc e).q1) := by
    intro y hy1 hy2
    have hye : y ≤ e := by lia
    have hstate : rst (rRun lat stl su F inc sd sorc y) = rst (rRun lat stl su F inc sd sorc e) ∧
        (rRun lat stl su F inc sd sorc y).q1 = (rRun lat stl su F inc sd sorc e).q1 ∧
        stl ≤ (rRun lat stl su F inc sd sorc y).since ∧ Settled kq rclk y := by
      by_cases hno : NoEdge F e
      · have hnoy : NoEdge F y := fun e' he' => hno e' (by lia)
        rw [rRun_noedge _ _ _ _ _ _ _ hnoy, rRun_noedge _ _ _ _ _ _ _ hno]
        exact ⟨rfl, rfl, by show stl ≤ stl + y; lia,
          Or.inl ((NoEdge_congr L.rclk_F (by lia)).mpr hnoy)⟩
      · obtain ⟨e₀, he₀⟩ := exists_lastEdge hno
        have hP := hokF e₀ e he₀.1 (Nat.lt_succ_self e) he₀.2.1 hre
        have he₀y : LastEdge F e₀ y := ⟨by lia, he₀.2.1, fun e' h1 h2 => he₀.2.2 e' h1 (by lia)⟩
        rw [rRun_lastEdge _ _ _ _ _ _ _ he₀y, rRun_lastEdge _ _ _ _ _ _ _ he₀]
        exact ⟨rfl, rfl, by show stl ≤ y - e₀ - 1; lia,
          Or.inr ⟨e₀, (LastEdge_congr L.rclk_F (by lia)).mpr he₀y, by lia⟩⟩
    obtain ⟨hst, hq1, hsince, hset⟩ := hstate
    have hf_y : RFilter P S R pw F inc y :=
      ⟨hokF.mono (by lia), hinc.mono (by lia), hres.mono (by lia), hpul.mono (by lia)⟩
    have c1 : nst.getD y default = rst (rRun lat stl su F inc sd sorc e) := by
      rw [L.st_link.getD_eq_left (by lia), hC y hye (by lia) hf_y hset, hst]
    have c2 : inc.getD y false = inc.getD e false := (hinc e (Nat.lt_succ_self e) hre) y (by lia) hye
    have c4 : nq1.getD y 0 = (rRun lat stl su F inc sd sorc e).q1 := by
      rw [L.q1_sync.getD_eq_left (by lia)]
      unfold syncOut
      rw [timeline_getD _ (by unfold syncLen; omega)]
      rw [rsyncRun_eq lat stl su F inc sd sorc L.sclk_F (by lia)]
      simp only
      rw [if_neg (by lia), hq1]
    simp only [rnextDep]
    rw [c1, c2, c4]
  rw [L.d_link.getD_eq_left (by lia)]
  have hlen : u - dmin < rnextLen ⟨nst, inc, nq1, nd⟩ := by
    simp only [rnextLen]; omega
  have hcomb := L.d_ok.2 u (by lia) (by lia) ⟨hlen, fun y hy1 hy2 => by
    rw [hdep y (by lia) (by lia), hdep (u - dmin) (by lia) (by lia)]⟩
  rw [hcomb, hdep (u - dmax) (by lia) (by lia)]

/-- A register loaded from the bus shows the register-level state whenever it has settled. -/
theorem rreg_value (L : RLinks kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc nst mst nq1 nd rd rmem mem st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R)
    {q : List (RSt n)} (hq : RegOutG kq su default (RFilter P S R pw F inc) rclk
      (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q)
    {t : Nat} (ht : t < q.length) (hf : RFilter P S R pw F inc t) (hs : Settled kq rclk t)
    (hC : ∀ x, x < t → x < st_q.length → RFilter P S R pw F inc x → Settled kq rclk x →
      st_q.getD x default = rst (rRun lat stl su F inc sd sorc x)) :
    q.getD t default = rst (rRun lat stl su F inc sd sorc t) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩ := L.lens
  have hql := hq.1
  obtain ⟨h1, h2⟩ := hq.2 t ht hf
  rcases hs with hno | ⟨e, he, hk⟩
  · rw [h1 hno, rRun_noedge _ _ _ _ _ _ _ ((NoEdge_congr L.rclk_F (by omega)).mp hno)]; rfl
  · have he1 := he.1
    have hreF : riseAt F e = true := by rw [← riseAt_prefix L.rclk_F (by omega)]; exact he.2.1
    have heF : LastEdge F e t := (LastEdge_congr L.rclk_F (by omega)).mp he
    have hf' : RFilter P S R pw F inc (e + 1) :=
      ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.mono (by lia)⟩
    have hed : e < rd.length := by omega
    have hev := redge_value L hP1 hP2 hS hdd hR hreF hed hf'
      (fun x hx hxl hfx hsx => hC x (by lia) hxl hfx hsx)
    rw [h2 e he ⟨hed, fun u hu1 hu2 => by
      show (rd.getD u default).st = (rd.getD e default).st
      rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]⟩ hk]
    show (rd.getD e default).st = _
    rw [hev e (by lia) (Nat.le_refl e), rRun_lastEdge _ _ _ _ _ _ _ heF]
    have hsn : stl ≤ (rRun lat stl su F inc sd sorc e).since :=
      (rRun_since lat stl su F inc sd sorc e).settled hreF (by lia) (hf.1.mono (by lia))
    show (rnextFun _).st = rst (rstep stl (rRun lat stl su F inc sd sorc e) (rinp lat su F inc sd sorc e))
    rw [rstep_rise (i := rinp lat su F inc sd sorc e) hreF]
    simp [rnextFun, rNext, rst, rinp, hsn]

/-- **The state register is right.** -/
theorem rst_correct (L : RLinks kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc nst mst nq1 nd rd rmem mem st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) :
    ∀ t, t < st_q.length → RFilter P S R pw F inc t → Settled kq rclk t →
      st_q.getD t default = rst (rRun lat stl su F inc sd sorc t) := by
  have key : ∀ T t, t < T → t < st_q.length → RFilter P S R pw F inc t → Settled kq rclk t →
      st_q.getD t default = rst (rRun lat stl su F inc sd sorc t) := by
    intro T
    induction T with
    | zero => intro t ht; exact absurd ht (Nat.not_lt_zero t)
    | succ T ih =>
      intro t ht htl hf hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with h | h
      · exact ih t h htl hf hs
      · subst h
        exact rreg_value L hP1 hP2 hS hdd hR L.st_ok htl hf hs (fun x hx => ih x hx)
  exact fun t => key (t + 1) t (Nat.lt_succ_self t)

/-! ### The outputs -/

theorem rempty_correct (L : RLinks kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc nst mst nq1 nd rd rmem mem st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) {empty_q : List Bool}
    (hq : ∃ q, RegOutG kq su default (RFilter P S R pw F inc) rclk
      (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q ∧
      empty_q = q.map (fun st => st.empty)) :
    REmptyF lat stl su kq P S R pw F inc sd sorc empty_q := by
  obtain ⟨q, hq, rfl⟩ := hq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩ := L.lens
  have hql := hq.1
  refine ⟨by simp only [List.length_map]; omega, fun t ht hf hs => ?_⟩
  simp only [List.length_map] at ht
  have hs' : Settled kq rclk t := (Settled_congr L.rclk_F (by omega)).mpr hs
  have hv := rreg_value L hP1 hP2 hS hdd hR hq ht hf hs'
    (fun x _ => rst_correct L hP1 hP2 hS hdd hR x)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht]
  simp only [Option.map_some, Option.getD_some] at hv ⊢
  rw [hv]; rfl

theorem rgray_correct (L : RLinks kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc nst mst nq1 nd rd rmem mem st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) {gray_q : List (BitVec (n+1))}
    (hq : BusRegOutG kq su (RFilter P S R pw F inc) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min rclk.length rd.length) gray_q) :
    RGrayF lat stl su kq P S R pw F inc sd sorc gray_q := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩ := L.lens
  obtain ⟨hreg, hwin⟩ := hq
  have hql := hreg.1
  have hval : ∀ t, t < gray_q.length → RFilter P S R pw F inc t → Settled kq rclk t →
      gray_q.getD t default = gray (rRun lat stl su F inc sd sorc t).ptr := by
    intro t ht hf hs
    obtain ⟨h1, h2⟩ := hreg.2 t ht hf
    rcases hs with hno | ⟨e, he, hk⟩
    · rw [h1 hno, rRun_noedge _ _ _ _ _ _ _ ((NoEdge_congr L.rclk_F (by omega)).mp hno)]
      show (0#(n+1)) = gray (0#(n+1))
      rw [gray_zero]
    · have he1 := he.1
      have hreF : riseAt F e = true := by rw [← riseAt_prefix L.rclk_F (by omega)]; exact he.2.1
      have heF : LastEdge F e t := (LastEdge_congr L.rclk_F (by omega)).mp he
      have hf' : RFilter P S R pw F inc (e + 1) :=
        ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.mono (by lia)⟩
      have hed : e < rd.length := by omega
      have hev := redge_value L hP1 hP2 hS hdd hR hreF hed hf'
        (fun x _ hxl hfx hsx => rst_correct L hP1 hP2 hS hdd hR x hxl hfx hsx)
      rw [h2 e he ⟨hed, fun u hu1 hu2 => by
        show (rd.getD u default).gnext = (rd.getD e default).gnext
        rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]⟩ hk]
      show (rd.getD e default).gnext = _
      rw [hev e (by lia) (Nat.le_refl e), rRun_lastEdge _ _ _ _ _ _ _ heF]
      show (rnextFun _).gnext = gray (rstep stl (rRun lat stl su F inc sd sorc e) (rinp lat su F inc sd sorc e)).ptr
      rw [rstep_rise (i := rinp lat su F inc sd sorc e) hreF]
      simp [rnextFun, rNext, rst, rinp]
  refine ⟨by omega, fun t ht hf => ⟨fun hs => hval t ht hf ((Settled_congr L.rclk_F (by omega)).mpr hs),
    fun e he hk i => ?_⟩⟩
  show (gray_q.getD t 0#(n+1)).getLsbD i = _ ∨ (gray_q.getD t 0#(n+1)).getLsbD i = _
  have he1 := he.1
  have he' : LastEdge rclk e t := (LastEdge_congr L.rclk_F (by omega)).mpr he
  have hreF := he.2.1
  have hed : e < rd.length := by omega
  have hf' : RFilter P S R pw F inc (e + 1) :=
    ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.mono (by lia)⟩
  have hev := redge_value L hP1 hP2 hS hdd hR hreF hed hf'
    (fun x _ hxl hfx hsx => rst_correct L hP1 hP2 hS hdd hR x hxl hfx hsx)
  have hclean : CleanEdges rclk (fun u => (rd.getD u default).gnext) rd.length su t := by
    intro e2 he2 hr2
    have hreF2 : riseAt F e2 = true := by rw [← riseAt_prefix L.rclk_F (by omega)]; exact hr2
    have hed2 : e2 < rd.length := by omega
    have hf2 : RFilter P S R pw F inc (e2 + 1) :=
      ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.mono (by lia)⟩
    have hev2 := redge_value L hP1 hP2 hS hdd hR hreF2 hed2 hf2
      (fun x _ hxl hfx hsx => rst_correct L hP1 hP2 hS hdd hR x hxl hfx hsx)
    exact ⟨hed2, fun u hu1 hu2 => by
      show (rd.getD u default).gnext = (rd.getD e2 default).gnext
      rw [hev2 u hu1 hu2, hev2 e2 (by lia) (Nat.le_refl e2)]⟩
  rcases hwin t ht hf hclean e he' hk i with h | h
  · left
    rw [h]
    show ((rd.getD e default).gnext).getLsbD i = _
    rw [hev e (by lia) (Nat.le_refl e), rRun_lastEdge _ _ _ _ _ _ _ he]
    show ((rnextFun _).gnext).getLsbD i =
      (gray (rstep stl (rRun lat stl su F inc sd sorc e) (rinp lat su F inc sd sorc e)).ptr).getLsbD i
    rw [rstep_rise (i := rinp lat su F inc sd sorc e) hreF]
    simp [rnextFun, rNext, rst, rinp]
  · right
    rw [h]
    have hse : Settled kq rclk e :=
      settled_at_edge ((hf.1.mono (by lia)).congr L.rclk_F (by omega)) (by lia) he'.2.1
    show (gray_q.getD e default).getLsbD i = _
    rw [hval e (by lia) ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia),
      hf.2.2.2.mono (by lia)⟩ hse]

/-- **The read data is right.**  The read port is combinational and has its own delay window
`[0, rdly]`, so it needs two things a register does not: the address settled `rdly` longer than
a register would (`Settled (kq + rdly)`), and the entry it addresses held over that window
(`MemHold rdly`) --- the one place a read-domain output depends on the write domain's timing,
which is why `MemHold` is discharged in `Invariant.lean` beside `mem_read`.

The address is stable over the window because the state register only moves at an edge, and
`Settled (kq + rdly)` puts the last edge at least `kq` instants before the start of the window;
`0 < kq` is what makes "at least `kq` before" mean "strictly before". -/
theorem rdata_correct (L : RLinks kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc nst mst nq1 nd rd rmem mem st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S)
    (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) (hkq : 0 < kq)
    {rdmin rdmax : Nat} (hrr : rdmin ≤ rdmax) (hrw : rdmax ≤ rdly) {v : List α}
    (hq : ReadOut rdmin rdmax (fun u => (mst.getD u default).ptr.setWidth n)
      (fun u => rmem.getD u (fun _ => default)) (min mst.length rmem.length) v) :
    RDataF lat stl su kq rdly P S R pw F inc sd sorc mem v := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩ := L.lens
  obtain ⟨hlen, hval⟩ := hq
  refine ⟨by unfold rDataLen; omega, fun t htd ht hf hs hmh => ?_⟩
  have hsm : t < mst.length := by omega
  have hs' : Settled (kq + rdly) rclk t := (Settled_congr L.rclk_F (by omega)).mpr hs
  -- Over the read window the register-level pointer does not move, and the state register
  -- shows it, because the last edge is at least `kq` instants before the window starts.
  have hstate : ∀ u, t - rdly ≤ u → u ≤ t →
      mst.getD u default = rst (rRun lat stl su F inc sd sorc u) ∧
      (rRun lat stl su F inc sd sorc u).ptr = (rRun lat stl su F inc sd sorc t).ptr := by
    intro u hu1 hu2
    have hful : RFilter P S R pw F inc u :=
      ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.mono (by lia)⟩
    have key : Settled kq rclk u ∧
        (rRun lat stl su F inc sd sorc u).ptr = (rRun lat stl su F inc sd sorc t).ptr := by
      rcases hs' with hno | ⟨e, he, hk⟩
      · have hnoF : NoEdge F t := (NoEdge_congr L.rclk_F (by omega)).mp hno
        have hnou : NoEdge F u := fun e' he' => hnoF e' (by lia)
        refine ⟨Or.inl (fun e' he' => hno e' (by lia)), ?_⟩
        rw [rRun_noedge _ _ _ _ _ _ _ hnou, rRun_noedge _ _ _ _ _ _ _ hnoF]
      · have he1 := he.1
        have heu : LastEdge rclk e u := ⟨by lia, he.2.1, fun e' h1 h2 => he.2.2 e' h1 (by lia)⟩
        refine ⟨Or.inr ⟨e, heu, by lia⟩, ?_⟩
        rw [rRun_lastEdge _ _ _ _ _ _ _ ((LastEdge_congr L.rclk_F (by omega)).mp heu),
            rRun_lastEdge _ _ _ _ _ _ _ ((LastEdge_congr L.rclk_F (by omega)).mp he)]
    refine ⟨?_, key.2⟩
    rw [L.mst_link.getD_eq_left (by omega)]
    exact rst_correct L hP1 hP2 hS hdd hR u (by omega) hful key.1
  have hmst : mst.getD t default = rst (rRun lat stl su F inc sd sorc t) :=
    (hstate t (Nat.sub_le _ _) (Nat.le_refl t)).1
  have haddr : (mst.getD t default).ptr.setWidth n = (rRun lat stl su F inc sd sorc t).ptr.setWidth n := by
    rw [hmst]; rfl
  have hstab : StableOn (fun u => (mst.getD u default).ptr.setWidth n)
      (min mst.length rmem.length) (t - rdmax) (t - rdmin) := by
    refine ⟨by omega, fun u hu1 hu2 => ?_⟩
    show (mst.getD u default).ptr.setWidth n = (mst.getD (t - rdmin) default).ptr.setWidth n
    rw [(hstate u (by omega) (by omega)).1, (hstate (t - rdmin) (by omega) (by omega)).1]
    show ((rRun lat stl su F inc sd sorc u).ptr).setWidth n
        = ((rRun lat stl su F inc sd sorc (t - rdmin)).ptr).setWidth n
    rw [(hstate u (by omega) (by omega)).2, (hstate (t - rdmin) (by omega) (by omega)).2]
  -- the address the port latches is the one the state register shows now
  have haddr' : (mst.getD (t - rdmin) default).ptr.setWidth n =
      (rRun lat stl su F inc sd sorc t).ptr.setWidth n := by
    rw [(hstate (t - rdmin) (by omega) (by omega)).1]
    show ((rRun lat stl su F inc sd sorc (t - rdmin)).ptr).setWidth n = _
    rw [(hstate (t - rdmin) (by omega) (by omega)).2]
  have hhold : ∀ u, t - rdmax ≤ u → u ≤ t - rdmin →
      rmem.getD u (fun _ => default) ((mst.getD (t - rdmin) default).ptr.setWidth n) =
      rmem.getD (t - rdmin) (fun _ => default) ((mst.getD (t - rdmin) default).ptr.setWidth n) := by
    intro u hu1 hu2
    rw [haddr', L.mem_link.getD_eq_left (by omega), L.mem_link.getD_eq_left (by omega)]
    rw [hmh u (by omega) (by omega), hmh (t - rdmin) (by omega) (by omega)]
  have h : v.getD t default =
      rmem.getD (t - rdmin) (fun _ => default) ((mst.getD (t - rdmin) default).ptr.setWidth n) :=
    hval t (by omega) ht hstab hhold
  have hmem : ∀ u, u ≤ t → rmem.getD u (fun _ => default) = mem.getD u (fun _ => default) :=
    fun u hu => L.mem_link.getD_eq_left (by omega) _
  rw [h, haddr', hmem (t - rdmin) (by omega), hmh (t - rdmin) (by omega) (by omega)]
  show (mem.getD t (fun _ => default)) ((rRun lat stl su F inc sd sorc t).ptr.setWidth n) = _
  rfl

end Blocks

end Graphiti.AsyncFifo.Timed
