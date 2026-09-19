/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Timed

/-!
# Delay analysis of the timed write domain

This file relates the streams flowing between the timed blocks of `Timed.lean` to the
register-level machine `wRun` of `Domains.lean`, run on the same inputs.  It is the delay
analysis of the design: with clock period `P`,

* `kq + su + dmax + 2 ≤ P`: after an edge the state register settles (`kq`), the next-state
  logic recomputes (`dmax`), and the result is stable over the setup window (`su + 1`) of the
  following edge;
* `stl + su + dmax + 2 ≤ P`: the same for the synchroniser stage, which needs `stl` to settle;
* `su + dmax + 1 ≤ S`: the synchronous inputs are stable long enough before an edge for the
  logic to have absorbed them;
* `dmin ≤ dmax`: the delay window is well formed;
* `dmax + su + 1 ≤ R`: the first edge comes after the logic has settled on its initial inputs.

Under these, `edge_value` shows that the bus loaded by the register bank at an edge, over the
whole setup window, is the next-state function of the register-level state (`wst`), and
`st_correct` that the state register equals that state whenever it has settled.  The three
outputs then satisfy the relaxed relations of `Filtered.lean` (`full_correct`,
`gray_correct`, `mem_correct`), which is what the filtered write domain promises.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Timed

open Graphiti.AsyncFifo Gray

variable {α : Type} [Inhabited α] {n : Nat}

/-- Projection of the register-level state onto the timed state register. -/
def wst (r : WReg α n) : WSt n := ⟨r.ptr, r.full, r.q2⟩

/-! ### Facts about the register-level machine -/

section Level0

variable (lat stl su : Nat) (F inc : List Bool) (data : List α) (sd : List (BitVec (n+1))) (sorc : List (Orc n))

theorem wRun_since (t : Nat) : SinceInv stl F t (wRun lat stl su F inc data sd sorc t).since := by
  induction t with
  | zero => exact SinceInv.zero _ _
  | succ t ih =>
    show SinceInv stl F (t + 1) (wstep stl (wRun lat stl su F inc data sd sorc t) (winp lat su F inc data sd sorc t)).since
    by_cases hr : (winp lat su F inc data sd sorc t).rise = true
    · rw [wstep_rise hr]; exact SinceInv.step_rise hr
    · have hr' : (winp lat su F inc data sd sorc t).rise = false := by simpa using hr
      rw [wstep_norise hr']; exact ih.step_norise hr'

/-- Before the first edge the machine holds its initial registers. -/
theorem wRun_noedge {t : Nat} (h : NoEdge F t) :
    wRun lat stl su F inc data sd sorc t = { WReg.init α n stl with since := stl + t } := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h' : NoEdge F t := fun e he => h e (by lia)
    have hr : (winp lat su F inc data sd sorc t).rise = false := h t (Nat.lt_succ_self t)
    show wstep stl (wRun lat stl su F inc data sd sorc t) (winp lat su F inc data sd sorc t) = _
    rw [wstep_norise hr, ih h']
    rfl

/-- Between edges only the `since` counter moves. -/
theorem wRun_lastEdge {e t : Nat} (h : LastEdge F e t) :
    wRun lat stl su F inc data sd sorc t =
      { wRun lat stl su F inc data sd sorc (e + 1) with since := t - e - 1 } := by
  obtain ⟨het, hre, hno⟩ := h
  induction t with
  | zero => exact absurd het (Nat.not_lt_zero e)
  | succ t ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ het) with hlt | heq
    · have hr : (winp lat su F inc data sd sorc t).rise = false := hno t hlt (Nat.lt_succ_self t)
      show wstep stl (wRun lat stl su F inc data sd sorc t) (winp lat su F inc data sd sorc t) = _
      rw [wstep_norise hr, ih hlt (fun e' h1 h2 => hno e' h1 (by lia))]
      show WReg.mk _ _ _ _ _ _ = WReg.mk _ _ _ _ _ _
      congr 1
      lia
    · subst heq
      have h0 : (wRun lat stl su F inc data sd sorc (e + 1)).since = 0 := by
        show (wstep stl (wRun lat stl su F inc data sd sorc e) (winp lat su F inc data sd sorc e)).since = 0
        rw [wstep_rise hre]
      have : e + 1 - e - 1 = 0 := by lia
      rw [this]
      generalize wRun lat stl su F inc data sd sorc (e + 1) = r at *
      obtain ⟨p, f, m, q1, q2, s⟩ := r
      simp only at h0
      subst h0
      rfl

/-- The synchroniser stage of the timed design is the first-stage register of the machine. -/
theorem syncRun_eq {sclk : List Bool} (hs : sclk <+: F) {x : Nat} (hx : x ≤ sclk.length) :
    syncRun lat su stl sclk sd sorc x =
      ⟨(wRun lat stl su F inc data sd sorc x).q1, (wRun lat stl su F inc data sd sorc x).since⟩ := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have ih := ih (by lia)
    show syncStep (syncRun lat su stl sclk sd sorc x) (syncInp lat su sclk sd sorc x) = _
    rw [ih]
    show _ = (⟨(wstep stl (wRun lat stl su F inc data sd sorc x) (winp lat su F inc data sd sorc x)).q1,
              (wstep stl (wRun lat stl su F inc data sd sorc x) (winp lat su F inc data sd sorc x)).since⟩ : SyncReg n)
    have hr : riseAt sclk x = riseAt F x := riseAt_prefix hs (by lia)
    by_cases h : (winp lat su F inc data sd sorc x).rise = true
    · rw [wstep_rise h]
      have h' : riseAt F x = true := h
      simp [syncStep, syncInp, hr, h', winp]
    · have h' : (winp lat su F inc data sd sorc x).rise = false := by simpa using h
      rw [wstep_norise h']
      have h'' : riseAt F x = false := h'
      simp [syncStep, syncInp, hr, h'']

/-- The memory of the machine holds, in each entry, the data of the last write to it. -/
theorem wRun_mem (t : Nat) (a : BitVec n) :
    ((∀ e, e < t → ¬ AsyncFifo.WriteAt lat stl su F inc data sd sorc a e) →
      (wRun lat stl su F inc data sd sorc t).mem a = default) ∧
    (∀ e, e < t → AsyncFifo.WriteAt lat stl su F inc data sd sorc a e →
      (∀ e', e < e' → e' < t → ¬ AsyncFifo.WriteAt lat stl su F inc data sd sorc a e') →
      (wRun lat stl su F inc data sd sorc t).mem a = data.getD e default) := by
  induction t with
  | zero => exact ⟨fun _ => rfl, fun e he => absurd he (Nat.not_lt_zero e)⟩
  | succ t ih =>
    by_cases hw : AsyncFifo.WriteAt lat stl su F inc data sd sorc a t
    · have hval : (wRun lat stl su F inc data sd sorc (t + 1)).mem a = data.getD t default := by
        obtain ⟨hr, hok, ha⟩ := hw
        show (wstep stl (wRun lat stl su F inc data sd sorc t) (winp lat su F inc data sd sorc t)).mem a = _
        rw [wstep_rise (i := winp lat su F inc data sd sorc t) hr]
        have hok' : ((winp lat su F inc data sd sorc t).inc && !(wRun lat stl su F inc data sd sorc t).full) = true := hok
        simp only [hok', if_true, ha.symm]
        simp [winp]
      refine ⟨fun hno => absurd hw (hno t (Nat.lt_succ_self t)), fun e he hwe hlast => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with hlt | heq
      · exact absurd hw (hlast t hlt (Nat.lt_succ_self t))
      · subst heq; exact hval
    · have hval : (wRun lat stl su F inc data sd sorc (t + 1)).mem a = (wRun lat stl su F inc data sd sorc t).mem a := by
        show (wstep stl (wRun lat stl su F inc data sd sorc t) (winp lat su F inc data sd sorc t)).mem a = _
        by_cases hr : (winp lat su F inc data sd sorc t).rise = true
        · rw [wstep_rise hr]
          by_cases hok : ((winp lat su F inc data sd sorc t).inc && !(wRun lat stl su F inc data sd sorc t).full) = true
          · have ha : ¬ (wRun lat stl su F inc data sd sorc t).ptr.setWidth n = a := fun ha => hw ⟨hr, hok, ha⟩
            simp only [hok, if_true]
            rw [if_neg (Ne.symm ha)]
          · simp only [hok, Bool.false_eq_true, if_false]
        · rw [wstep_norise (by simpa using hr)]
      refine ⟨fun hno => ?_, fun e he hwe hlast => ?_⟩
      · rw [hval]; exact ih.1 (fun e he => hno e (by lia))
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with hlt | heq
        · rw [hval]; exact ih.2 e hlt hwe (fun e' h1 h2 => hlast e' h1 (by lia))
        · subst heq; exact absurd hwe hw

end Level0

/-- Among the instants before `t` satisfying `Q`, there is a last one. -/
theorem exists_last {Q : Nat → Prop} {t : Nat} (h : ∃ e, e < t ∧ Q e) :
    ∃ e, e < t ∧ Q e ∧ ∀ e', e < e' → e' < t → ¬ Q e' := by
  induction t with
  | zero => obtain ⟨e, he, _⟩ := h; exact absurd he (Nat.not_lt_zero e)
  | succ t ih =>
    by_cases hQ : Q t
    · exact ⟨t, Nat.lt_succ_self t, hQ, fun e' h1 h2 => absurd (Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h2)) (Nat.lt_irrefl _)⟩
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

/-! ### The streams between the blocks -/

section Blocks

variable (kq su dmin dmax lat stl P S R pw : Nat)
variable (F sclk rclk : List Bool) (sd : List (BitVec (n+1))) (sorc : List (Orc n)) (inc : List Bool) (data : List α)
  (nst : List (WSt n)) (nq1 : List (BitVec (n+1))) (nd rd : List (WNext α n)) (st_q : List (WSt n))

/-- How the streams of the timed write domain are linked: the clock fork, the synchroniser's
deterministic output, the two wires of the loop between the register bank and the next-state
logic, and the two contracts along that loop. -/
structure Links : Prop where
  sclk_F : sclk <+: F
  rclk_F : rclk <+: F
  q1_sync : nq1 <+: syncOut lat su stl sclk sd sorc
  st_link : nst <+: st_q
  d_link : rd <+: nd
  st_ok : RegOutG kq su default (WFilter P S R pw F inc data) rclk (fun u => (rd.getD u default).st)
    rd.length (min rclk.length rd.length) st_q
  d_ok : CombOut (nextDep α ⟨nst, inc, data, nq1, nd⟩) (nextFun α) (nextLen α ⟨nst, inc, data, nq1, nd⟩) dmin dmax nd

variable {kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc data nst nq1 nd rd st_q}

theorem Links.lens (L : Links kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc data nst nq1 nd rd st_q) :
    rd.length ≤ nd.length ∧ nd.length ≤ nst.length ∧ nd.length ≤ inc.length ∧ nd.length ≤ data.length ∧
    nd.length ≤ nq1.length ∧ nq1.length ≤ sclk.length ∧ nq1.length ≤ sd.length + lat ∧ nq1.length ≤ sorc.length ∧
    nst.length ≤ st_q.length ∧ st_q.length ≤ rclk.length + 1 ∧ st_q.length ≤ rd.length + 1 ∧
    sclk.length ≤ F.length ∧ rclk.length ≤ F.length ∧ rd.length ≤ wLen lat F inc data sd sorc := by
  have h1 := L.d_link.length_le
  have h2 := L.d_ok.1
  have h3 := L.q1_sync.length_le
  simp only [syncOut, timeline_length, syncLen] at h3
  simp only [nextLen] at h2
  have h4 := L.st_link.length_le
  have h5 := L.st_ok.1
  have h6 := L.sclk_F.length_le
  have h7 := L.rclk_F.length_le
  unfold wLen
  omega

/-- **The edge computation.**  At a rising edge `e` (with the filter holding up to it), the bus
loaded by the register bank is, over the whole setup window, the next-state function of the
register-level state before the edge, the inputs at the edge, and the synchroniser's first
stage — provided the state register showed the register-level state at the settled instants
before `e` (`hC`). -/
theorem edge_value (L : Links kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc data nst nq1 nd rd st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R)
    {e : Nat} (hre : riseAt F e = true) (hed : e < rd.length) (hf : WFilter P S R pw F inc data (e + 1))
    (hC : ∀ x, x ≤ e → x < st_q.length → WFilter P S R pw F inc data x → Settled kq rclk x →
      st_q.getD x default = wst (wRun lat stl su F inc data sd sorc x)) :
    ∀ u, e - su - 1 ≤ u → u ≤ e → rd.getD u default =
      wNext α (wst (wRun lat stl su F inc data sd sorc e)) (inc.getD e false) (data.getD e default)
        (wRun lat stl su F inc data sd sorc e).q1 := by
  intro u hu1 hu2
  obtain ⟨hokF, hinc, hdata, hres, hpul⟩ := hf
  have heR : R ≤ e := hres e (Nat.lt_succ_self e) hre
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14⟩ := L.lens
  -- the dependency cone of the next-state logic is constant over the window
  have hdep : ∀ y, e - su - 1 - dmax ≤ y → y ≤ e - dmin →
      nextDep α ⟨nst, inc, data, nq1, nd⟩ y =
        (wst (wRun lat stl su F inc data sd sorc e), inc.getD e false, data.getD e default,
         (wRun lat stl su F inc data sd sorc e).q1) := by
    intro y hy1 hy2
    have hye : y ≤ e := by lia
    have hstate : wst (wRun lat stl su F inc data sd sorc y) = wst (wRun lat stl su F inc data sd sorc e) ∧
        (wRun lat stl su F inc data sd sorc y).q1 = (wRun lat stl su F inc data sd sorc e).q1 ∧
        stl ≤ (wRun lat stl su F inc data sd sorc y).since ∧ Settled kq rclk y := by
      by_cases hno : NoEdge F e
      · have hnoy : NoEdge F y := fun e' he' => hno e' (by lia)
        rw [wRun_noedge _ _ _ _ _ _ _ _ hnoy, wRun_noedge _ _ _ _ _ _ _ _ hno]
        exact ⟨rfl, rfl, by show stl ≤ stl + y; lia, Or.inl ((NoEdge_congr L.rclk_F (by lia)).mpr hnoy)⟩
      · obtain ⟨e₀, he₀⟩ := exists_lastEdge hno
        have hP := hokF e₀ e he₀.1 (Nat.lt_succ_self e) he₀.2.1 hre
        have he₀y : LastEdge F e₀ y := ⟨by lia, he₀.2.1, fun e' h1 h2 => he₀.2.2 e' h1 (by lia)⟩
        rw [wRun_lastEdge _ _ _ _ _ _ _ _ he₀y, wRun_lastEdge _ _ _ _ _ _ _ _ he₀]
        exact ⟨rfl, rfl, by show stl ≤ y - e₀ - 1; lia,
          Or.inr ⟨e₀, (LastEdge_congr L.rclk_F (by lia)).mpr he₀y, by lia⟩⟩
    obtain ⟨hst, hq1, hsince, hset⟩ := hstate
    have hf_y : WFilter P S R pw F inc data y :=
      ⟨hokF.mono (by lia), hinc.mono (by lia), hdata.mono (by lia), hres.mono (by lia), hpul.mono (by lia)⟩
    have c1 : nst.getD y default = wst (wRun lat stl su F inc data sd sorc e) := by
      rw [L.st_link.getD_eq_left (by lia), hC y hye (by lia) hf_y hset, hst]
    have c2 : inc.getD y false = inc.getD e false := (hinc e (Nat.lt_succ_self e) hre) y (by lia) hye
    have c3 : data.getD y default = data.getD e default := (hdata e (Nat.lt_succ_self e) hre) y (by lia) hye
    have c4 : nq1.getD y 0 = (wRun lat stl su F inc data sd sorc e).q1 := by
      rw [L.q1_sync.getD_eq_left (by lia)]
      unfold syncOut
      rw [timeline_getD _ (by unfold syncLen; omega)]
      rw [syncRun_eq lat stl su F inc data sd sorc L.sclk_F (by lia)]
      simp only
      rw [if_neg (by lia), hq1]
    simp only [nextDep]
    rw [c1, c2, c3, c4]
  rw [L.d_link.getD_eq_left (by lia)]
  have hlen : u - dmin < nextLen α ⟨nst, inc, data, nq1, nd⟩ := by
    simp only [nextLen]; omega
  have hcomb := L.d_ok.2 u (by lia) (by lia) ⟨hlen, fun y hy1 hy2 => by
    rw [hdep y (by lia) (by lia), hdep (u - dmin) (by lia) (by lia)]⟩
  rw [hcomb, hdep (u - dmax) (by lia) (by lia)]
  rfl

/-- A register loaded from the bus shows the register-level state whenever it has settled. -/
theorem reg_value (L : Links kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc data nst nq1 nd rd st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R)
    {q : List (WSt n)} (hq : RegOutG kq su default (WFilter P S R pw F inc data) rclk
      (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q)
    {t : Nat} (ht : t < q.length) (hf : WFilter P S R pw F inc data t) (hs : Settled kq rclk t)
    (hC : ∀ x, x < t → x < st_q.length → WFilter P S R pw F inc data x → Settled kq rclk x →
      st_q.getD x default = wst (wRun lat stl su F inc data sd sorc x)) :
    q.getD t default = wst (wRun lat stl su F inc data sd sorc t) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14⟩ := L.lens
  have hql := hq.1
  obtain ⟨h1, h2⟩ := hq.2 t ht hf
  rcases hs with hno | ⟨e, he, hk⟩
  · rw [h1 hno, wRun_noedge _ _ _ _ _ _ _ _ ((NoEdge_congr L.rclk_F (by omega)).mp hno)]; rfl
  · have he1 := he.1
    have hreF : riseAt F e = true := by rw [← riseAt_prefix L.rclk_F (by omega)]; exact he.2.1
    have heF : LastEdge F e t := (LastEdge_congr L.rclk_F (by omega)).mp he
    have hf' : WFilter P S R pw F inc data (e + 1) := ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.1.mono (by lia), hf.2.2.2.2.mono (by lia)⟩
    have hed : e < rd.length := by omega
    have hev := edge_value L hP1 hP2 hS hdd hR hreF hed hf' (fun x hx hxl hfx hsx => hC x (by lia) hxl hfx hsx)
    rw [h2 e he ⟨hed, fun u hu1 hu2 => by
      show (rd.getD u default).st = (rd.getD e default).st
      rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]⟩ hk]
    show (rd.getD e default).st = _
    rw [hev e (by lia) (Nat.le_refl e), wRun_lastEdge _ _ _ _ _ _ _ _ heF]
    have hs : stl ≤ (wRun lat stl su F inc data sd sorc e).since :=
      (wRun_since lat stl su F inc data sd sorc e).settled hreF (by lia) (hf.1.mono (by lia))
    show (wNext α _ _ _ _).st = wst (wstep stl (wRun lat stl su F inc data sd sorc e) (winp lat su F inc data sd sorc e))
    rw [wstep_rise (i := winp lat su F inc data sd sorc e) hreF]
    simp [wNext, wst, winp, hs]

/-- **The state register is right.** -/
theorem st_correct (L : Links kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc data nst nq1 nd rd st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R) :
    ∀ t, t < st_q.length → WFilter P S R pw F inc data t → Settled kq rclk t →
      st_q.getD t default = wst (wRun lat stl su F inc data sd sorc t) := by
  have key : ∀ T t, t < T → t < st_q.length → WFilter P S R pw F inc data t → Settled kq rclk t →
      st_q.getD t default = wst (wRun lat stl su F inc data sd sorc t) := by
    intro T
    induction T with
    | zero => intro t ht; exact absurd ht (Nat.not_lt_zero t)
    | succ T ih =>
      intro t ht htl hf hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with h | h
      · exact ih t h htl hf hs
      · subst h
        exact reg_value L hP1 hP2 hS hdd hR L.st_ok htl hf hs (fun x hx => ih x hx)
  exact fun t => key (t + 1) t (Nat.lt_succ_self t)

/-! ### The outputs -/

theorem full_correct (L : Links kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc data nst nq1 nd rd st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R)
    {full_q : List Bool}
    (hq : ∃ q, RegOutG kq su default (WFilter P S R pw F inc data) rclk
        (fun u => (rd.getD u default).st) rd.length (min rclk.length rd.length) q ∧
      full_q = q.map (fun st => st.full)) :
    WFullF lat stl su kq P S R pw F inc data sd sorc full_q := by
  obtain ⟨q, hq, rfl⟩ := hq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14⟩ := L.lens
  have hql := hq.1
  refine ⟨by simp only [List.length_map]; omega, fun t ht hf hs => ?_⟩
  simp only [List.length_map] at ht
  have hs' : Settled kq rclk t := (Settled_congr L.rclk_F (by omega)).mpr hs
  have hv := reg_value L hP1 hP2 hS hdd hR hq ht hf hs' (fun x _ => st_correct L hP1 hP2 hS hdd hR x)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht]
  simp only [Option.map_some, Option.getD_some] at hv ⊢
  rw [hv]; rfl

theorem gray_correct (L : Links kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc data nst nq1 nd rd st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R)
    {gray_q : List (BitVec (n+1))}
    (hq : BusRegOutG kq su (WFilter P S R pw F inc data) rclk (fun u => (rd.getD u default).gnext)
      rd.length (min rclk.length rd.length) gray_q) :
    WGrayF lat stl su kq P S R pw F inc data sd sorc gray_q := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14⟩ := L.lens
  obtain ⟨hreg, hwin⟩ := hq
  have hql := hreg.1
  -- the settled value
  have hval : ∀ t, t < gray_q.length → WFilter P S R pw F inc data t → Settled kq rclk t →
      gray_q.getD t default = gray (wRun lat stl su F inc data sd sorc t).ptr := by
    intro t ht hf hs
    obtain ⟨h1, h2⟩ := hreg.2 t ht hf
    rcases hs with hno | ⟨e, he, hk⟩
    · rw [h1 hno, wRun_noedge _ _ _ _ _ _ _ _ ((NoEdge_congr L.rclk_F (by omega)).mp hno)]
      show (0#(n+1)) = gray (0#(n+1))
      rw [gray_zero]
    · have he1 := he.1
      have hreF : riseAt F e = true := by rw [← riseAt_prefix L.rclk_F (by omega)]; exact he.2.1
      have heF : LastEdge F e t := (LastEdge_congr L.rclk_F (by omega)).mp he
      have hf' : WFilter P S R pw F inc data (e + 1) := ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.1.mono (by lia), hf.2.2.2.2.mono (by lia)⟩
      have hed : e < rd.length := by omega
      have hev := edge_value L hP1 hP2 hS hdd hR hreF hed hf' (fun x _ hxl hfx hsx => st_correct L hP1 hP2 hS hdd hR x hxl hfx hsx)
      rw [h2 e he ⟨hed, fun u hu1 hu2 => by
        show (rd.getD u default).gnext = (rd.getD e default).gnext
        rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]⟩ hk]
      show (rd.getD e default).gnext = _
      rw [hev e (by lia) (Nat.le_refl e), wRun_lastEdge _ _ _ _ _ _ _ _ heF]
      show (wNext α _ _ _ _).gnext = gray (wstep stl (wRun lat stl su F inc data sd sorc e) (winp lat su F inc data sd sorc e)).ptr
      rw [wstep_rise (i := winp lat su F inc data sd sorc e) hreF]
      simp [wNext, wst, winp]
  refine ⟨by omega, fun t ht hf => ⟨fun hs => hval t ht hf ((Settled_congr L.rclk_F (by omega)).mpr hs),
    fun e he hk i => ?_⟩⟩
  show (gray_q.getD t 0#(n+1)).getLsbD i = _ ∨ (gray_q.getD t 0#(n+1)).getLsbD i = _
  have he1 := he.1
  have he' : LastEdge rclk e t := (LastEdge_congr L.rclk_F (by omega)).mpr he
  have hreF := he.2.1
  have hed : e < rd.length := by omega
  have hf' : WFilter P S R pw F inc data (e + 1) := ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.1.mono (by lia), hf.2.2.2.2.mono (by lia)⟩
  have hev := edge_value L hP1 hP2 hS hdd hR hreF hed hf' (fun x _ hxl hfx hsx => st_correct L hP1 hP2 hS hdd hR x hxl hfx hsx)
  -- every edge before `t` showed the next-state logic settled, which is what the glitch-free
  -- clause needs: a violated edge would have left the register unsettled now
  have hclean : CleanEdges rclk (fun u => (rd.getD u default).gnext) rd.length su t := by
    intro e2 he2 hr2
    have hreF2 : riseAt F e2 = true := by rw [← riseAt_prefix L.rclk_F (by omega)]; exact hr2
    have hed2 : e2 < rd.length := by omega
    have hf2 : WFilter P S R pw F inc data (e2 + 1) :=
      ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.1.mono (by lia),
       hf.2.2.2.2.mono (by lia)⟩
    have hev2 := edge_value L hP1 hP2 hS hdd hR hreF2 hed2 hf2
      (fun x _ hxl hfx hsx => st_correct L hP1 hP2 hS hdd hR x hxl hfx hsx)
    exact ⟨hed2, fun u hu1 hu2 => by
      show (rd.getD u default).gnext = (rd.getD e2 default).gnext
      rw [hev2 u hu1 hu2, hev2 e2 (by lia) (Nat.le_refl e2)]⟩
  rcases hwin t ht hf hclean e he' hk i with h | h
  · left
    rw [h]
    show ((rd.getD e default).gnext).getLsbD i = _
    rw [hev e (by lia) (Nat.le_refl e), wRun_lastEdge _ _ _ _ _ _ _ _ he]
    show ((wNext α _ _ _ _).gnext).getLsbD i =
      (gray (wstep stl (wRun lat stl su F inc data sd sorc e) (winp lat su F inc data sd sorc e)).ptr).getLsbD i
    rw [wstep_rise (i := winp lat su F inc data sd sorc e) hreF]
    simp [wNext, wst, winp]
  · right
    rw [h]
    have hse : Settled kq rclk e :=
      settled_at_edge ((hf.1.mono (by lia)).congr L.rclk_F (by omega)) (by lia) he'.2.1
    show (gray_q.getD e default).getLsbD i = _
    rw [hval e (by lia) ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.1.mono (by lia), hf.2.2.2.2.mono (by lia)⟩ hse]

theorem mem_correct (L : Links kq su dmin dmax lat stl P S R pw F sclk rclk sd sorc inc data nst nq1 nd rd st_q)
    (hP1 : kq + su + dmax + 2 ≤ P) (hP2 : stl + su + dmax + 2 ≤ P) (hS : su + dmax + 1 ≤ S) (hdd : dmin ≤ dmax) (hR : dmax + su + 1 ≤ R)
    {mem_q : List (BitVec n → α)}
    (hq : MemOutG kq su (WFilter P S R pw F inc data) rclk (fun u => (rd.getD u default).we)
      (fun u => (rd.getD u default).addr) (fun u => (rd.getD u default).data) rd.length
      (min rclk.length rd.length) mem_q) :
    WMemF lat stl su kq P S R pw F inc data sd sorc mem_q := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14⟩ := L.lens
  obtain ⟨hml, hmem⟩ := hq
  refine ⟨by omega, fun t ht hf a hset => ?_⟩
  -- write events of the timed design are the write events of the machine
  have hev : ∀ e, e < t → riseAt F e = true → ∀ u, e - su - 1 ≤ u → u ≤ e → rd.getD u default =
      wNext α (wst (wRun lat stl su F inc data sd sorc e)) (inc.getD e false) (data.getD e default)
        (wRun lat stl su F inc data sd sorc e).q1 := by
    intro e he hreF
    have hed : e < rd.length := by omega
    have hf' : WFilter P S R pw F inc data (e + 1) := ⟨hf.1.mono (by lia), hf.2.1.mono (by lia), hf.2.2.1.mono (by lia), hf.2.2.2.1.mono (by lia), hf.2.2.2.2.mono (by lia)⟩
    exact edge_value L hP1 hP2 hS hdd hR hreF hed hf' (fun x _ hxl hfx hsx => st_correct L hP1 hP2 hS hdd hR x hxl hfx hsx)
  have hW : ∀ e, e < t →
      (Timed.WriteEdge a rclk (fun u => (rd.getD u default).we) (fun u => (rd.getD u default).addr)
        (fun u => (rd.getD u default).data) rd.length su e ↔
       AsyncFifo.WriteAt lat stl su F inc data sd sorc a e) := by
    intro e he
    have hed : e < rd.length := by omega
    have hr : riseAt rclk e = riseAt F e := riseAt_prefix L.rclk_F (by omega)
    constructor
    · rintro ⟨hre, _, _, _, hwe, haddr⟩
      have hreF : riseAt F e = true := by rw [← hr]; exact hre
      have hev := hev e he hreF
      have hwe' : (rd.getD e default).we = true := hwe
      have haddr' : (rd.getD e default).addr = a := haddr
      rw [hev e (by lia) (Nat.le_refl e)] at hwe' haddr'
      exact ⟨hreF, hwe', haddr'⟩
    · rintro ⟨hreF, hok, haddr⟩
      have hev := hev e he hreF
      refine ⟨by rw [hr]; exact hreF,
        ⟨hed, fun u hu1 hu2 => by
          show (rd.getD u default).we = (rd.getD e default).we
          rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]⟩,
        ⟨hed, fun u hu1 hu2 => by
          show (rd.getD u default).addr = (rd.getD e default).addr
          rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]⟩,
        ⟨hed, fun u hu1 hu2 => by
          show (rd.getD u default).data = (rd.getD e default).data
          rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]⟩, ?_, ?_⟩
      · show (rd.getD e default).we = true
        rw [hev e (by lia) (Nat.le_refl e)]; exact hok
      · show (rd.getD e default).addr = a
        rw [hev e (by lia) (Nat.le_refl e)]; exact haddr
  -- every edge so far loaded a stable bus, so the register file was never written unsafely
  have hclean : CleanWrites rclk (fun u => (rd.getD u default).we) (fun u => (rd.getD u default).addr)
      (fun u => (rd.getD u default).data) rd.length su t := by
    intro e he hre
    have hreF : riseAt F e = true := by rw [← riseAt_prefix L.rclk_F (by omega)]; exact hre
    have hev := hev e he hreF
    have hed : e < rd.length := by omega
    refine ⟨⟨hed, fun u hu1 hu2 => ?_⟩, fun _ => ⟨⟨hed, fun u hu1 hu2 => ?_⟩, ⟨hed, fun u hu1 hu2 => ?_⟩⟩⟩
    · show (rd.getD u default).we = (rd.getD e default).we
      rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]
    · show (rd.getD u default).addr = (rd.getD e default).addr
      rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]
    · show (rd.getD u default).data = (rd.getD e default).data
      rw [hev u hu1 hu2, hev e (by lia) (Nat.le_refl e)]
  obtain ⟨hm1, hm2⟩ := hmem t ht hf hclean a
  obtain ⟨hr1, hr2⟩ := wRun_mem lat stl su F inc data sd sorc t a
  by_cases hex : ∃ e, e < t ∧ AsyncFifo.WriteAt lat stl su F inc data sd sorc a e
  · obtain ⟨e, he, hwe, hlast⟩ := exists_last hex
    rw [hm2 e he ((hW e he).mpr hwe) (fun e' h1 h2 hw' => hlast e' h1 h2 ((hW e' h2).mp hw')) (hset e he hwe),
      hr2 e he hwe hlast]
    show (rd.getD e default).data = _
    rw [hev e he hwe.1 e (by lia) (Nat.le_refl e)]
    rfl
  · have hno : ∀ e, e < t → ¬ AsyncFifo.WriteAt lat stl su F inc data sd sorc a e := fun e he hw => hex ⟨e, he, hw⟩
    rw [hm1 (fun e he hw => hno e he ((hW e he).mp hw)), hr1 hno]

end Blocks

end Graphiti.AsyncFifo.Timed
