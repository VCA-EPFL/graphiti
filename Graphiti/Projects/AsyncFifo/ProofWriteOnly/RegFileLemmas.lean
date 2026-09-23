/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.EnRegTiming
import Graphiti.Projects.AsyncFifo.components.level5.RegFile

/-! # `RegFile`: the lemmas

Facts about the definitions in `components/level5/RegFile.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.RegFile
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff Graphiti.AsyncFifo.EnReg

@[drenv] theorem menv_unpack2A : menv.find? "unpack2A" = .some ⟨_, unpack2A⟩ := rfl
@[drenv] theorem menv_fork2 : menv.find? "fork2" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem menv_fork3 : menv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem menv_fork4 : menv.find? "fork4" = .some ⟨_, fork4⟩ := rfl
@[drenv] theorem menv_not1 : menv.find? "not1" = .some ⟨_, gate1 not⟩ := rfl
@[drenv] theorem menv_and2 : menv.find? "and2" = .some ⟨_, gate2 and2⟩ := rfl
@[drenv] theorem menv_cell : menv.find? "cell" = .some ⟨_, enSpec⟩ := rfl
@[drenv] theorem menv_packMem : menv.find? "packMem" = .some ⟨_, packMem⟩ := rfl


@[simp] theorem bitsA_length (i : Nat) (addr : List (BitVec 2)) :
    (bitsA i addr).length = addr.length := by simp [bitsA]

theorem bitsA_mono {i : Nat} {a a' : List (BitVec 2)} (h : a <+: a') : bitsA i a <+: bitsA i a' :=
  h.map _

theorem bitsA_getD_all (i : Nat) (addr : List (BitVec 2)) (u : Nat) :
    (bitsA i addr).getD u false = (addr.getD u 0#2).getLsbD i := by
  by_cases h : u < addr.length
  · simp [bitsA, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [bitsA]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

@[simp] theorem packMemOut_length (q0 q1 q2 q3 : List Bool) :
    (packMemOut q0 q1 q2 q3).length =
      min (min q0.length q1.length) (min q2.length q3.length) - 3 := timeline_length _ _

theorem packMemOut_mono {q0 q0' q1 q1' q2 q2' q3 q3' : List Bool} (h0 : q0 <+: q0')
    (h1 : q1 <+: q1') (h2 : q2 <+: q2') (h3 : q3 <+: q3') :
    packMemOut q0 q1 q2 q3 <+: packMemOut q0' q1' q2' q3' := by
  have := h0.length_le; have := h1.length_le; have := h2.length_le; have := h3.length_le
  apply timeline_mono (by omega)
  intro t ht
  have ht' : t < min (min q0.length q1.length) (min q2.length q3.length) := by omega
  simp only [Nat.lt_min] at ht'
  rw [h0.getD_eq_left (by omega), h1.getD_eq_left (by omega), h2.getD_eq_left (by omega),
    h3.getD_eq_left (by omega)]

theorem W_bit_mono {i k : Nat} {addr addr' : List (BitVec 2)} (h : addr <+: addr') :
    W_bit i k addr <+: W_bit i k addr' := by
  unfold W_bit
  split
  · exact gate1Out_mono _ (bitsA_mono h)
  · exact bitsA_mono h

theorem W_dec_mono {i : Nat} {addr addr' : List (BitVec 2)} (h : addr <+: addr') :
    W_dec i addr <+: W_dec i addr' := gateOut_mono _ (W_bit_mono h) (W_bit_mono h)

theorem W_en_mono {i : Nat} {we we' : List Bool} {addr addr' : List (BitVec 2)}
    (hw : we <+: we') (ha : addr <+: addr') : W_en i we addr <+: W_en i we' addr' :=
  gateOut_mono _ hw (W_dec_mono ha)

theorem cellOut_mono {i : Nat} {clk clk' we we' : List Bool} {addr addr' : List (BitVec 2)}
    {data data' crn crn' : List Bool} (hc : clk <+: clk') (hw : we <+: we') (ha : addr <+: addr')
    (hd : data <+: data') (hr : crn <+: crn') :
    cellOut i clk we addr data crn <+: cellOut i clk' we' addr' data' crn' :=
  enOut_mono hc (W_en_mono hw ha) hd hr

@[simp] theorem memOut_length (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) :
    (memOut clk we addr data crn).length = memLen clk we addr data crn + 1 := timeline_length _ _

theorem memOut_getD {clk we : List Bool} {addr : List (BitVec 2)} {data crn : List Bool} {t : Nat}
    (dflt : BitVec 2 → Bool) (ht : t < memLen clk we addr data crn + 1) :
    (memOut clk we addr data crn).getD t dflt =
      (fun a => if a = 0#2 then (cellOut 0 clk we addr data crn).getD t false
        else if a = 1#2 then (cellOut 1 clk we addr data crn).getD t false
        else if a = 2#2 then (cellOut 2 clk we addr data crn).getD t false
        else (cellOut 3 clk we addr data crn).getD t false) := timeline_getD _ ht _


/-! ### What the decoder shows

The decoder is three gates deep -- an inverter, the address match, the write enable -- so its
stream at an edge shows the enable and the address of three instants earlier.  Where they were
stable, that is the enable and the address of the edge itself. -/

theorem W_bit_length (i k : Nat) (addr : List (BitVec 2)) :
    addr.length ≤ (W_bit i k addr).length ∧ (W_bit i k addr).length ≤ addr.length + 1 := by
  unfold W_bit
  split <;> simp

theorem W_en_length_ge (i : Nat) (we : List Bool) (addr : List (BitVec 2)) :
    min we.length addr.length ≤ (W_en i we addr).length := by
  have h0 := W_bit_length i 0 addr
  have h1 := W_bit_length i 1 addr
  unfold W_en W_dec
  simp only [gateOut_length]
  omega

/-- The bit of the address the decoder reads for entry `i`, at a stable edge. -/
private theorem match_bits (x : BitVec 2) (i : Nat) (hi : i < 4) :
    ((if i % 2 = 0 then !x.getLsbD 0 else x.getLsbD 0) &&
      (if i / 2 = 0 then !x.getLsbD 1 else x.getLsbD 1)) = decide (x = BitVec.ofNat 2 i) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    revert x <;> decide

theorem W_en_getD {i : Nat} (hi : i < 4) {we : List Bool} {addr : List (BitVec 2)} {e : Nat}
    (he : 3 ≤ e) (hlen : e < min we.length addr.length)
    (hwe : ∀ u, e - 3 ≤ u → u ≤ e → we.getD u false = we.getD e false)
    (haddr : ∀ u, e - 3 ≤ u → u ≤ e → addr.getD u 0#2 = addr.getD e 0#2) :
    (W_en i we addr).getD e false =
      (we.getD e false && decide (addr.getD e 0#2 = BitVec.ofNat 2 i)) := by
  have hb0 := W_bit_length i 0 addr
  have hb1 := W_bit_length i 1 addr
  unfold W_en W_dec
  rw [gateOut_getD _ _ _ (by omega) (by
    have := W_en_length_ge i we addr
    unfold W_en at this
    simp only [gateOut_length] at this ⊢
    omega)]
  rw [gateOut_getD _ _ _ (by omega) (by omega)]
  rw [hwe (e - 1) (by omega) (by omega)]
  have hbit : ∀ k : Nat, ∀ b : Bool,
      (if b then gate1Out not (bitsA k addr) else bitsA k addr).getD (e - 1 - 1) false =
        (if b then !(addr.getD e 0#2).getLsbD k else (addr.getD e 0#2).getLsbD k) := by
    intro k b
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [bitsA_getD_all, haddr (e - 1 - 1) (by omega) (by omega)]
    · simp only [if_true]
      rw [gate1Out_getD _ _ (by omega) (by simp; omega), bitsA_getD_all,
        haddr (e - 1 - 1 - 1) (by omega) (by omega)]
  rw [show W_bit i 0 addr = (if decide (i % 2 = 0) then gate1Out not (bitsA 0 addr)
        else bitsA 0 addr) by unfold W_bit; simp,
    show W_bit i 1 addr = (if decide (i / 2 = 0) then gate1Out not (bitsA 1 addr)
        else bitsA 1 addr) by
      unfold W_bit
      rw [show (i >>> 1) % 2 = i / 2 by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl]
      simp,
    hbit 0 (decide (i % 2 = 0)), hbit 1 (decide (i / 2 = 0))]
  simp only [decide_eq_true_eq, and2]
  rw [show (if (i % 2 = 0) then !(addr.getD e 0#2).getLsbD 0 else (addr.getD e 0#2).getLsbD 0) =
      (if i % 2 = 0 then !(addr.getD e 0#2).getLsbD 0 else (addr.getD e 0#2).getLsbD 0) from rfl]
  rw [match_bits _ i hi]

/-! ### The contract of the register file -/

theorem memLen_le_enLen (i : Nat) (clk we : List Bool) (addr : List (BitVec 2))
    (data crn : List Bool) :
    memLen clk we addr data crn ≤ enLen clk (W_en i we addr) data crn := by
  have := W_en_length_ge i we addr
  unfold memLen enLen
  omega

/-- The decoder is three gates deep, so it carries the enable at most three instants past the
address and the write enable -- and that is the whole of the slack the packer has to guess. -/
theorem W_en_length_le (i : Nat) (we : List Bool) (addr : List (BitVec 2)) :
    (W_en i we addr).length ≤ min we.length addr.length + 3 := by
  have h0 := W_bit_length i 0 addr
  have h1 := W_bit_length i 1 addr
  unfold W_en W_dec
  simp only [gateOut_length]
  omega

theorem memOut_mono {clk clk' we we' : List Bool} {addr addr' : List (BitVec 2)}
    {data data' crn crn' : List Bool} (hc : clk <+: clk') (hw : we <+: we') (ha : addr <+: addr')
    (hd : data <+: data') (hr : crn <+: crn') :
    memOut clk we addr data crn <+: memOut clk' we' addr' data' crn' := by
  have l1 := hc.length_le; have l2 := hw.length_le; have l3 := ha.length_le
  have l4 := hd.length_le; have l5 := hr.length_le
  apply timeline_mono (by unfold memLen; omega)
  intro t ht
  have hm : ∀ i : Nat, memLen clk we addr data crn <
      (cellOut i clk we addr data crn).length := by
    intro i
    have := memLen_le_enLen i clk we addr data crn
    simp only [cellOut, enOut_length]
    omega
  have hcell : ∀ i : Nat, (cellOut i clk we addr data crn).getD t false =
      (cellOut i clk' we' addr' data' crn').getD t false := fun i =>
    (cellOut_mono (i := i) hc hw ha hd hr).getD_eq_left (by have := hm i; omega) false
  rw [hcell 0, hcell 1, hcell 2, hcell 3]

/-- A packer's report is a prefix of the file's: it computes the same values and stops earlier,
because the file knows the bound that the packer has to guess. -/
theorem packMemOut_prefix {clk we : List Bool} {addr : List (BitVec 2)} {data crn : List Bool}
    {q0 q1 q2 q3 : List Bool} (h0 : q0 <+: cellOut 0 clk we addr data crn)
    (h1 : q1 <+: cellOut 1 clk we addr data crn) (h2 : q2 <+: cellOut 2 clk we addr data crn)
    (h3 : q3 <+: cellOut 3 clk we addr data crn) :
    packMemOut q0 q1 q2 q3 <+: memOut clk we addr data crn := by
  have l0 := h0.length_le; have l1 := h1.length_le; have l2 := h2.length_le; have l3 := h3.length_le
  have hcl : ∀ i : Nat, (cellOut i clk we addr data crn).length =
      enLen clk (W_en i we addr) data crn + 1 := by
    intro i; simp only [cellOut, enOut_length]
  have hw0 := W_en_length_le 0 we addr; have hw1 := W_en_length_le 1 we addr
  have hw2 := W_en_length_le 2 we addr; have hw3 := W_en_length_le 3 we addr
  have he0 : enLen clk (W_en 0 we addr) data crn ≤ memLen clk we addr data crn + 3 := by
    unfold enLen memLen; omega
  have he1 : enLen clk (W_en 1 we addr) data crn ≤ memLen clk we addr data crn + 3 := by
    unfold enLen memLen; omega
  have he2 : enLen clk (W_en 2 we addr) data crn ≤ memLen clk we addr data crn + 3 := by
    unfold enLen memLen; omega
  have he3 : enLen clk (W_en 3 we addr) data crn ≤ memLen clk we addr data crn + 3 := by
    unfold enLen memLen; omega
  rw [hcl 0] at l0; rw [hcl 1] at l1; rw [hcl 2] at l2; rw [hcl 3] at l3
  apply timeline_mono (by omega)
  intro t ht
  rw [h0.getD_eq_left (by omega), h1.getD_eq_left (by omega), h2.getD_eq_left (by omega),
    h3.getD_eq_left (by omega)]

/-- The decoder's output is stable over the cell's setup window whenever the write enable and
the address were stable over the file's own, which is three instants wider. -/
theorem W_en_stable {i : Nat} (hi : i < 4) {we : List Bool} {addr : List (BitVec 2)} {e T : Nat}
    (he : 9 ≤ e) (hlen : e < min we.length addr.length) (hT : e < T)
    (hwe : ∀ u, e - 8 - 1 ≤ u → u ≤ e → we.getD u false = we.getD e false)
    (haddr : ∀ u, e - 8 - 1 ≤ u → u ≤ e → addr.getD u 0#2 = addr.getD e 0#2) :
    StableOn (fun u => (W_en i we addr).getD u false) T (e - 5 - 1) e := by
  refine ⟨hT, fun u k1 k2 => ?_⟩
  show (W_en i we addr).getD u false = (W_en i we addr).getD e false
  rw [W_en_getD hi (by omega) (by omega) (fun w j1 j2 => by
        rw [hwe w (by omega) (by omega), hwe u (by omega) (by omega)])
      (fun w j1 j2 => by rw [haddr w (by omega) (by omega), haddr u (by omega) (by omega)]),
    W_en_getD hi (by omega) hlen (fun w j1 j2 => hwe w (by omega) j2)
      (fun w j1 j2 => haddr w (by omega) j2),
    hwe u (by omega) (by omega), haddr u (by omega) (by omega)]

/-- With the write enable low, the decoder's output is low whatever the address. -/
theorem W_en_false {i : Nat} {we : List Bool} {addr : List (BitVec 2)} {u : Nat} (h1 : 1 ≤ u)
    (hlen : u < min we.length addr.length) (h : we.getD (u - 1) false = false) :
    (W_en i we addr).getD u false = false := by
  have hge := W_en_length_ge i we addr
  unfold W_en
  unfold W_en at hge
  rw [gateOut_getD _ _ _ h1 (by simp only [gateOut_length] at hge ⊢; omega), h]
  rfl

/-- The decoder is stable over the cell's setup window: either the write enable is low
throughout, or it is high and the address was stable too. -/
theorem W_en_stable' {i : Nat} (hi : i < 4) {we : List Bool} {addr : List (BitVec 2)} {e T : Nat}
    (he : 9 ≤ e) (hlen : e < min we.length addr.length) (hT : e < T)
    (hwe : ∀ u, e - 8 - 1 ≤ u → u ≤ e → we.getD u false = we.getD e false)
    (haddr : we.getD e false = true →
      ∀ u, e - 8 - 1 ≤ u → u ≤ e → addr.getD u 0#2 = addr.getD e 0#2) :
    StableOn (fun u => (W_en i we addr).getD u false) T (e - 5 - 1) e := by
  cases hb : we.getD e false
  · refine ⟨hT, fun u k1 k2 => ?_⟩
    show (W_en i we addr).getD u false = (W_en i we addr).getD e false
    rw [W_en_false (by omega) (by omega) (by rw [hwe (u - 1) (by omega) (by omega)]; exact hb),
      W_en_false (by omega) hlen (by rw [hwe (e - 1) (by omega) (by omega)]; exact hb)]
  · exact W_en_stable hi he hlen hT hwe (haddr hb)

/-- The filters the file needs. -/
structure MemOK (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) (R : Nat) :
    Prop where
  hR : 6 ≤ R
  clear : ClearOK R crn crn.length
  reset : ResetOK (R + 3) clk clk.length
  pulse : PulseOK 3 clk clk.length
  period : ClockOK 12 clk clk.length

variable {clk we : List Bool} {addr : List (BitVec 2)} {data crn : List Bool} {R : Nat}

theorem cellOK_of (H : MemOK clk we addr data crn R) (i : Nat) :
    CellOK clk (W_en i we addr) data crn R := by
  have hc : enLen clk (W_en i we addr) data crn ≤ clk.length := by unfold enLen; omega
  have hr : enLen clk (W_en i we addr) data crn ≤ crn.length := by unfold enLen; omega
  exact ⟨H.hR, H.clear.mono hr, H.reset.mono hc, H.pulse.mono hc, H.period.mono hc⟩

/-- The outer gate of the decoder: if the cell's enable is high, the write enable was. -/
theorem W_en_we {i : Nat} {we : List Bool} {addr : List (BitVec 2)} {e : Nat} (he : 1 ≤ e)
    (hlen : e < min we.length addr.length) (h : (W_en i we addr).getD e false = true) :
    we.getD (e - 1) false = true := by
  have hge := W_en_length_ge i we addr
  unfold W_en at h hge
  rw [gateOut_getD _ _ _ he (by simp only [gateOut_length] at hge ⊢; omega)] at h
  exact (Bool.and_eq_true _ _).mp h |>.1

/-- A write to entry `i` of the file is a write to cell `i`. -/
theorem writeAt_iff (H : MemOK clk we addr data crn R) {i : Nat} (hi : i < 4) {t : Nat}
    (ht : t ≤ memLen clk we addr data crn)
    (hclean : CleanWrites clk (fun u => we.getD u false) (fun u => addr.getD u 0#2)
      (fun u => data.getD u false) (memLen clk we addr data crn) 8 t)
    {e : Nat} (he : e < t) :
    WriteEdge (BitVec.ofNat 2 i) clk (fun u => we.getD u false) (fun u => addr.getD u 0#2)
        (fun u => data.getD u false) (memLen clk we addr data crn) 8 e ↔
      EnReg.WriteAt clk (W_en i we addr) data (enLen clk (W_en i we addr) data crn) 5 e := by
  have hmem := memLen_le_enLen i clk we addr data crn
  have hR6 := H.hR
  constructor
  · rintro ⟨hrise, hwe, haddr, hdat, hwe1, haddr1⟩
    have hel : e < memLen clk we addr data crn := by have := hwe.1; omega
    have hml : memLen clk we addr data crn ≤ min we.length addr.length := by
      unfold memLen; omega
    have hRe : R + 3 ≤ e := H.reset e (by unfold memLen at hel; omega) hrise
    refine ⟨hrise, W_en_stable hi (by omega) (by omega) (by omega)
        (fun u k1 k2 => hwe.2 u k1 k2) (fun u k1 k2 => haddr.2 u k1 k2),
      ⟨by omega, fun u k1 k2 => hdat.2 u (by omega) k2⟩, ?_⟩
    show (W_en i we addr).getD e false = true
    rw [W_en_getD hi (by omega) (by omega) (fun u k1 k2 => hwe.2 u (by omega) k2)
      (fun u k1 k2 => haddr.2 u (by omega) k2)]
    show (we.getD e false && decide (addr.getD e 0#2 = BitVec.ofNat 2 i)) = true
    rw [show we.getD e false = true from hwe1, show addr.getD e 0#2 = BitVec.ofNat 2 i from haddr1]
    simp
  · rintro ⟨hrise, _, _, hen⟩
    have hcl := hclean e he hrise
    have hel : e < memLen clk we addr data crn := by have := hcl.1.1; omega
    have hml : memLen clk we addr data crn ≤ min we.length addr.length := by
      unfold memLen; omega
    have hRe : R + 3 ≤ e := H.reset e (by unfold memLen at hel; omega) hrise
    have hwe' : ∀ u, e - 8 - 1 ≤ u → u ≤ e → we.getD u false = we.getD e false :=
      fun u k1 k2 => hcl.1.2 u k1 k2
    -- the outer gate gives the write enable, and then the address is stable too
    have hwe1 : we.getD e false = true := by
      rw [← hwe' (e - 1) (by omega) (by omega)]
      exact W_en_we (by omega) (by omega) hen
    have hst := hcl.2 hwe1
    have haddr' : ∀ u, e - 8 - 1 ≤ u → u ≤ e → addr.getD u 0#2 = addr.getD e 0#2 :=
      fun u k1 k2 => hst.1.2 u k1 k2
    rw [W_en_getD hi (by omega) (by omega) (fun u k1 k2 => hwe' u (by omega) k2)
      (fun u k1 k2 => haddr' u (by omega) k2)] at hen
    have haddr1 : addr.getD e 0#2 = BitVec.ofNat 2 i := by
      show _ = _
      rw [show we.getD e false = true from hwe1] at hen
      simpa using hen
    exact ⟨hrise, hcl.1, hst.1, hst.2, hwe1, haddr1⟩

/-! ### The file's contract -/

theorem memOut_length_le (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) :
    (memOut clk we addr data crn).length ≤ memLen clk we addr data crn + 1 := by
  rw [memOut_length]

/-- Every edge is clean for cell `i` when it is clean for the file. -/
theorem cleanCell_of (H : MemOK clk we addr data crn R) {i : Nat} (hi : i < 4) {t : Nat}
    (ht : t ≤ memLen clk we addr data crn)
    (hclean : CleanWrites clk (fun u => we.getD u false) (fun u => addr.getD u 0#2)
      (fun u => data.getD u false) (memLen clk we addr data crn) 8 t) :
    CleanCell clk (W_en i we addr) data (enLen clk (W_en i we addr) data crn) 5 t := by
  have hmem := memLen_le_enLen i clk we addr data crn
  have hR6 := H.hR
  intro e k1 k2
  have hcl := hclean e k1 k2
  have hel : e < memLen clk we addr data crn := by have := hcl.1.1; omega
  have hml : memLen clk we addr data crn ≤ min we.length addr.length := by unfold memLen; omega
  have hRe : R + 3 ≤ e := H.reset e (by unfold memLen at hel; omega) k2
  refine ⟨W_en_stable' hi (by omega) (by omega) (by omega) (fun u j1 j2 => hcl.1.2 u j1 j2)
    (fun hb u j1 j2 => (hcl.2 hb).1.2 u j1 j2), fun hb => ?_⟩
  -- the enable is high, so the file was writing and the data was stable
  have hwe' : ∀ u, e - 8 - 1 ≤ u → u ≤ e → we.getD u false = we.getD e false :=
    fun u j1 j2 => hcl.1.2 u j1 j2
  have hwe1 : we.getD e false = true := by
    rw [← hwe' (e - 1) (by omega) (by omega)]
    exact W_en_we (by omega) (by omega) hb
  exact ⟨by omega, fun u j1 j2 => (hcl.2 hwe1).2.2 u (by omega) j2⟩

/-- One entry of the file holds what the last write to it wrote. -/
theorem cell_clause (H : MemOK clk we addr data crn R) {i : Nat} (hi : i < 4) {t : Nat}
    (ht : t ≤ memLen clk we addr data crn)
    (hclean : CleanWrites clk (fun u => we.getD u false) (fun u => addr.getD u 0#2)
      (fun u => data.getD u false) (memLen clk we addr data crn) 8 t) :
    ((∀ e, e < t → ¬ WriteEdge (BitVec.ofNat 2 i) clk (fun u => we.getD u false)
        (fun u => addr.getD u 0#2) (fun u => data.getD u false)
        (memLen clk we addr data crn) 8 e) →
      (cellOut i clk we addr data crn).getD t false = false) ∧
    (∀ e, e < t → WriteEdge (BitVec.ofNat 2 i) clk (fun u => we.getD u false)
        (fun u => addr.getD u 0#2) (fun u => data.getD u false)
        (memLen clk we addr data crn) 8 e →
      (∀ e', e < e' → e' < t → ¬ WriteEdge (BitVec.ofNat 2 i) clk (fun u => we.getD u false)
        (fun u => addr.getD u 0#2) (fun u => data.getD u false)
        (memLen clk we addr data crn) 8 e') → e + 4 ≤ t →
      (cellOut i clk we addr data crn).getD t false = data.getD e false) := by
  have hmem := memLen_le_enLen i clk we addr data crn
  have hcv := cell_value (cellOK_of H i) t (by omega) (cleanCell_of H hi ht hclean)
  refine ⟨fun hnone => hcv.1 (fun e k hw => hnone e k ((writeAt_iff H hi ht hclean k).mpr hw)),
    fun e he hw hlast hk => hcv.2 e he ((writeAt_iff H hi ht hclean he).mp hw)
      (fun e' k1 k2 hw' => hlast e' k1 k2 ((writeAt_iff H hi ht hclean (by omega)).mpr hw')) hk⟩

private theorem bv2_cases (a : BitVec 2) : a = 0#2 ∨ a = 1#2 ∨ a = 2#2 ∨ a = 3#2 := by
  revert a; decide

/-- **The register file meets `MemOut`**, with clock-to-q `4` and setup `8`: the decoder is
three gates deep and the cell needs five, so the file's window is the sum. -/
theorem memOut_memOut (H : MemOK clk we addr data crn R) {v : List (BitVec 2 → Bool)}
    (hv : v <+: memOut clk we addr data crn) :
    MemOut 4 8 clk (fun u => we.getD u false) (fun u => addr.getD u 0#2)
      (fun u => data.getD u false) (memLen clk we addr data crn) v := by
  have hlen := hv.length_le
  have hml := memOut_length_le clk we addr data crn
  have hmc : memLen clk we addr data crn ≤ clk.length := by unfold memLen; omega
  refine ⟨by omega, fun t ht hclean a => ?_⟩
  have htm : t ≤ memLen clk we addr data crn := by omega
  -- the entry `a` is held by cell `a`
  have hcell : ∀ i : Nat, i < 4 → BitVec.ofNat 2 i = a →
      v.getD t (fun _ => default) a = (cellOut i clk we addr data crn).getD t false := by
    intro i hi hia
    rw [hv.getD_eq_left ht]
    have hml4 : t < memLen clk we addr data crn + 1 := by
      have := hv.length_le
      rw [memOut_length] at this
      omega
    rw [memOut_getD _ hml4, ← hia]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  rcases bv2_cases a with rfl | rfl | rfl | rfl
  · rw [hcell 0 (by omega) (by decide)]
    exact cell_clause H (by omega) htm hclean
  · rw [hcell 1 (by omega) (by decide)]
    exact cell_clause H (by omega) htm hclean
  · rw [hcell 2 (by omega) (by decide)]
    exact cell_clause H (by omega) htm hclean
  · rw [hcell 3 (by omega) (by decide)]
    exact cell_clause H (by omega) htm hclean

seal menv in
def_module memT : Type :=
  [T| memLowered, menv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal menv in
def_module memNetlist : StringModule memT :=
  [e| memLowered, menv.find? ]

instance : MatchInterface memNetlist memSpec := by
  dsimp [memNetlist, memSpec]
  solve_match_interface
end Graphiti.AsyncFifo.RegFile