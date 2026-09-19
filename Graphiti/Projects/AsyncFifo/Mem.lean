/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.EnRegTiming

/-!
# The register file: an address decoder and four cells

The write domain's memory holds four one-bit entries.  The address is decoded into four write
enables -- six gates, two inverters and four ANDs, and one more AND per entry for the write
enable itself -- and each enable drives a cell of `EnReg.lean`.

Nothing here has feedback: the loop of a memory lives inside the cell, so at this level the
cells are the blocks they were proved to refine and the proof is the one `BusReg.lean` uses,
with the decoder's gates in front.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.Mem

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff Graphiti.AsyncFifo.EnReg

/-! ### The address and its bits -/

def bitsA (i : Nat) (addr : List (BitVec 2)) : List Bool := addr.map (·.getLsbD i)

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

/-- Split the address bus into its two bits. -/
@[drcomponents]
def unpack2A : StringModule (List (BitVec 2)) :=
  { inputs := [ (↑"a", ⟨List (BitVec 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"b0", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsA 0 s⟩)
               , (↑"b1", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsA 1 s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The four entries as one function, reported three instants short of where the cells reach.
That is the file's reporting policy: the decoder in front of the cells is three gates deep, so
the cells run up to three instants ahead of the address, and what a block reports has to stay
inside the horizon its own inputs justify (`MemOut`'s length clause, which is what makes that
contract monotone).  Reporting less than one computes is always sound. -/
def packMemOut (q0 q1 q2 q3 : List Bool) : List (BitVec 2 → Bool) :=
  timeline (fun t a => if a = 0#2 then q0.getD t false else if a = 1#2 then q1.getD t false
    else if a = 2#2 then q2.getD t false else q3.getD t false)
    (min (min q0.length q1.length) (min q2.length q3.length) - 3)

@[simp] theorem packMemOut_length (q0 q1 q2 q3 : List Bool) :
    (packMemOut q0 q1 q2 q3).length =
      min (min q0.length q1.length) (min q2.length q3.length) - 3 := timeline_length _ _

theorem packMemOut_getD {q0 q1 q2 q3 : List Bool} {t : Nat} (dflt : BitVec 2 → Bool)
    (ht : t < min (min q0.length q1.length) (min q2.length q3.length) - 3) :
    (packMemOut q0 q1 q2 q3).getD t dflt =
      (fun a => if a = 0#2 then q0.getD t false else if a = 1#2 then q1.getD t false
        else if a = 2#2 then q2.getD t false else q3.getD t false) := timeline_getD _ ht _

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

/-- Assemble the four entries into one function. -/
@[drcomponents]
def packMem : StringModule (List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"q0", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"q1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"q2", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"q3", ⟨List Bool, fun s v s' => s.2.2.2 ⊏ v ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s' = s ∧
                    v = packMemOut s.1 s.2.1 s.2.2.1 s.2.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

/-! ### The decoded write enables, as streams -/

/-- The address bit the decoder of entry `i` reads, inverted or not. -/
def W_bit (i k : Nat) (addr : List (BitVec 2)) : List Bool :=
  if (i >>> k) % 2 = 0 then gate1Out not (bitsA k addr) else bitsA k addr

/-- The address match of entry `i`. -/
def W_dec (i : Nat) (addr : List (BitVec 2)) : List Bool :=
  gateOut and2 (W_bit i 0 addr) (W_bit i 1 addr)

/-- The enable of entry `i`: the write enable, and the address matching `i`.  Three gates deep:
an inverter, the address match, and the write enable itself. -/
def W_en (i : Nat) (we : List Bool) (addr : List (BitVec 2)) : List Bool :=
  gateOut and2 we (W_dec i addr)

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

/-- What one cell of the file reports. -/
def cellOut (i : Nat) (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) :
    List Bool :=
  enOut clk (W_en i we addr) data crn

theorem cellOut_mono {i : Nat} {clk clk' we we' : List Bool} {addr addr' : List (BitVec 2)}
    {data data' crn crn' : List Bool} (hc : clk <+: clk') (hw : we <+: we') (ha : addr <+: addr')
    (hd : data <+: data') (hr : crn <+: crn') :
    cellOut i clk we addr data crn <+: cellOut i clk' we' addr' data' crn' :=
  enOut_mono hc (W_en_mono hw ha) hd hr

/-- How far the file's inputs are known. -/
def memLen (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) : Nat :=
  min (min clk.length we.length) (min addr.length (min data.length crn.length))

/-- What the file reports: its four cells, as far as the *file's own* inputs are known plus the
one instant a Moore block may add.

The packer on its own cannot know that bound.  It sees only the four cells, and a cell's enable
comes through the decoder, which is three gates deep, so the cells are known further than the
file's inputs are --- by as much as three instants, and by nothing at all when the address and
the write enable are the short ones.  With only the cells in hand the packer has to assume the
worst and subtract the decoder's depth (`packMemOut`), which costs it three instants whenever
they were not there to lose.  Read against the file's inputs the bound is exact, and that is
what the file reports: `memLen + 1`, never more (`memLen_le_enLen`) and never less. -/
def memOut (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) :
    List (BitVec 2 → Bool) :=
  timeline (fun t a => if a = 0#2 then (cellOut 0 clk we addr data crn).getD t false
      else if a = 1#2 then (cellOut 1 clk we addr data crn).getD t false
      else if a = 2#2 then (cellOut 2 clk we addr data crn).getD t false
      else (cellOut 3 clk we addr data crn).getD t false)
    (memLen clk we addr data crn + 1)

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

theorem enLen_le (i : Nat) (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) :
    enLen clk (W_en i we addr) data crn ≤ memLen clk we addr data crn + 3 := by
  have h : (W_en i we addr).length ≤ min we.length addr.length + 3 := by
    have h0 := W_bit_length i 0 addr
    have h1 := W_bit_length i 1 addr
    unfold W_en W_dec
    simp only [gateOut_length]
    omega
  unfold memLen enLen
  omega

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

/-! ### The netlist -/

def memGraph := [graphEnv|
    clk [type="io"];
    we [type="io"];
    addr [type="io"];
    data [type="io"];
    clrn [type="io"];
    mem [type="io"];

    unpA [type="unpack2A", typeImp=$(⟨_, unpack2A⟩)];
    clkF [type="fork4", typeImp=$(⟨_, fork4⟩)];
    crF [type="fork4", typeImp=$(⟨_, fork4⟩)];
    weF [type="fork4", typeImp=$(⟨_, fork4⟩)];
    dataF [type="fork4", typeImp=$(⟨_, fork4⟩)];
    a0F [type="fork3", typeImp=$(⟨_, fork3⟩)];
    a1F [type="fork3", typeImp=$(⟨_, fork3⟩)];
    na0 [type="not1", typeImp=$(⟨_, gate1 not⟩)];
    na1 [type="not1", typeImp=$(⟨_, gate1 not⟩)];
    na0F [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    na1F [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    dec0 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    dec1 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    dec2 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    dec3 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    en0 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    en1 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    en2 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    en3 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    c0 [type="cell", typeImp=$(⟨_, enSpec⟩)];
    c1 [type="cell", typeImp=$(⟨_, enSpec⟩)];
    c2 [type="cell", typeImp=$(⟨_, enSpec⟩)];
    c3 [type="cell", typeImp=$(⟨_, enSpec⟩)];
    pk [type="packMem", typeImp=$(⟨_, packMem⟩)];

    clk -> clkF [to="in"];
    we -> weF [to="in"];
    addr -> unpA [to="a"];
    data -> dataF [to="in"];
    clrn -> crF [to="in"];

    unpA -> a0F [from="b0", to="in"];
    unpA -> a1F [from="b1", to="in"];
    a0F -> na0 [from="out1", to="a"];
    a0F -> dec1 [from="out2", to="a"];
    a0F -> dec3 [from="out3", to="a"];
    a1F -> na1 [from="out1", to="a"];
    a1F -> dec2 [from="out2", to="b"];
    a1F -> dec3 [from="out3", to="b"];
    na0 -> na0F [from="out", to="in"];
    na0F -> dec0 [from="out1", to="a"];
    na0F -> dec2 [from="out2", to="a"];
    na1 -> na1F [from="out", to="in"];
    na1F -> dec0 [from="out1", to="b"];
    na1F -> dec1 [from="out2", to="b"];
    weF -> en0 [from="out1", to="a"];
    weF -> en1 [from="out2", to="a"];
    weF -> en2 [from="out3", to="a"];
    weF -> en3 [from="out4", to="a"];
    dec0 -> en0 [from="out", to="b"];
    dec1 -> en1 [from="out", to="b"];
    dec2 -> en2 [from="out", to="b"];
    dec3 -> en3 [from="out", to="b"];
    clkF -> c0 [from="out1", to="clk"];
    clkF -> c1 [from="out2", to="clk"];
    clkF -> c2 [from="out3", to="clk"];
    clkF -> c3 [from="out4", to="clk"];
    crF -> c0 [from="out1", to="clrn"];
    crF -> c1 [from="out2", to="clrn"];
    crF -> c2 [from="out3", to="clrn"];
    crF -> c3 [from="out4", to="clrn"];
    dataF -> c0 [from="out1", to="data"];
    dataF -> c1 [from="out2", to="data"];
    dataF -> c2 [from="out3", to="data"];
    dataF -> c3 [from="out4", to="data"];
    en0 -> c0 [from="out", to="en"];
    en1 -> c1 [from="out", to="en"];
    en2 -> c2 [from="out", to="en"];
    en3 -> c3 [from="out", to="en"];
    c0 -> pk [from="q", to="q0"];
    c1 -> pk [from="q", to="q1"];
    c2 -> pk [from="q", to="q2"];
    c3 -> pk [from="q", to="q3"];

    pk -> mem [from="mem"];
  ]

@[drunfold_defs]
def memLowered := memGraph.1.lower_TR |>.get rfl

def menv := memGraph.2

@[drenv] theorem menv_unpack2A : menv.find? "unpack2A" = .some ⟨_, unpack2A⟩ := rfl
@[drenv] theorem menv_fork2 : menv.find? "fork2" = .some ⟨_, Timed.fork2 Bool⟩ := rfl
@[drenv] theorem menv_fork3 : menv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem menv_fork4 : menv.find? "fork4" = .some ⟨_, fork4⟩ := rfl
@[drenv] theorem menv_not1 : menv.find? "not1" = .some ⟨_, gate1 not⟩ := rfl
@[drenv] theorem menv_and2 : menv.find? "and2" = .some ⟨_, gate2 and2⟩ := rfl
@[drenv] theorem menv_cell : menv.find? "cell" = .some ⟨_, enSpec⟩ := rfl
@[drenv] theorem menv_packMem : menv.find? "packMem" = .some ⟨_, packMem⟩ := rfl

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

-- HEADER_END (everything below is generated by gen/gen_mem.py)

/-! ### The specification -/

/-- The register file as a single block. -/
@[drcomponents]
def memSpec : StringModule (List Bool × List Bool × List (BitVec 2) × List Bool × List Bool ×
    List (BitVec 2 → Bool)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"we", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"addr", ⟨List (BitVec 2), fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"data", ⟨List Bool, fun s v s' => s.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩) ].toAssocList
    outputs := [ (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2.2.2.2.2 <+: v ∧
                    v <+: memOut s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], []) }

instance : MatchInterface memNetlist memSpec := by
  dsimp [memNetlist, memSpec]
  solve_match_interface

/-! ### The invariant -/

structure Wf (en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn : List Bool)
    (unpA_a : List (BitVec 2)) (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) : Prop where
  e_clk : clkF_in = s.1
  e_we : weF_in = s.2.1
  e_addr : unpA_a = s.2.2.1
  e_data : dataF_in = s.2.2.2.1
  e_crn : crF_in = s.2.2.2.2.1
  w_en2_a : en2_a <+: weF_in
  w_en2_b : en2_b <+: gateOut and2 dec2_a dec2_b
  w_en3_a : en3_a <+: weF_in
  w_en3_b : en3_b <+: gateOut and2 dec3_a dec3_b
  w_pk_q0 : pk_q0 <+: enOut c0_clk c0_en c0_data c0_clrn
  w_pk_q1 : pk_q1 <+: enOut c1_clk c1_en c1_data c1_clrn
  w_pk_q2 : pk_q2 <+: enOut c2_clk c2_en c2_data c2_clrn
  w_pk_q3 : pk_q3 <+: enOut c3_clk c3_en c3_data c3_clrn
  w_dec3_a : dec3_a <+: a0F_in
  w_dec3_b : dec3_b <+: a1F_in
  w_c2_clk : c2_clk <+: clkF_in
  w_c2_en : c2_en <+: gateOut and2 en2_a en2_b
  w_c2_data : c2_data <+: dataF_in
  w_c2_clrn : c2_clrn <+: crF_in
  w_c3_clk : c3_clk <+: clkF_in
  w_c3_en : c3_en <+: gateOut and2 en3_a en3_b
  w_c3_data : c3_data <+: dataF_in
  w_c3_clrn : c3_clrn <+: crF_in
  w_a0F_in : a0F_in <+: bitsA 0 unpA_a
  w_na0F_in : na0F_in <+: gate1Out not na0_a
  w_a1F_in : a1F_in <+: bitsA 1 unpA_a
  w_na1_a : na1_a <+: a1F_in
  w_en0_a : en0_a <+: weF_in
  w_en0_b : en0_b <+: gateOut and2 dec0_a dec0_b
  w_c0_clk : c0_clk <+: clkF_in
  w_c0_en : c0_en <+: gateOut and2 en0_a en0_b
  w_c0_data : c0_data <+: dataF_in
  w_c0_clrn : c0_clrn <+: crF_in
  w_en1_a : en1_a <+: weF_in
  w_en1_b : en1_b <+: gateOut and2 dec1_a dec1_b
  w_na0_a : na0_a <+: a0F_in
  w_dec0_a : dec0_a <+: na0F_in
  w_dec0_b : dec0_b <+: na1F_in
  w_dec2_a : dec2_a <+: na0F_in
  w_dec2_b : dec2_b <+: a1F_in
  w_dec1_a : dec1_a <+: a0F_in
  w_dec1_b : dec1_b <+: na1F_in
  w_na1F_in : na1F_in <+: gate1Out not na1_a
  w_c1_clk : c1_clk <+: clkF_in
  w_c1_en : c1_en <+: gateOut and2 en1_a en1_b
  w_c1_data : c1_data <+: dataF_in
  w_c1_clrn : c1_clrn <+: crF_in
  h_mem : s.2.2.2.2.2 <+: packMemOut pk_q0 pk_q1 pk_q2 pk_q3

def ψ (i : memT) (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) : Prop :=
  Wf i.1.1 i.1.2 i.2.1.1 i.2.1.2 i.2.2.1.1 i.2.2.1.2.1 i.2.2.1.2.2.1 i.2.2.1.2.2.2 i.2.2.2.1.1 i.2.2.2.1.2 i.2.2.2.2.1.1 i.2.2.2.2.1.2.1 i.2.2.2.2.1.2.2.1 i.2.2.2.2.1.2.2.2 i.2.2.2.2.2.1.1 i.2.2.2.2.2.1.2.1 i.2.2.2.2.2.1.2.2.1 i.2.2.2.2.2.1.2.2.2 i.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s

theorem Wf.init : Wf [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] ([], [], [], [], [], []) :=
  ⟨rfl, rfl, rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩

section SpecRules
variable (sp : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_we (v : List Bool) (h : sp.2.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"we").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_addr (v : List (BitVec 2)) (h : sp.2.2.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"addr").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_data (v : List Bool) (h : sp.2.2.2.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"data").2 sp v (sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.2.2.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_mem (v : List (BitVec 2 → Bool)) (h1 : sp.2.2.2.2.2 <+: v)
    (h2 : v <+: memOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2.1 sp.2.2.2.2.1) :
    (memSpec.outputs.getIO ↑"mem").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

section Cases
variable {en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn : List Bool}
  {unpA_a : List (BitVec 2)} {sp : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)}
  (Hψ : Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp)
include Hψ

theorem in_clk (v : List Bool) (h : clkF_in ⊏ v) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b (v) dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a (v, sp.2) := by
  have hm : clkF_in <+: v := h.isPrefix
  exact { e_clk := rfl
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk.trans hm
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk.trans hm
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk.trans hm
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk.trans hm
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem in_we (v : List Bool) (h : weF_in ⊏ v) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in (v) na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a (sp.1, v, sp.2.2) := by
  have hm : weF_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_we := rfl
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a.trans hm
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a.trans hm
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a.trans hm
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a.trans hm
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem in_addr (v : List (BitVec 2)) (h : unpA_a ⊏ v) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn (v) (sp.1, sp.2.1, v, sp.2.2.2) := by
  have hm : unpA_a <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := rfl
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in.trans (bitsA_mono hm)
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in.trans (bitsA_mono hm)
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem in_data (v : List Bool) (h : dataF_in ⊏ v) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in (v) weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a (sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2) := by
  have hm : dataF_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := rfl
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data.trans hm
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data.trans hm
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data.trans hm
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data.trans hm
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem in_clrn (v : List Bool) (h : crF_in ⊏ v) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in (v) na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2) := by
  have hm : crF_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := rfl
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn.trans hm
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn.trans hm
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn.trans hm
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn.trans hm
          h_mem := Hψ.h_mem }

theorem int_0 (_h : a0F_in ⊏ bitsA 0 unpA_a) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn (bitsA 0 unpA_a) crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a.trans Hψ.w_a0F_in
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := List.prefix_rfl
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a.trans Hψ.w_a0F_in
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a.trans Hψ.w_a0F_in
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_1 (_h : a1F_in ⊏ bitsA 1 unpA_a) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in (bitsA 1 unpA_a) dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b.trans Hψ.w_a1F_in
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := List.prefix_rfl
          w_na1_a := Hψ.w_na1_a.trans Hψ.w_a1F_in
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b.trans Hψ.w_a1F_in
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_2 (_h : na0_a ⊏ a0F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b (a0F_in) dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in.trans (gate1Out_mono _ Hψ.w_na0_a)
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := List.prefix_rfl
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_3 (_h : dec1_a ⊏ a0F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b (a0F_in) dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b.trans (gateOut_mono _ Hψ.w_dec1_a List.prefix_rfl)
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := List.prefix_rfl
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_4 (_h : dec3_a ⊏ a0F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 (a0F_in) dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b.trans (gateOut_mono _ Hψ.w_dec3_a List.prefix_rfl)
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := List.prefix_rfl
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_5 (_h : na1_a ⊏ a1F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in (a1F_in) en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := List.prefix_rfl
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in.trans (gate1Out_mono _ Hψ.w_na1_a)
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_6 (_h : dec2_b ⊏ a1F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a (a1F_in) dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_dec2_b)
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := List.prefix_rfl
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_7 (_h : dec3_b ⊏ a1F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a (a1F_in) c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_dec3_b)
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := List.prefix_rfl
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_8 (_h : na0F_in ⊏ gate1Out not na0_a) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in (gate1Out not na0_a) a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := List.prefix_rfl
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a.trans Hψ.w_na0F_in
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a.trans Hψ.w_na0F_in
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_9 (_h : dec0_a ⊏ na0F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a (na0F_in) dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b.trans (gateOut_mono _ Hψ.w_dec0_a List.prefix_rfl)
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := List.prefix_rfl
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_10 (_h : dec2_a ⊏ na0F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in (na0F_in) dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b.trans (gateOut_mono _ Hψ.w_dec2_a List.prefix_rfl)
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := List.prefix_rfl
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_11 (_h : na1F_in ⊏ gate1Out not na1_a) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b (gate1Out not na1_a) c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b.trans Hψ.w_na1F_in
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b.trans Hψ.w_na1F_in
          w_na1F_in := List.prefix_rfl
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_12 (_h : dec0_b ⊏ na1F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a (na1F_in) clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_dec0_b)
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := List.prefix_rfl
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_13 (_h : dec1_b ⊏ na1F_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a (na1F_in) na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_dec1_b)
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := List.prefix_rfl
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_14 (_h : en0_a ⊏ weF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a (weF_in) en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := List.prefix_rfl
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en.trans (gateOut_mono _ Hψ.w_en0_a List.prefix_rfl)
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_15 (_h : en1_a ⊏ weF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn (weF_in) en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := List.prefix_rfl
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en.trans (gateOut_mono _ Hψ.w_en1_a List.prefix_rfl)
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_16 (_h : en2_a ⊏ weF_in) :
    Wf (weF_in) en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := List.prefix_rfl
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en.trans (gateOut_mono _ Hψ.w_en2_a List.prefix_rfl)
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_17 (_h : en3_a ⊏ weF_in) :
    Wf en2_a en2_b (weF_in) en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := List.prefix_rfl
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en.trans (gateOut_mono _ Hψ.w_en3_a List.prefix_rfl)
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_18 (_h : en0_b ⊏ gateOut and2 dec0_a dec0_b) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a (gateOut and2 dec0_a dec0_b) c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := List.prefix_rfl
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en.trans (gateOut_mono _ List.prefix_rfl Hψ.w_en0_b)
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_19 (_h : en1_b ⊏ gateOut and2 dec1_a dec1_b) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a (gateOut and2 dec1_a dec1_b) na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := List.prefix_rfl
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en.trans (gateOut_mono _ List.prefix_rfl Hψ.w_en1_b)
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_20 (_h : en2_b ⊏ gateOut and2 dec2_a dec2_b) :
    Wf en2_a (gateOut and2 dec2_a dec2_b) en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := List.prefix_rfl
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en.trans (gateOut_mono _ List.prefix_rfl Hψ.w_en2_b)
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_21 (_h : en3_b ⊏ gateOut and2 dec3_a dec3_b) :
    Wf en2_a en2_b en3_a (gateOut and2 dec3_a dec3_b) pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := List.prefix_rfl
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en.trans (gateOut_mono _ List.prefix_rfl Hψ.w_en3_b)
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_22 (_h : c0_clk ⊏ clkF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b (clkF_in) c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0.trans (enOut_mono Hψ.w_c0_clk List.prefix_rfl List.prefix_rfl List.prefix_rfl)
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := List.prefix_rfl
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_23 (_h : c1_clk ⊏ clkF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in (clkF_in) c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1.trans (enOut_mono Hψ.w_c1_clk List.prefix_rfl List.prefix_rfl List.prefix_rfl)
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := List.prefix_rfl
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_24 (_h : c2_clk ⊏ clkF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b (clkF_in) c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2.trans (enOut_mono Hψ.w_c2_clk List.prefix_rfl List.prefix_rfl List.prefix_rfl)
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := List.prefix_rfl
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_25 (_h : c3_clk ⊏ clkF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn (clkF_in) c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3.trans (enOut_mono Hψ.w_c3_clk List.prefix_rfl List.prefix_rfl List.prefix_rfl)
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := List.prefix_rfl
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_26 (_h : c0_clrn ⊏ crF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data (crF_in) en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0.trans (enOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl Hψ.w_c0_clrn)
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := List.prefix_rfl
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_27 (_h : c1_clrn ⊏ crF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data (crF_in) unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1.trans (enOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl Hψ.w_c1_clrn)
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := List.prefix_rfl
          h_mem := Hψ.h_mem }

theorem int_28 (_h : c2_clrn ⊏ crF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data (crF_in) c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2.trans (enOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl Hψ.w_c2_clrn)
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := List.prefix_rfl
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_29 (_h : c3_clrn ⊏ crF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data (crF_in) a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3.trans (enOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl Hψ.w_c3_clrn)
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := List.prefix_rfl
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_30 (_h : c0_data ⊏ dataF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en (dataF_in) c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0.trans (enOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_c0_data List.prefix_rfl)
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := List.prefix_rfl
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_31 (_h : c1_data ⊏ dataF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en (dataF_in) c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1.trans (enOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_c1_data List.prefix_rfl)
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := List.prefix_rfl
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_32 (_h : c2_data ⊏ dataF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en (dataF_in) c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2.trans (enOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_c2_data List.prefix_rfl)
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := List.prefix_rfl
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_33 (_h : c3_data ⊏ dataF_in) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en (dataF_in) c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3.trans (enOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_c3_data List.prefix_rfl)
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := List.prefix_rfl
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_34 (_h : c0_en ⊏ gateOut and2 en0_a en0_b) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk (gateOut and2 en0_a en0_b) c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0.trans (enOut_mono List.prefix_rfl Hψ.w_c0_en List.prefix_rfl List.prefix_rfl)
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := List.prefix_rfl
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_35 (_h : c1_en ⊏ gateOut and2 en1_a en1_b) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk (gateOut and2 en1_a en1_b) c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1.trans (enOut_mono List.prefix_rfl Hψ.w_c1_en List.prefix_rfl List.prefix_rfl)
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := List.prefix_rfl
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_36 (_h : c2_en ⊏ gateOut and2 en2_a en2_b) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk (gateOut and2 en2_a en2_b) c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2.trans (enOut_mono List.prefix_rfl Hψ.w_c2_en List.prefix_rfl List.prefix_rfl)
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := List.prefix_rfl
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_37 (_h : c3_en ⊏ gateOut and2 en3_a en3_b) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk (gateOut and2 en3_a en3_b) c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3.trans (enOut_mono List.prefix_rfl Hψ.w_c3_en List.prefix_rfl List.prefix_rfl)
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := List.prefix_rfl
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem }

theorem int_38 {out : List Bool} (_h : pk_q0 ⊏ out) (hout : out <+: enOut c0_clk c0_en c0_data c0_clrn) :
    Wf en2_a en2_b en3_a en3_b (out) pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := hout
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem.trans (packMemOut_mono (_h.isPrefix) List.prefix_rfl List.prefix_rfl List.prefix_rfl) }

theorem int_39 {out : List Bool} (_h : pk_q1 ⊏ out) (hout : out <+: enOut c1_clk c1_en c1_data c1_clrn) :
    Wf en2_a en2_b en3_a en3_b pk_q0 (out) pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := hout
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem.trans (packMemOut_mono List.prefix_rfl (_h.isPrefix) List.prefix_rfl List.prefix_rfl) }

theorem int_40 {out : List Bool} (_h : pk_q2 ⊏ out) (hout : out <+: enOut c2_clk c2_en c2_data c2_clrn) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 (out) pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := hout
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem.trans (packMemOut_mono List.prefix_rfl List.prefix_rfl (_h.isPrefix) List.prefix_rfl) }

theorem int_41 {out : List Bool} (_h : pk_q3 ⊏ out) (hout : out <+: enOut c3_clk c3_en c3_data c3_clrn) :
    Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 (out) dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a sp := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := hout
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := Hψ.h_mem.trans (packMemOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl (_h.isPrefix)) }

/-- What the file reports is a prefix of the specification's stream: every cell sees prefixes
of the block's inputs, and the decoder in front of it a prefix of the address. -/
theorem out_mem : packMemOut pk_q0 pk_q1 pk_q2 pk_q3 <+:
    memOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2.1 sp.2.2.2.2.1 := by
  have hclk : ∀ x : List Bool, x <+: clkF_in → x <+: sp.1 := fun x h => h.trans (Hψ.e_clk ▸ List.prefix_rfl)
  have hwe : ∀ x : List Bool, x <+: weF_in → x <+: sp.2.1 := fun x h => h.trans (Hψ.e_we ▸ List.prefix_rfl)
  have hdata : ∀ x : List Bool, x <+: dataF_in → x <+: sp.2.2.2.1 := fun x h => h.trans (Hψ.e_data ▸ List.prefix_rfl)
  have hcrn : ∀ x : List Bool, x <+: crF_in → x <+: sp.2.2.2.2.1 := fun x h => h.trans (Hψ.e_crn ▸ List.prefix_rfl)
  have ha0 : a0F_in <+: bitsA 0 sp.2.2.1 := Hψ.w_a0F_in.trans (bitsA_mono (Hψ.e_addr ▸ List.prefix_rfl))
  have ha1 : a1F_in <+: bitsA 1 sp.2.2.1 := Hψ.w_a1F_in.trans (bitsA_mono (Hψ.e_addr ▸ List.prefix_rfl))
  have hn0 : na0F_in <+: gate1Out not (bitsA 0 sp.2.2.1) :=
    Hψ.w_na0F_in.trans (gate1Out_mono _ (Hψ.w_na0_a.trans ha0))
  have hn1 : na1F_in <+: gate1Out not (bitsA 1 sp.2.2.1) :=
    Hψ.w_na1F_in.trans (gate1Out_mono _ (Hψ.w_na1_a.trans ha1))
  have hd0 : gateOut and2 dec0_a dec0_b <+: W_dec 0 sp.2.2.1 :=
    gateOut_mono _ (Hψ.w_dec0_a.trans hn0) (Hψ.w_dec0_b.trans hn1)
  have he0 : gateOut and2 en0_a en0_b <+: W_en 0 sp.2.1 sp.2.2.1 :=
    gateOut_mono _ (hwe _ Hψ.w_en0_a) (Hψ.w_en0_b.trans hd0)
  have hd1 : gateOut and2 dec1_a dec1_b <+: W_dec 1 sp.2.2.1 :=
    gateOut_mono _ (Hψ.w_dec1_a.trans ha0) (Hψ.w_dec1_b.trans hn1)
  have he1 : gateOut and2 en1_a en1_b <+: W_en 1 sp.2.1 sp.2.2.1 :=
    gateOut_mono _ (hwe _ Hψ.w_en1_a) (Hψ.w_en1_b.trans hd1)
  have hd2 : gateOut and2 dec2_a dec2_b <+: W_dec 2 sp.2.2.1 :=
    gateOut_mono _ (Hψ.w_dec2_a.trans hn0) (Hψ.w_dec2_b.trans ha1)
  have he2 : gateOut and2 en2_a en2_b <+: W_en 2 sp.2.1 sp.2.2.1 :=
    gateOut_mono _ (hwe _ Hψ.w_en2_a) (Hψ.w_en2_b.trans hd2)
  have hd3 : gateOut and2 dec3_a dec3_b <+: W_dec 3 sp.2.2.1 :=
    gateOut_mono _ (Hψ.w_dec3_a.trans ha0) (Hψ.w_dec3_b.trans ha1)
  have he3 : gateOut and2 en3_a en3_b <+: W_en 3 sp.2.1 sp.2.2.1 :=
    gateOut_mono _ (hwe _ Hψ.w_en3_a) (Hψ.w_en3_b.trans hd3)
  refine packMemOut_prefix ?_ ?_ ?_ ?_
  · exact Hψ.w_pk_q0.trans (enOut_mono (hclk _ Hψ.w_c0_clk) (Hψ.w_c0_en.trans he0)
      (hdata _ Hψ.w_c0_data) (hcrn _ Hψ.w_c0_clrn))
  · exact Hψ.w_pk_q1.trans (enOut_mono (hclk _ Hψ.w_c1_clk) (Hψ.w_c1_en.trans he1)
      (hdata _ Hψ.w_c1_data) (hcrn _ Hψ.w_c1_clrn))
  · exact Hψ.w_pk_q2.trans (enOut_mono (hclk _ Hψ.w_c2_clk) (Hψ.w_c2_en.trans he2)
      (hdata _ Hψ.w_c2_data) (hcrn _ Hψ.w_c2_clrn))
  · exact Hψ.w_pk_q3.trans (enOut_mono (hclk _ Hψ.w_c3_clk) (Hψ.w_c3_en.trans he3)
      (hdata _ Hψ.w_c3_data) (hcrn _ Hψ.w_c3_clrn))

/-- What it has reported it has reported: the report is the packer's, and the packer's
inputs only grow. -/
theorem out_wf : Wf en2_a en2_b en3_a en3_b pk_q0 pk_q1 pk_q2 pk_q3 dec3_a dec3_b c2_clk c2_en c2_data c2_clrn c3_clk c3_en c3_data c3_clrn a0F_in crF_in na0F_in a1F_in dataF_in weF_in na1_a en0_a en0_b c0_clk c0_en c0_data c0_clrn en1_a en1_b na0_a dec0_a dec0_b clkF_in dec2_a dec2_b dec1_a dec1_b na1F_in c1_clk c1_en c1_data c1_clrn unpA_a (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, packMemOut pk_q0 pk_q1 pk_q2 pk_q3) := by
  exact { e_clk := Hψ.e_clk
          e_we := Hψ.e_we
          e_addr := Hψ.e_addr
          e_data := Hψ.e_data
          e_crn := Hψ.e_crn
          w_en2_a := Hψ.w_en2_a
          w_en2_b := Hψ.w_en2_b
          w_en3_a := Hψ.w_en3_a
          w_en3_b := Hψ.w_en3_b
          w_pk_q0 := Hψ.w_pk_q0
          w_pk_q1 := Hψ.w_pk_q1
          w_pk_q2 := Hψ.w_pk_q2
          w_pk_q3 := Hψ.w_pk_q3
          w_dec3_a := Hψ.w_dec3_a
          w_dec3_b := Hψ.w_dec3_b
          w_c2_clk := Hψ.w_c2_clk
          w_c2_en := Hψ.w_c2_en
          w_c2_data := Hψ.w_c2_data
          w_c2_clrn := Hψ.w_c2_clrn
          w_c3_clk := Hψ.w_c3_clk
          w_c3_en := Hψ.w_c3_en
          w_c3_data := Hψ.w_c3_data
          w_c3_clrn := Hψ.w_c3_clrn
          w_a0F_in := Hψ.w_a0F_in
          w_na0F_in := Hψ.w_na0F_in
          w_a1F_in := Hψ.w_a1F_in
          w_na1_a := Hψ.w_na1_a
          w_en0_a := Hψ.w_en0_a
          w_en0_b := Hψ.w_en0_b
          w_c0_clk := Hψ.w_c0_clk
          w_c0_en := Hψ.w_c0_en
          w_c0_data := Hψ.w_c0_data
          w_c0_clrn := Hψ.w_c0_clrn
          w_en1_a := Hψ.w_en1_a
          w_en1_b := Hψ.w_en1_b
          w_na0_a := Hψ.w_na0_a
          w_dec0_a := Hψ.w_dec0_a
          w_dec0_b := Hψ.w_dec0_b
          w_dec2_a := Hψ.w_dec2_a
          w_dec2_b := Hψ.w_dec2_b
          w_dec1_a := Hψ.w_dec1_a
          w_dec1_b := Hψ.w_dec1_b
          w_na1F_in := Hψ.w_na1F_in
          w_c1_clk := Hψ.w_c1_clk
          w_c1_en := Hψ.w_c1_en
          w_c1_data := Hψ.w_c1_data
          w_c1_clrn := Hψ.w_c1_clrn
          h_mem := List.prefix_rfl }

end Cases

/-! ### The refinement -/

theorem int_case_0 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_0 Hψ ‹_›⟩

theorem int_case_1 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_1 Hψ ‹_›⟩

theorem int_case_2 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_2 Hψ ‹_›⟩

theorem int_case_3 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_3 Hψ ‹_›⟩

theorem int_case_4 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_4 Hψ ‹_›⟩

theorem int_case_5 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_5 Hψ ‹_›⟩

theorem int_case_6 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_6 Hψ ‹_›⟩

theorem int_case_7 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_7 Hψ ‹_›⟩

theorem int_case_8 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_8 Hψ ‹_›⟩

theorem int_case_9 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_9 Hψ ‹_›⟩

theorem int_case_10 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_10 Hψ ‹_›⟩

theorem int_case_11 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_11 Hψ ‹_›⟩

theorem int_case_12 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_12 Hψ ‹_›⟩

theorem int_case_13 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_13 Hψ ‹_›⟩

theorem int_case_14 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_14 Hψ ‹_›⟩

theorem int_case_15 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_15 Hψ ‹_›⟩

theorem int_case_16 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_16 Hψ ‹_›⟩

theorem int_case_17 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_17 Hψ ‹_›⟩

theorem int_case_18 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_18 Hψ ‹_›⟩

theorem int_case_19 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_19 Hψ ‹_›⟩

theorem int_case_20 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_20 Hψ ‹_›⟩

theorem int_case_21 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_21 Hψ ‹_›⟩

theorem int_case_22 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_22 Hψ ‹_›⟩

theorem int_case_23 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_23 Hψ ‹_›⟩

theorem int_case_24 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_24 Hψ ‹_›⟩

theorem int_case_25 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_25 Hψ ‹_›⟩

theorem int_case_26 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_26 Hψ ‹_›⟩

theorem int_case_27 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_27 Hψ ‹_›⟩

theorem int_case_28 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 28 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_28 Hψ ‹_›⟩

theorem int_case_29 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 29 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_29 Hψ ‹_›⟩

theorem int_case_30 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 30 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_30 Hψ ‹_›⟩

theorem int_case_31 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 31 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_31 Hψ ‹_›⟩

theorem int_case_32 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 32 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_32 Hψ ‹_›⟩

theorem int_case_33 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 33 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_33 Hψ ‹_›⟩

theorem int_case_34 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 34 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_34 Hψ ‹_›⟩

theorem int_case_35 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 35 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_35 Hψ ‹_›⟩

theorem int_case_36 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 36 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_36 Hψ ‹_›⟩

theorem int_case_37 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 37 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_37 Hψ ‹_›⟩

theorem int_case_38 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 38 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_38 Hψ ‹_› ‹_›⟩

theorem int_case_39 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 39 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_39 Hψ ‹_› ‹_›⟩

theorem int_case_40 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 40 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_40 Hψ ‹_› ‹_›⟩

theorem int_case_41 (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)) (i mid : memT) (Hψ : ψ i s)
    (Hrule : (memNetlist.internals.getD 41 (fun _ _ => False)) i mid) :
    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_en2_a, c_en2_b⟩, ⟨c_en3_a, c_en3_b⟩, ⟨c_pk_q0, c_pk_q1, c_pk_q2, c_pk_q3⟩, ⟨c_dec3_a, c_dec3_b⟩, ⟨c_c2_clk, c_c2_en, c_c2_data, c_c2_clrn⟩, ⟨c_c3_clk, c_c3_en, c_c3_data, c_c3_clrn⟩, c_a0F_in, c_crF_in, c_na0F_in, c_a1F_in, c_dataF_in, c_weF_in, c_na1_a, ⟨c_en0_a, c_en0_b⟩, ⟨c_c0_clk, c_c0_en, c_c0_data, c_c0_clrn⟩, c_unpA_a, ⟨c_en1_a, c_en1_b⟩, c_na0_a, ⟨c_dec0_a, c_dec0_b⟩, c_clkF_in, ⟨c_dec2_a, c_dec2_b⟩, ⟨c_dec1_a, c_dec1_b⟩, c_na1F_in, ⟨c_c1_clk, c_c1_en, c_c1_data, c_c1_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_41 Hψ ‹_› ‹_›⟩

theorem memNetlist_internals_eq : memNetlist.internals = [memNetlist.internals.getD 0 (fun _ _ => False), memNetlist.internals.getD 1 (fun _ _ => False), memNetlist.internals.getD 2 (fun _ _ => False), memNetlist.internals.getD 3 (fun _ _ => False), memNetlist.internals.getD 4 (fun _ _ => False), memNetlist.internals.getD 5 (fun _ _ => False), memNetlist.internals.getD 6 (fun _ _ => False), memNetlist.internals.getD 7 (fun _ _ => False), memNetlist.internals.getD 8 (fun _ _ => False), memNetlist.internals.getD 9 (fun _ _ => False), memNetlist.internals.getD 10 (fun _ _ => False), memNetlist.internals.getD 11 (fun _ _ => False), memNetlist.internals.getD 12 (fun _ _ => False), memNetlist.internals.getD 13 (fun _ _ => False), memNetlist.internals.getD 14 (fun _ _ => False), memNetlist.internals.getD 15 (fun _ _ => False), memNetlist.internals.getD 16 (fun _ _ => False), memNetlist.internals.getD 17 (fun _ _ => False), memNetlist.internals.getD 18 (fun _ _ => False), memNetlist.internals.getD 19 (fun _ _ => False), memNetlist.internals.getD 20 (fun _ _ => False), memNetlist.internals.getD 21 (fun _ _ => False), memNetlist.internals.getD 22 (fun _ _ => False), memNetlist.internals.getD 23 (fun _ _ => False), memNetlist.internals.getD 24 (fun _ _ => False), memNetlist.internals.getD 25 (fun _ _ => False), memNetlist.internals.getD 26 (fun _ _ => False), memNetlist.internals.getD 27 (fun _ _ => False), memNetlist.internals.getD 28 (fun _ _ => False), memNetlist.internals.getD 29 (fun _ _ => False), memNetlist.internals.getD 30 (fun _ _ => False), memNetlist.internals.getD 31 (fun _ _ => False), memNetlist.internals.getD 32 (fun _ _ => False), memNetlist.internals.getD 33 (fun _ _ => False), memNetlist.internals.getD 34 (fun _ _ => False), memNetlist.internals.getD 35 (fun _ _ => False), memNetlist.internals.getD 36 (fun _ _ => False), memNetlist.internals.getD 37 (fun _ _ => False), memNetlist.internals.getD 38 (fun _ _ => False), memNetlist.internals.getD 39 (fun _ _ => False), memNetlist.internals.getD 40 (fun _ _ => False), memNetlist.internals.getD 41 (fun _ _ => False)] := rfl

theorem refines_ψ : memNetlist ⊑_{ψ} memSpec := by
  intro i s Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs memNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [memNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← Hψ.e_clk]; assumption), existSR_reflexive, in_clk Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_we s _ (by rw [← Hψ.e_we]; assumption), existSR_reflexive, in_we Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_addr s _ (by rw [← Hψ.e_addr]; assumption), existSR_reflexive, in_addr Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_data s _ (by rw [← Hψ.e_data]; assumption), existSR_reflexive, in_data Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← Hψ.e_crn]; assumption), existSR_reflexive, in_clrn Hψ _ ‹_›⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_en2_a, m_en2_b⟩, ⟨m_en3_a, m_en3_b⟩, ⟨m_pk_q0, m_pk_q1, m_pk_q2, m_pk_q3⟩, ⟨m_dec3_a, m_dec3_b⟩, ⟨m_c2_clk, m_c2_en, m_c2_data, m_c2_clrn⟩, ⟨m_c3_clk, m_c3_en, m_c3_data, m_c3_clrn⟩, m_a0F_in, m_crF_in, m_na0F_in, m_a1F_in, m_dataF_in, m_weF_in, m_na1_a, ⟨m_en0_a, m_en0_b⟩, ⟨m_c0_clk, m_c0_en, m_c0_data, m_c0_clrn⟩, m_unpA_a, ⟨m_en1_a, m_en1_b⟩, m_na0_a, ⟨m_dec0_a, m_dec0_b⟩, m_clkF_in, ⟨m_dec2_a, m_dec2_b⟩, ⟨m_dec1_a, m_dec1_b⟩, m_na1F_in, ⟨m_c1_clk, m_c1_en, m_c1_data, m_c1_clrn⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs memNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [memNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    exact ⟨s, _, existSR_reflexive, spec_out_mem s _ Hψ.h_mem (out_mem Hψ), out_wf Hψ⟩
  · intro rule mid_i Hin Hrule
    rw [memNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact int_case_0 s i mid_i Hψ Hrule
    · subst h; exact int_case_1 s i mid_i Hψ Hrule
    · subst h; exact int_case_2 s i mid_i Hψ Hrule
    · subst h; exact int_case_3 s i mid_i Hψ Hrule
    · subst h; exact int_case_4 s i mid_i Hψ Hrule
    · subst h; exact int_case_5 s i mid_i Hψ Hrule
    · subst h; exact int_case_6 s i mid_i Hψ Hrule
    · subst h; exact int_case_7 s i mid_i Hψ Hrule
    · subst h; exact int_case_8 s i mid_i Hψ Hrule
    · subst h; exact int_case_9 s i mid_i Hψ Hrule
    · subst h; exact int_case_10 s i mid_i Hψ Hrule
    · subst h; exact int_case_11 s i mid_i Hψ Hrule
    · subst h; exact int_case_12 s i mid_i Hψ Hrule
    · subst h; exact int_case_13 s i mid_i Hψ Hrule
    · subst h; exact int_case_14 s i mid_i Hψ Hrule
    · subst h; exact int_case_15 s i mid_i Hψ Hrule
    · subst h; exact int_case_16 s i mid_i Hψ Hrule
    · subst h; exact int_case_17 s i mid_i Hψ Hrule
    · subst h; exact int_case_18 s i mid_i Hψ Hrule
    · subst h; exact int_case_19 s i mid_i Hψ Hrule
    · subst h; exact int_case_20 s i mid_i Hψ Hrule
    · subst h; exact int_case_21 s i mid_i Hψ Hrule
    · subst h; exact int_case_22 s i mid_i Hψ Hrule
    · subst h; exact int_case_23 s i mid_i Hψ Hrule
    · subst h; exact int_case_24 s i mid_i Hψ Hrule
    · subst h; exact int_case_25 s i mid_i Hψ Hrule
    · subst h; exact int_case_26 s i mid_i Hψ Hrule
    · subst h; exact int_case_27 s i mid_i Hψ Hrule
    · subst h; exact int_case_28 s i mid_i Hψ Hrule
    · subst h; exact int_case_29 s i mid_i Hψ Hrule
    · subst h; exact int_case_30 s i mid_i Hψ Hrule
    · subst h; exact int_case_31 s i mid_i Hψ Hrule
    · subst h; exact int_case_32 s i mid_i Hψ Hrule
    · subst h; exact int_case_33 s i mid_i Hψ Hrule
    · subst h; exact int_case_34 s i mid_i Hψ Hrule
    · subst h; exact int_case_35 s i mid_i Hψ Hrule
    · subst h; exact int_case_36 s i mid_i Hψ Hrule
    · subst h; exact int_case_37 s i mid_i Hψ Hrule
    · subst h; exact int_case_38 s i mid_i Hψ Hrule
    · subst h; exact int_case_39 s i mid_i Hψ Hrule
    · subst h; exact int_case_40 s i mid_i Hψ Hrule
    · subst h; exact int_case_41 s i mid_i Hψ Hrule

theorem refines_initial : Module.refines_initial memNetlist memSpec ψ := by
  intro i hi
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  dsimp only [memNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨([], [], [], [], [], []), rfl, Wf.init⟩

/-- **The decoder and the four cells refine the register file.** -/
theorem mem_refines : memNetlist ⊑ memSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.Mem
