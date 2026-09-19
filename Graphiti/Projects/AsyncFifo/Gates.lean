/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Timed

/-!
# Gates

Unit-delay boolean gates as Graphiti modules, in the style of Kobler's report: a gate stores
its input streams, and its output at instant `t ≥ 1` is the gate function of the inputs at
`t - 1`; at instant `0` it is low (`delay false`).  A gate reports its output only as far as
its inputs are known (one instant less than it could), so that outputs never outrun inputs:
this is the length discipline of the contracts of `Timed.lean`.  Forks copy a stream with no
delay.

`Comb lo hi F inp w` is the combinational contract of a wire of a netlist: `w` is the output
of logic of depth between `lo` and `hi` computing `F` of the netlist's primary inputs
`inp`.  It composes through gates (`Comb.gate2`, `Comb.gate1`), weakens to wider depth windows
(`Comb.weaken`), and a bundle of such wires satisfies the `CombOut` contract of the block.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Gates

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Timed

/-! ### Gate semantics on streams

A gate has unit delay, so its output at instant `t` is its function of the inputs at `t - 1`,
and at instant `0` it is low: nothing has propagated yet.  That makes the output *one instant
longer* than its inputs -- the Moore convention of Kobler's report, and the reason information
can go round a loop at all.  A gate that truncated its output to its inputs' horizon would be
sound but useless: in a cycle every gate would wait for the one before it and no stream would
ever grow. -/

/-- Output of a two-input gate: low at `0`, then `f` of the inputs one instant earlier. -/
def gateOut (f : Bool → Bool → Bool) (a b : List Bool) : List Bool :=
  false :: List.zipWith f a b

/-- Output of a three-input gate (the flip-flop needs one). -/
def gate3Out (f : Bool → Bool → Bool → Bool) (a b c : List Bool) : List Bool :=
  false :: List.zipWith (fun x yz => f x yz.1 yz.2) a (b.zip c)

/-- Output of a one-input gate. -/
def gate1Out (f : Bool → Bool) (a : List Bool) : List Bool := false :: a.map f

@[simp] theorem gateOut_length (f : Bool → Bool → Bool) (a b : List Bool) :
    (gateOut f a b).length = min a.length b.length + 1 := by
  simp [gateOut, List.length_zipWith]

@[simp] theorem gate1Out_length (f : Bool → Bool) (a : List Bool) :
    (gate1Out f a).length = a.length + 1 := by
  simp [gate1Out]

@[simp] theorem gate3Out_length (f : Bool → Bool → Bool → Bool) (a b c : List Bool) :
    (gate3Out f a b c).length = min (min a.length b.length) c.length + 1 := by
  simp [gate3Out, List.length_zipWith]

theorem gateOut_getD_zero (f : Bool → Bool → Bool) (a b : List Bool) :
    (gateOut f a b).getD 0 false = false := rfl

theorem gate1Out_getD_zero (f : Bool → Bool) (a : List Bool) :
    (gate1Out f a).getD 0 false = false := rfl

theorem gate3Out_getD_zero (f : Bool → Bool → Bool → Bool) (a b c : List Bool) :
    (gate3Out f a b c).getD 0 false = false := rfl

theorem gateOut_getD (f : Bool → Bool → Bool) (a b : List Bool) {t : Nat} (ht : 1 ≤ t)
    (ht' : t < min a.length b.length + 1) :
    (gateOut f a b).getD t false = f (a.getD (t - 1) false) (b.getD (t - 1) false) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hta : t < a.length := by omega
  have htb : t < b.length := by omega
  have hz : t < (List.zipWith f a b).length := by simp only [List.length_zipWith]; omega
  unfold gateOut
  rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_eq_getElem hz,
    Option.getD_some, List.getElem_zipWith]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hta, List.getElem?_eq_getElem htb]

theorem gate1Out_getD (f : Bool → Bool) (a : List Bool) {t : Nat} (ht : 1 ≤ t)
    (ht' : t < a.length + 1) :
    (gate1Out f a).getD t false = f (a.getD (t - 1) false) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hta : t < a.length := by omega
  unfold gate1Out
  rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  simp [List.getElem?_map, List.getElem?_eq_getElem hta, List.getD_eq_getElem?_getD]

theorem gate3Out_getD (f : Bool → Bool → Bool → Bool) (a b c : List Bool) {t : Nat} (ht : 1 ≤ t)
    (ht' : t < min (min a.length b.length) c.length + 1) :
    (gate3Out f a b c).getD t false =
      f (a.getD (t - 1) false) (b.getD (t - 1) false) (c.getD (t - 1) false) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hta : t < a.length := by omega
  have htb : t < b.length := by omega
  have htc : t < c.length := by omega
  have hz : t < (List.zipWith (fun x yz => f x yz.1 yz.2) a (b.zip c)).length := by
    simp only [List.length_zipWith, List.length_zip]; omega
  unfold gate3Out
  rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_eq_getElem hz,
    Option.getD_some, List.getElem_zipWith, List.getElem_zip]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hta, List.getElem?_eq_getElem htb,
    List.getElem?_eq_getElem htc]

theorem gate3Out_mono (f : Bool → Bool → Bool → Bool) {a a' b b' c c' : List Bool}
    (ha : a <+: a') (hb : b <+: b') (hc : c <+: c') : gate3Out f a b c <+: gate3Out f a' b' c' := by
  rw [prefix_iff_length_getD false]
  have := ha.length_le; have := hb.length_le; have := hc.length_le
  refine ⟨by simp only [gate3Out_length]; omega, fun t ht => ?_⟩
  simp only [gate3Out_length] at ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [gate3Out_getD_zero, gate3Out_getD_zero]
  · rw [gate3Out_getD f a b c hpos ht, gate3Out_getD f a' b' c' hpos (by omega),
      ha.getD_eq_left (by omega), hb.getD_eq_left (by omega), hc.getD_eq_left (by omega)]

theorem gateOut_mono (f : Bool → Bool → Bool) {a a' b b' : List Bool} (ha : a <+: a') (hb : b <+: b') :
    gateOut f a b <+: gateOut f a' b' := by
  rw [prefix_iff_length_getD false]
  have := ha.length_le; have := hb.length_le
  refine ⟨by simp only [gateOut_length]; omega, fun t ht => ?_⟩
  simp only [gateOut_length] at ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [gateOut_getD_zero, gateOut_getD_zero]
  · rw [gateOut_getD f a b hpos ht, gateOut_getD f a' b' hpos (by omega), ha.getD_eq_left (by omega),
      hb.getD_eq_left (by omega)]

theorem gate1Out_mono (f : Bool → Bool) {a a' : List Bool} (ha : a <+: a') : gate1Out f a <+: gate1Out f a' := by
  rw [prefix_iff_length_getD false]
  have := ha.length_le
  refine ⟨by simp only [gate1Out_length]; omega, fun t ht => ?_⟩
  simp only [gate1Out_length] at ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [gate1Out_getD_zero, gate1Out_getD_zero]
  · rw [gate1Out_getD f a hpos ht, gate1Out_getD f a' hpos (by omega), ha.getD_eq_left (by omega)]

/-- Two streams agree when they have the same length and the same elements. -/
theorem list_eq_of_getD {α : Type} {l₁ l₂ : List α} (d : α) (hl : l₁.length = l₂.length)
    (h : ∀ t, t < l₁.length → l₁.getD t d = l₂.getD t d) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro t h₁ h₂
  have := h t h₁
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂, Option.getD_some, Option.getD_some] at this

/-! ### Gate modules -/

/-- A two-input gate with function `f`. -/
@[drcomponents]
def gate2 (f : Bool → Bool → Bool) : StringModule (List Bool × List Bool) :=
  { inputs := [ (↑"a", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"b", ⟨List Bool, fun s v s' => s.2 ⊏ v ∧ s' = (s.1, v)⟩) ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = gateOut f s.1 s.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], []) }

/-- A one-input gate with function `f`. -/
@[drcomponents]
def gate1 (f : Bool → Bool) : StringModule (List Bool) :=
  { inputs := [ (↑"a", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = gate1Out f s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- A three-input gate with function `f`. -/
@[drcomponents]
def gate3 (f : Bool → Bool → Bool → Bool) : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"a", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"b", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"c", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = gate3Out f s.1 s.2.1 s.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

/-- Zero-delay forks. -/
@[drcomponents]
def fork3 : StringModule (List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out3", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

@[drcomponents]
def fork4 : StringModule (List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out3", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out4", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

@[drcomponents]
def fork5 : StringModule (List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out3", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out4", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out5", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

@[drcomponents]
def fork7 : StringModule (List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out3", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out4", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out5", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out6", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out7", ⟨List Bool, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-! ### Buses and their bits -/

/-- A three-bit bus from its bits, least significant first. -/
def bv3 (b0 b1 b2 : Bool) : BitVec 3 :=
  (BitVec.ofBool b0).setWidth 3 ||| ((BitVec.ofBool b1).setWidth 3 <<< 1) |||
    ((BitVec.ofBool b2).setWidth 3 <<< 2)

/-- A two-bit bus from its bits. -/
def bv2 (b0 b1 : Bool) : BitVec 2 :=
  (BitVec.ofBool b0).setWidth 2 ||| ((BitVec.ofBool b1).setWidth 2 <<< 1)

/-! ### The reporting policy of a block

A netlist of unit-delay gates computes further ahead than its inputs: each level of logic knows
its output one instant past the inputs it reads, which is exactly what lets a stream go round a
loop.  What a *block* may report is another matter.  The contracts of `Timed.lean` bound an
output by the horizon of the block's inputs (plus the one instant a Moore block is entitled to,
since its output at `t` depends on its inputs strictly before `t`), and that bound is what makes
them monotone: if a block reported a value that a not-yet-known clock edge would change, the
stream it remembers could not stay valid as its inputs grow.

So a gate-level block ends in `cut3`, which passes its input on only as far as three reference
streams -- the block's own inputs -- are known, plus one.  This is not a gate: it computes
nothing, and reporting less than one knows is always sound. -/

/-- Report a stream as far as four reference streams are known, plus one instant. -/
@[drcomponents]
def cut4 : StringModule (List Bool × List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"r1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"r2", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"r3", ⟨List Bool, fun s v s' => s.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
              , (↑"r4", ⟨List Bool, fun s v s' => s.2.2.2.2 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧
                    v = s.1.take (min (min s.2.1.length s.2.2.1.length)
                      (min s.2.2.2.1.length s.2.2.2.2.length) + 1)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], []) }

/-- Report a stream as far as three reference streams are known, plus one instant. -/
@[drcomponents]
def cut3 : StringModule (List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"r1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"r2", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"r3", ⟨List Bool, fun s v s' => s.2.2.2 ⊏ v ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧
                    v = s.1.take (min (min s.2.1.length s.2.2.1.length) s.2.2.2.length + 1)⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

/-! ### Combinational contracts of wires -/

/-- `w` is a wire of a netlist whose primary inputs are `inp` (known for `len` instants),
computing `F` of them through logic of depth between `lo` and `hi`: wherever the inputs were
constant over the delay window, the wire shows `F` of them. -/
def Comb {I : Type} (lo hi : Nat) (F : I → Bool) (inp : Nat → I) (w : List Bool) : Prop :=
  lo ≤ hi ∧
  ∀ t, hi ≤ t → t < w.length → (∀ u, t - hi ≤ u → u ≤ t - lo → inp u = inp (t - lo)) →
    w.getD t false = F (inp (t - hi))

variable {I : Type} {inp : Nat → I}

/-- A primary input, or a projection of one, is a wire of depth `0`. -/
theorem Comb.input {F : I → Bool} {w : List Bool}
    (h : ∀ t, t < w.length → w.getD t false = F (inp t)) : Comb 0 0 F inp w :=
  ⟨Nat.le_refl _, fun t _ ht _ => h t ht⟩

theorem Comb.weaken {lo hi lo' hi' : Nat} {F : I → Bool} {w : List Bool} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : Comb lo hi F inp w) : Comb lo' hi' F inp w := by
  obtain ⟨hlh, h⟩ := h
  refine ⟨by lia, fun t ht htl hs => ?_⟩
  rw [h t (by lia) htl (fun u hu1 hu2 => by rw [hs u (by lia) (by lia), hs (t - lo) (by lia) (by lia)])]
  rw [hs (t - hi) (by lia) (by lia), hs (t - hi') (by lia) (by lia)]

theorem Comb.gate2 {lo1 hi1 lo2 hi2 : Nat} {F1 F2 : I → Bool} {w1 w2 : List Bool} (f : Bool → Bool → Bool)
    (h1 : Comb lo1 hi1 F1 inp w1) (h2 : Comb lo2 hi2 F2 inp w2) :
    Comb (min lo1 lo2 + 1) (max hi1 hi2 + 1) (fun i => f (F1 i) (F2 i)) inp (gateOut f w1 w2) := by
  obtain ⟨hlh1, h1⟩ := h1
  obtain ⟨hlh2, h2⟩ := h2
  refine ⟨by omega, fun t ht htl hs => ?_⟩
  simp only [gateOut_length] at htl
  have hmin : min lo1 lo2 ≤ lo1 ∧ min lo1 lo2 ≤ lo2 := ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩
  have hmax : hi1 ≤ max hi1 hi2 ∧ hi2 ≤ max hi1 hi2 := ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  rw [gateOut_getD f w1 w2 (by omega) htl]
  rw [h1 (t - 1) (by omega) (by omega) (fun u hu1 hu2 => by rw [hs u (by omega) (by omega), hs (t - 1 - lo1) (by omega) (by omega)])]
  rw [h2 (t - 1) (by omega) (by omega) (fun u hu1 hu2 => by rw [hs u (by omega) (by omega), hs (t - 1 - lo2) (by omega) (by omega)])]
  rw [hs (t - 1 - hi1) (by omega) (by omega), hs (t - 1 - hi2) (by omega) (by omega),
    hs (t - (max hi1 hi2 + 1)) (by omega) (by omega)]

theorem Comb.gate1 {lo1 hi1 : Nat} {F1 : I → Bool} {w1 : List Bool} (f : Bool → Bool)
    (h1 : Comb lo1 hi1 F1 inp w1) :
    Comb (lo1 + 1) (hi1 + 1) (fun i => f (F1 i)) inp (gate1Out f w1) := by
  obtain ⟨hlh1, h1⟩ := h1
  refine ⟨by omega, fun t ht htl hs => ?_⟩
  simp only [gate1Out_length] at htl
  rw [gate1Out_getD f w1 (by omega) htl]
  rw [h1 (t - 1) (by omega) (by omega) (fun u hu1 hu2 => by rw [hs u (by omega) (by omega), hs (t - 1 - lo1) (by omega) (by omega)])]
  rw [hs (t - 1 - hi1) (by omega) (by omega), hs (t - (hi1 + 1)) (by omega) (by omega)]

/-- A prefix of a wire satisfies its contract. -/
theorem Comb.of_prefix {lo hi : Nat} {F : I → Bool} {w w' : List Bool} (h : w' <+: w) (hw : Comb lo hi F inp w) :
    Comb lo hi F inp w' := by
  have := h.length_le
  obtain ⟨hlh, hw⟩ := hw
  refine ⟨hlh, fun t ht htl hs => ?_⟩
  rw [h.getD_eq_left htl]; exact hw t ht (by omega) hs

/-- `getD` through `map`, below the length. -/
theorem getD_map_lt {α β : Type} [Inhabited α] (f : α → β) (l : List α) {t : Nat} (ht : t < l.length) (d : β) :
    (l.map f).getD t d = f (l.getD t default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

/-- `CombOut` is prefix-closed. -/
theorem CombOut.of_prefix {κ ο : Type} [Inhabited ο] {dep : Nat → κ} {g : κ → ο} {len dmin dmax : Nat}
    {v v' : List ο} (h : v' <+: v) (hv : CombOut dep g len dmin dmax v) : CombOut dep g len dmin dmax v' := by
  have := h.length_le
  obtain ⟨hl, hv⟩ := hv
  refine ⟨by omega, fun t hdt ht hs => ?_⟩
  rw [h.getD_eq_left ht]; exact hv t hdt (by omega) hs

/-- The stability hypothesis of `CombOut` gives the one of `Comb` (for a window `[0, hi]`). -/
theorem Comb.stable_of_StableOn {κ : Type} {dep : Nat → κ} {len hi t : Nat} (hs : StableOn dep len (t - hi) t) :
    ∀ u, t - hi ≤ u → u ≤ t - 0 → dep u = dep (t - 0) := fun u hu1 hu2 => hs.2 u hu1 (by omega)

/-! ### Arithmetic on stream lengths without case splits

The length of a netlist's output is a nested `min` of its inputs' lengths.  `omega` handles
`min` by splitting every occurrence into two cases, so its cost doubles with each `min`: a
goal with 13 of them already needs minutes and gigabytes.  Generated proofs therefore never
give `omega` a nested `min`.  They rewrite `t < min a b` into a conjunction (`Nat.lt_min`),
`min a b ≤ c` into a disjunction (`min_le_iff_nat`), and prove monotonicity by composing
`min_mono`, all of which stay linear in the number of `min`s. -/

theorem min_mono {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : min a b ≤ min c d := by omega

theorem min_le_iff_nat {a b c : Nat} : min a b ≤ c ↔ a ≤ c ∨ b ≤ c := by omega

end Graphiti.AsyncFifo.Gates
