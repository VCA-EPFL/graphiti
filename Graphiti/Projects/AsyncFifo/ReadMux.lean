/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Gates
import Graphiti.Projects.AsyncFifo.Timed

/-!
# The read port as gates

The read domain's data output is `mem[ptr]`: combinational, and at depth 4 with one-bit data it
is a two-bit address decode and a four-way multiplexer --- eleven gates.

The one thing that has to be said about it is why the memory can be gates at all.  The wire that
carries it from the write domain has type `List (BitVec 2 → Bool)`: at each instant a *function*
from address to value.  That is what makes `Timed.MemOut` sayable --- a write to one entry is
invisible to another --- but gates carry `Bool`.  The bridge is a projection: a function-valued
wire *is* four wires, and `entry a` picks one of them, exactly as `StReg.bitsOf` picks a bit out
of a record.  It computes nothing; it is the same kind of adapter as `unpackSt` or `unpackNext`.

The other thing worth naming is why the contract is `Timed.ReadOut` and not `Comb`.  A
multiplexer depends combinationally on *all four* entries, so a `Comb` argument would demand the
whole memory stand still over the delay window --- which is precisely what a memory is for not
having to do.  The gate-level argument is the one `Mem.W_en_false` already makes for the write
decoder: once the address has settled, the three disabled AND gates are `false` whatever their
data, so only the selected entry reaches the output.  `ReadOut`'s two hypotheses (the address
stable, the *selected* word held) are exactly what that argument consumes.

The window is `[3, 5]`: an entry reaches the output through one AND and two ORs, and the address
through an inverter first.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.ReadMux

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Timed

/-! ### The two projections

Neither is logic: both are the identity on the wires the stream stands for. -/

/-- Bit `i` of the read address. -/
def addrBit (i : Nat) (st : List (RSt 2)) : List Bool :=
  st.map (fun x => (x.ptr.setWidth 2).getLsbD i)

/-- Entry `a` of the memory, as its own wire. -/
def entry (a : BitVec 2) (mem : List (BitVec 2 → Bool)) : List Bool :=
  mem.map (fun f => f a)

@[simp] theorem addrBit_length (i : Nat) (st : List (RSt 2)) :
    (addrBit i st).length = st.length := by simp [addrBit]

@[simp] theorem entry_length (a : BitVec 2) (mem : List (BitVec 2 → Bool)) :
    (entry a mem).length = mem.length := by simp [entry]

theorem addrBit_mono {i : Nat} {st st' : List (RSt 2)} (h : st <+: st') :
    addrBit i st <+: addrBit i st' := h.map _

theorem entry_mono {a : BitVec 2} {mem mem' : List (BitVec 2 → Bool)} (h : mem <+: mem') :
    entry a mem <+: entry a mem' := h.map _

theorem addrBit_getD {i : Nat} {st : List (RSt 2)} {u : Nat} (h : u < st.length) :
    (addrBit i st).getD u false = ((st.getD u default).ptr.setWidth 2).getLsbD i := by
  simp [addrBit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]

theorem entry_getD {a : BitVec 2} {mem : List (BitVec 2 → Bool)} {u : Nat} (h : u < mem.length) :
    (entry a mem).getD u false = (mem.getD u (fun _ => default)) a := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]

/-! ### The netlist's wires -/

/-- The complement of an address bit. -/
def na (i : Nat) (st : List (RSt 2)) : List Bool := gate1Out not (addrBit i st)

/-- The four decoded selects. -/
def sel0 (st : List (RSt 2)) : List Bool := gateOut Bool.and (na 0 st) (na 1 st)
def sel1 (st : List (RSt 2)) : List Bool := gateOut Bool.and (addrBit 0 st) (na 1 st)
def sel2 (st : List (RSt 2)) : List Bool := gateOut Bool.and (na 0 st) (addrBit 1 st)
def sel3 (st : List (RSt 2)) : List Bool := gateOut Bool.and (addrBit 0 st) (addrBit 1 st)

/-- The four gated entries. -/
def gd0 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.and (sel0 st) (entry 0#2 mem)
def gd1 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.and (sel1 st) (entry 1#2 mem)
def gd2 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.and (sel2 st) (entry 2#2 mem)
def gd3 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.and (sel3 st) (entry 3#2 mem)

def or01 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.or (gd0 st mem) (gd1 st mem)
def or23 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.or (gd2 st mem) (gd3 st mem)

/-- What the eleven gates compute. -/
def muxWire (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.or (or01 st mem) (or23 st mem)

/-- The boundary cut: the block reports only as far as its own inputs are known.  `ReadOut`'s
length clause has no `+ 1` --- a combinational block is not entitled to the instant a Moore
block is --- so the cut is exact. -/
def cutOut (o r1 r2 : List Bool) : List Bool := o.take (min r1.length r2.length)

/-- What the read port *reports*. -/
def muxOut (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  cutOut (muxWire st mem) (addrBit 0 st) (entry 0#2 mem)

@[simp] theorem muxOut_length (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) :
    (muxOut st mem).length = min (min st.length mem.length) (muxWire st mem).length := by
  simp only [muxOut, cutOut, List.length_take, addrBit_length, entry_length]

/-! ### Lengths

Every wire reaches at least `min st.length mem.length + 1`, so every instant the block reports
is one the gates have computed. -/

theorem len_step {a b N : Nat} (ha : N + 1 ≤ a) (hb : N ≤ b) : N + 1 ≤ min a b + 1 := by
  have : N ≤ min a b := Nat.le_min.mpr ⟨by omega, hb⟩
  omega

/-- A gate reaches every instant the block reports, if both its inputs do. -/
theorem gate_reaches {a b : List Bool} (N : Nat) {u : Nat}
    (ha : N ≤ a.length) (hb : N ≤ b.length) (hu : u ≤ N) : u < min a.length b.length + 1 := by
  have : N ≤ min a.length b.length := Nat.le_min.mpr ⟨ha, hb⟩
  omega

section Lengths

variable {st : List (RSt 2)} {mem : List (BitVec 2 → Bool)}

theorem le_na (i : Nat) : min st.length mem.length + 1 ≤ (na i st).length := by
  rw [na, gate1Out_length, addrBit_length]; omega

theorem le_addrBit (i : Nat) : min st.length mem.length ≤ (addrBit i st).length := by
  rw [addrBit_length]; omega

theorem le_entry (a : BitVec 2) : min st.length mem.length ≤ (entry a mem).length := by
  rw [entry_length]; omega

theorem le_sel0 : min st.length mem.length + 1 ≤ (sel0 st).length := by
  rw [sel0, gateOut_length]; exact len_step (le_na 0) (by have := le_na (st := st) (mem := mem) 1; omega)

theorem le_sel1 : min st.length mem.length + 1 ≤ (sel1 st).length := by
  rw [sel1, gateOut_length]
  exact Nat.succ_le_succ (Nat.le_min.mpr ⟨le_addrBit 0, by have := le_na (st := st) (mem := mem) 1; omega⟩)

theorem le_sel2 : min st.length mem.length + 1 ≤ (sel2 st).length := by
  rw [sel2, gateOut_length]
  exact Nat.succ_le_succ (Nat.le_min.mpr ⟨by have := le_na (st := st) (mem := mem) 0; omega, le_addrBit 1⟩)

theorem le_sel3 : min st.length mem.length + 1 ≤ (sel3 st).length := by
  rw [sel3, gateOut_length]
  exact Nat.succ_le_succ (Nat.le_min.mpr ⟨le_addrBit 0, le_addrBit 1⟩)

theorem le_gd0 : min st.length mem.length + 1 ≤ (gd0 st mem).length := by
  rw [gd0, gateOut_length]; exact len_step le_sel0 (le_entry 0#2)
theorem le_gd1 : min st.length mem.length + 1 ≤ (gd1 st mem).length := by
  rw [gd1, gateOut_length]; exact len_step le_sel1 (le_entry 1#2)
theorem le_gd2 : min st.length mem.length + 1 ≤ (gd2 st mem).length := by
  rw [gd2, gateOut_length]; exact len_step le_sel2 (le_entry 2#2)
theorem le_gd3 : min st.length mem.length + 1 ≤ (gd3 st mem).length := by
  rw [gd3, gateOut_length]; exact len_step le_sel3 (le_entry 3#2)

theorem le_or01 : min st.length mem.length + 1 ≤ (or01 st mem).length := by
  rw [or01, gateOut_length]; exact len_step le_gd0 (by have := le_gd1 (st := st) (mem := mem); omega)
theorem le_or23 : min st.length mem.length + 1 ≤ (or23 st mem).length := by
  rw [or23, gateOut_length]; exact len_step le_gd2 (by have := le_gd3 (st := st) (mem := mem); omega)

theorem le_muxWire : min st.length mem.length + 1 ≤ (muxWire st mem).length := by
  rw [muxWire, gateOut_length]; exact len_step le_or01 (by have := le_or23 (st := st) (mem := mem); omega)

end Lengths

/-! ### What the gates compute -/

theorem bv2_cases (a : BitVec 2) : a = 0#2 ∨ a = 1#2 ∨ a = 2#2 ∨ a = 3#2 := by revert a; decide

section Value

variable {st : List (RSt 2)} {mem : List (BitVec 2 → Bool)} {t : Nat}

/-- **The multiplexer selects.**  With the address stable over `[t-5, t-3]`, the output at `t` is
the entry that address names, read at `t - 3` --- and nothing is assumed about the other three
entries, because their AND gates are disabled. -/
theorem muxWire_getD (h5 : 5 ≤ t) (hS : t < st.length) (hM : t < mem.length)
    (hstab : ∀ u, t - 5 ≤ u → u ≤ t - 3 →
      (st.getD u default).ptr.setWidth 2 = (st.getD (t - 3) default).ptr.setWidth 2) :
    (muxWire st mem).getD t false =
      (mem.getD (t - 3) (fun _ => default)) ((st.getD (t - 3) default).ptr.setWidth 2) := by
  have hN : min st.length mem.length + 1 ≤ st.length + 1 := by omega
  have hNt : t < min st.length mem.length := by omega
  -- the address bits, everywhere in the window
  have hab : ∀ i u, t - 5 ≤ u → u ≤ t - 3 → (addrBit i st).getD u false =
      ((st.getD (t - 3) default).ptr.setWidth 2).getLsbD i := by
    intro i u h1 h2
    rw [addrBit_getD (by omega), hstab u h1 h2]
  have hna : ∀ i, (na i st).getD (t - 4) false =
      !((st.getD (t - 3) default).ptr.setWidth 2).getLsbD i := by
    intro i
    rw [na, gate1Out_getD _ _ (t := t - 4) (by omega) (by rw [addrBit_length]; omega)]
    have : t - 4 - 1 = t - 5 := by omega
    rw [this, hab i (t - 5) (by omega) (by omega)]
  set A := (st.getD (t - 3) default).ptr.setWidth 2 with hA
  have e4 : t - 3 - 1 = t - 4 := by omega
  have hs0 : (sel0 st).getD (t - 3) false = (!A.getLsbD 0 && !A.getLsbD 1) := by
    rw [sel0, gateOut_getD _ _ _ (t := t - 3) (by omega)
      (gate_reaches (min st.length mem.length)
        (by have := le_na (st := st) (mem := mem) 0; omega)
        (by have := le_na (st := st) (mem := mem) 1; omega) (by omega))]
    rw [e4, hna 0, hna 1]
  have hs1 : (sel1 st).getD (t - 3) false = (A.getLsbD 0 && !A.getLsbD 1) := by
    rw [sel1, gateOut_getD _ _ _ (t := t - 3) (by omega)
      (gate_reaches (min st.length mem.length) (by rw [addrBit_length]; omega)
        (by have := le_na (st := st) (mem := mem) 1; omega) (by omega))]
    rw [e4, hab 0 (t - 4) (by omega) (by omega), hna 1]
  have hs2 : (sel2 st).getD (t - 3) false = (!A.getLsbD 0 && A.getLsbD 1) := by
    rw [sel2, gateOut_getD _ _ _ (t := t - 3) (by omega)
      (gate_reaches (min st.length mem.length)
        (by have := le_na (st := st) (mem := mem) 0; omega)
        (by rw [addrBit_length]; omega) (by omega))]
    rw [e4, hna 0, hab 1 (t - 4) (by omega) (by omega)]
  have hs3 : (sel3 st).getD (t - 3) false = (A.getLsbD 0 && A.getLsbD 1) := by
    rw [sel3, gateOut_getD _ _ _ (t := t - 3) (by omega)
      (gate_reaches (min st.length mem.length) (by rw [addrBit_length]; omega)
        (by rw [addrBit_length]; omega) (by omega))]
    rw [e4, hab 0 (t - 4) (by omega) (by omega), hab 1 (t - 4) (by omega) (by omega)]
  -- the gated entries
  have hg : ∀ (s : List Bool) (a : BitVec 2) (b : Bool),
      min st.length mem.length + 1 ≤ s.length → s.getD (t - 3) false = b →
      (gateOut Bool.and s (entry a mem)).getD (t - 2) false =
        (b && (mem.getD (t - 3) (fun _ => default)) a) := by
    intro s a b hls hsv
    rw [gateOut_getD _ _ _ (t := t - 2) (by omega)
      (gate_reaches (min st.length mem.length) (by omega) (le_entry a) (by omega))]
    have h21 : t - 2 - 1 = t - 3 := by omega
    rw [h21, hsv, entry_getD (by omega)]
  have hgd0 := hg _ 0#2 _ le_sel0 hs0
  have hgd1 := hg _ 1#2 _ le_sel1 hs1
  have hgd2 := hg _ 2#2 _ le_sel2 hs2
  have hgd3 := hg _ 3#2 _ le_sel3 hs3
  -- the OR tree
  have ho : ∀ (x y : List Bool) (bx byy : Bool),
      min st.length mem.length + 1 ≤ x.length → min st.length mem.length + 1 ≤ y.length →
      x.getD (t - 2) false = bx → y.getD (t - 2) false = byy →
      (gateOut Bool.or x y).getD (t - 1) false = (bx || byy) := by
    intro x y bx byy hx hy hxv hyv
    rw [gateOut_getD _ _ _ (t := t - 1) (by omega)
      (gate_reaches (min st.length mem.length) (by omega) (by omega) (by omega))]
    have h11 : t - 1 - 1 = t - 2 := by omega
    rw [h11, hxv, hyv]
  have ho01 := ho _ _ _ _ le_gd0 le_gd1 hgd0 hgd1
  have ho23 := ho _ _ _ _ le_gd2 le_gd3 hgd2 hgd3
  rw [muxWire, gateOut_getD _ _ _ (t := t) (by omega)
    (gate_reaches (min st.length mem.length)
      (by have := le_or01 (st := st) (mem := mem); omega)
      (by have := le_or23 (st := st) (mem := mem); omega) (by omega))]
  simp only [or01, or23]
  rw [ho01, ho23]
  rcases bv2_cases A with h | h | h | h <;> rw [h] <;> simp

/-- **The read port's contract**: an asynchronous read with delay window `[3, 5]`. -/
theorem muxOut_readOut {v : List Bool} (hv : v <+: muxOut st mem) :
    ReadOut 3 5 (fun u => (st.getD u default).ptr.setWidth 2)
      (fun u => mem.getD u (fun _ => default)) (min st.length mem.length) v := by
  have hvl := hv.length_le
  rw [muxOut_length] at hvl
  refine ⟨by omega, fun t h5 ht hstab _ => ?_⟩
  have hlt : t < min st.length mem.length := by omega
  have hmw := le_muxWire (st := st) (mem := mem)
  have htk : t < ((muxWire st mem).take
      (min (addrBit 0 st).length (entry 0#2 mem).length)).length := by
    simp only [List.length_take, addrBit_length, entry_length]
    omega
  rw [hv.getD_eq_left ht, muxOut, cutOut, (List.take_prefix _ _).getD_eq_left htk]
  exact muxWire_getD h5 (by omega) (by omega) (fun u h1 h2 => hstab.2 u h1 h2)

end Value

/-! ### The netlist -/

/-- The two projections as a block: no logic, only wiring.  `a0c`/`m0c` are the same wires as
`a0`/`m0`, offered a second time for the boundary cut. -/
@[drcomponents]
def unpRD : StringModule (List (RSt 2) × List (BitVec 2 → Bool)) :=
  { inputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2 ⊏ v ∧ s' = (s.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"a0", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 0 s.1⟩)
               , (↑"a0c", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 0 s.1⟩)
               , (↑"a1", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 1 s.1⟩)
               , (↑"m0", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 0#2 s.2⟩)
               , (↑"m0c", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 0#2 s.2⟩)
               , (↑"m1", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 1#2 s.2⟩)
               , (↑"m2", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 2#2 s.2⟩)
               , (↑"m3", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 3#2 s.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], []) }

/-- The boundary cut as a block. -/
@[drcomponents]
def cutRD : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"r1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"r2", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = cutOut s.1 s.2.1 s.2.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

theorem cutOut_mono {o o' r1 r1' r2 r2' : List Bool} (ho : o <+: o') (h1 : r1 <+: r1')
    (h2 : r2 <+: r2') : cutOut o r1 r2 <+: cutOut o' r1' r2' := by
  have l1 := h1.length_le; have l2 := h2.length_le; have lo := ho.length_le
  rw [prefix_iff_length_getD false]
  refine ⟨by simp only [cutOut, List.length_take]; omega, fun t ht => ?_⟩
  simp only [cutOut, List.length_take] at ht
  show (o.take _).getD t false = (o'.take _).getD t false
  rw [(List.take_prefix _ _).getD_eq_left (by simp only [List.length_take]; omega),
    (List.take_prefix _ _).getD_eq_left (by simp only [List.length_take]; omega),
    ho.getD_eq_left (by omega)]

def muxGraph := [graphEnv|
    st [type="io"];
    mem [type="io"];
    q [type="io"];

    unpRD [type="unpRD", typeImp=$(⟨_, unpRD⟩)];
    fa0 [type="fork3", typeImp=$(⟨_, fork3⟩)];
    fa1 [type="fork3", typeImp=$(⟨_, fork3⟩)];
    na0 [type="inv", typeImp=$(⟨_, gate1 not⟩)];
    na1 [type="inv", typeImp=$(⟨_, gate1 not⟩)];
    fn0 [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    fn1 [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    s0 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s1 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s2 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s3 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g0 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g1 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g2 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g3 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    o01 [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    o23 [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    outg [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    cut [type="cutRD", typeImp=$(⟨_, cutRD⟩)];

    st -> unpRD [to="st"];
    mem -> unpRD [to="mem"];

    unpRD -> fa0 [from="a0", to="in"];
    unpRD -> fa1 [from="a1", to="in"];
    unpRD -> cut [from="a0c", to="r1"];
    unpRD -> cut [from="m0c", to="r2"];
    fa0 -> na0 [from="out1", to="a"];
    fa1 -> na1 [from="out1", to="a"];
    na0 -> fn0 [from="out", to="in"];
    na1 -> fn1 [from="out", to="in"];
    fn0 -> s0 [from="out1", to="a"];
    fn1 -> s0 [from="out1", to="b"];
    fa0 -> s1 [from="out2", to="a"];
    fn1 -> s1 [from="out2", to="b"];
    fn0 -> s2 [from="out2", to="a"];
    fa1 -> s2 [from="out2", to="b"];
    fa0 -> s3 [from="out3", to="a"];
    fa1 -> s3 [from="out3", to="b"];
    s0 -> g0 [from="out", to="a"];
    unpRD -> g0 [from="m0", to="b"];
    s1 -> g1 [from="out", to="a"];
    unpRD -> g1 [from="m1", to="b"];
    s2 -> g2 [from="out", to="a"];
    unpRD -> g2 [from="m2", to="b"];
    s3 -> g3 [from="out", to="a"];
    unpRD -> g3 [from="m3", to="b"];
    g0 -> o01 [from="out", to="a"];
    g1 -> o01 [from="out", to="b"];
    g2 -> o23 [from="out", to="a"];
    g3 -> o23 [from="out", to="b"];
    o01 -> outg [from="out", to="a"];
    o23 -> outg [from="out", to="b"];
    outg -> cut [from="out", to="in"];

    cut -> q [from="out"];
  ]

@[drunfold_defs]
def muxLowered := muxGraph.1.lower_TR |>.get rfl

def rdenv := muxGraph.2

@[drenv] theorem rdenv_unpRD : rdenv.find? "unpRD" = .some ⟨_, unpRD⟩ := rfl
@[drenv] theorem rdenv_cutRD : rdenv.find? "cutRD" = .some ⟨_, cutRD⟩ := rfl
@[drenv] theorem rdenv_fork3 : rdenv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem rdenv_fork2 : rdenv.find? "fork2" = .some ⟨_, Timed.fork2 Bool⟩ := rfl
@[drenv] theorem rdenv_inv : rdenv.find? "inv" = .some ⟨_, gate1 not⟩ := rfl
@[drenv] theorem rdenv_and2 : rdenv.find? "and2" = .some ⟨_, gate2 Bool.and⟩ := rfl
@[drenv] theorem rdenv_or2 : rdenv.find? "or2" = .some ⟨_, gate2 Bool.or⟩ := rfl

seal rdenv in
def_module muxT : Type :=
  [T| muxLowered, rdenv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal rdenv in
def_module muxNetlist : StringModule muxT :=
  [e| muxLowered, rdenv.find? ]

-- HEADER_END (everything below is generated by gen/gen_readmux.py)

/-! ### The specification -/

/-- The read port as a single block: what the eleven gates compute, cut at the block's own
inputs. -/
@[drcomponents]
def readMuxSpec : StringModule (List (RSt 2) × List (BitVec 2 → Bool) × List Bool) :=
  { inputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2.1 ⊏ v ∧
                  s' = (s.1, v, s.2.2)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s.2.2 <+: v ∧ v <+: muxOut s.1 s.2.1 ∧
                    s' = (s.1, s.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

instance : MatchInterface muxNetlist readMuxSpec := by
  dsimp [muxNetlist, readMuxSpec]
  solve_match_interface

/-! ### The invariant -/

structure Wf (o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b : List Bool)
    (unpRD_st : List (RSt 2)) (unpRD_mem : List (BitVec 2 → Bool))
    (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) : Prop where
  e_st : unpRD_st = s.1
  e_mem : unpRD_mem = s.2.1
  w_o23_a : o23_a <+: gateOut Bool.and g2_a g2_b
  w_o23_b : o23_b <+: gateOut Bool.and g3_a g3_b
  w_outg_a : outg_a <+: gateOut Bool.or o01_a o01_b
  w_outg_b : outg_b <+: gateOut Bool.or o23_a o23_b
  w_s0_a : s0_a <+: fn0_in
  w_s0_b : s0_b <+: fn1_in
  w_s2_a : s2_a <+: fn0_in
  w_s2_b : s2_b <+: fa1_in
  w_s3_a : s3_a <+: fa0_in
  w_s3_b : s3_b <+: fa1_in
  w_fn1_in : fn1_in <+: gate1Out not na1_a
  w_na1_a : na1_a <+: fa1_in
  w_g1_a : g1_a <+: gateOut Bool.and s1_a s1_b
  w_g1_b : g1_b <+: entry 1#2 unpRD_mem
  w_fn0_in : fn0_in <+: gate1Out not na0_a
  w_fa0_in : fa0_in <+: addrBit 0 unpRD_st
  w_g2_a : g2_a <+: gateOut Bool.and s2_a s2_b
  w_g2_b : g2_b <+: entry 2#2 unpRD_mem
  w_na0_a : na0_a <+: fa0_in
  w_fa1_in : fa1_in <+: addrBit 1 unpRD_st
  w_o01_a : o01_a <+: gateOut Bool.and g0_a g0_b
  w_o01_b : o01_b <+: gateOut Bool.and g1_a g1_b
  w_g3_a : g3_a <+: gateOut Bool.and s3_a s3_b
  w_g3_b : g3_b <+: entry 3#2 unpRD_mem
  w_cut_in : cut_in <+: gateOut Bool.or outg_a outg_b
  w_cut_r1 : cut_r1 <+: addrBit 0 unpRD_st
  w_cut_r2 : cut_r2 <+: entry 0#2 unpRD_mem
  w_g0_a : g0_a <+: gateOut Bool.and s0_a s0_b
  w_g0_b : g0_b <+: entry 0#2 unpRD_mem
  w_s1_a : s1_a <+: fa0_in
  w_s1_b : s1_b <+: fn1_in
  h_q : s.2.2 <+: cutOut cut_in cut_r1 cut_r2

def ψ (i : muxT) (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) : Prop :=
  Wf i.1.1 i.1.2 i.2.1.1 i.2.1.2 i.2.2.1.1 i.2.2.1.2 i.2.2.2.1.1 i.2.2.2.1.2 i.2.2.2.2.1.1 i.2.2.2.2.1.2 i.2.2.2.2.2.1 i.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 i.2.2.2.2.2.2.2.1.1 i.2.2.2.2.2.2.2.1.2 s

theorem Wf.init : Wf [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] ([], [], []) :=
  ⟨rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩

section SpecRules
variable (sp : List (RSt 2) × List (BitVec 2 → Bool) × List Bool)

theorem spec_in_st (v : List (RSt 2)) (h : sp.1 ⊏ v) :
    (readMuxSpec.inputs.getIO ↑"st").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_mem (v : List (BitVec 2 → Bool)) (h : sp.2.1 ⊏ v) :
    (readMuxSpec.inputs.getIO ↑"mem").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List Bool) (h1 : sp.2.2 <+: v) (h2 : v <+: muxOut sp.1 sp.2.1) :
    (readMuxSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

section Cases
variable {o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b : List Bool}
  {unpRD_st : List (RSt 2)} {unpRD_mem : List (BitVec 2 → Bool)} {sp : List (RSt 2) × List (BitVec 2 → Bool) × List Bool}
  (Hψ : Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp)
include Hψ

theorem in_st (v : List (RSt 2)) (h : unpRD_st ⊏ v) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b (v) unpRD_mem (v, sp.2) := by
  have hm : unpRD_st <+: v := h.isPrefix
  exact { e_st := rfl
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in.trans (addrBit_mono hm)
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in.trans (addrBit_mono hm)
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1.trans (addrBit_mono hm)
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem in_mem (v : List (BitVec 2 → Bool)) (h : unpRD_mem ⊏ v) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st (v) (sp.1, v, sp.2.2) := by
  have hm : unpRD_mem <+: v := h.isPrefix
  exact { e_st := Hψ.e_st
          e_mem := rfl
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b.trans (entry_mono hm)
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b.trans (entry_mono hm)
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b.trans (entry_mono hm)
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2.trans (entry_mono hm)
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b.trans (entry_mono hm)
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_0 (_h : fa0_in ⊏ addrBit 0 unpRD_st) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in (addrBit 0 unpRD_st) g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a.trans Hψ.w_fa0_in
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := List.prefix_rfl
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a.trans Hψ.w_fa0_in
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a.trans Hψ.w_fa0_in
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_1 (_h : fa1_in ⊏ addrBit 1 unpRD_st) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a (addrBit 1 unpRD_st) o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b.trans Hψ.w_fa1_in
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b.trans Hψ.w_fa1_in
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a.trans Hψ.w_fa1_in
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := List.prefix_rfl
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_2 (_h : cut_r1 ⊏ addrBit 0 unpRD_st) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in (addrBit 0 unpRD_st) cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := List.prefix_rfl
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q.trans (cutOut_mono List.prefix_rfl (_h.isPrefix) List.prefix_rfl) }

theorem int_3 (_h : cut_r2 ⊏ entry 0#2 unpRD_mem) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 (entry 0#2 unpRD_mem) g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := List.prefix_rfl
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q.trans (cutOut_mono List.prefix_rfl List.prefix_rfl (_h.isPrefix)) }

theorem int_4 (_h : na0_a ⊏ fa0_in) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b (fa0_in) fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in.trans (gate1Out_mono _ Hψ.w_na0_a)
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := List.prefix_rfl
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_5 (_h : na1_a ⊏ fa1_in) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in (fa1_in) g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in.trans (gate1Out_mono _ Hψ.w_na1_a)
          w_na1_a := List.prefix_rfl
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_6 (_h : fn0_in ⊏ gate1Out not na0_a) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b (gate1Out not na0_a) fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a.trans Hψ.w_fn0_in
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a.trans Hψ.w_fn0_in
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := List.prefix_rfl
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_7 (_h : fn1_in ⊏ gate1Out not na1_a) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b (gate1Out not na1_a) na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b.trans Hψ.w_fn1_in
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := List.prefix_rfl
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b.trans Hψ.w_fn1_in
          h_q := Hψ.h_q }

theorem int_8 (_h : s0_a ⊏ fn0_in) :
    Wf o23_a o23_b outg_a outg_b (fn0_in) s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := List.prefix_rfl
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a.trans (gateOut_mono _ Hψ.w_s0_a List.prefix_rfl)
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_9 (_h : s0_b ⊏ fn1_in) :
    Wf o23_a o23_b outg_a outg_b s0_a (fn1_in) s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := List.prefix_rfl
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_s0_b)
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_10 (_h : s1_a ⊏ fa0_in) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b (fa0_in) s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a.trans (gateOut_mono _ Hψ.w_s1_a List.prefix_rfl)
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := List.prefix_rfl
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_11 (_h : s1_b ⊏ fn1_in) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a (fn1_in) unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_s1_b)
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := List.prefix_rfl
          h_q := Hψ.h_q }

theorem int_12 (_h : s2_a ⊏ fn0_in) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b (fn0_in) s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := List.prefix_rfl
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a.trans (gateOut_mono _ Hψ.w_s2_a List.prefix_rfl)
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_13 (_h : s2_b ⊏ fa1_in) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a (fa1_in) s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := List.prefix_rfl
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_s2_b)
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_14 (_h : s3_a ⊏ fa0_in) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b (fa0_in) s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := List.prefix_rfl
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a.trans (gateOut_mono _ Hψ.w_s3_a List.prefix_rfl)
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_15 (_h : s3_b ⊏ fa1_in) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a (fa1_in) fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := List.prefix_rfl
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_s3_b)
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_16 (_h : g0_a ⊏ gateOut Bool.and s0_a s0_b) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 (gateOut Bool.and s0_a s0_b) g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a.trans (gateOut_mono _ Hψ.w_g0_a List.prefix_rfl)
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := List.prefix_rfl
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_17 (_h : g0_b ⊏ entry 0#2 unpRD_mem) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a (entry 0#2 unpRD_mem) s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_g0_b)
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := List.prefix_rfl
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_18 (_h : g1_a ⊏ gateOut Bool.and s1_a s1_b) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a (gateOut Bool.and s1_a s1_b) g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := List.prefix_rfl
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b.trans (gateOut_mono _ Hψ.w_g1_a List.prefix_rfl)
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_19 (_h : g1_b ⊏ entry 1#2 unpRD_mem) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a (entry 1#2 unpRD_mem) fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := List.prefix_rfl
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_g1_b)
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_20 (_h : g2_a ⊏ gateOut Bool.and s2_a s2_b) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in (gateOut Bool.and s2_a s2_b) g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a.trans (gateOut_mono _ Hψ.w_g2_a List.prefix_rfl)
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := List.prefix_rfl
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_21 (_h : g2_b ⊏ entry 2#2 unpRD_mem) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a (entry 2#2 unpRD_mem) na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_g2_b)
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := List.prefix_rfl
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_22 (_h : g3_a ⊏ gateOut Bool.and s3_a s3_b) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b (gateOut Bool.and s3_a s3_b) g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b.trans (gateOut_mono _ Hψ.w_g3_a List.prefix_rfl)
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := List.prefix_rfl
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_23 (_h : g3_b ⊏ entry 3#2 unpRD_mem) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a (entry 3#2 unpRD_mem) cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_g3_b)
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := List.prefix_rfl
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_24 (_h : o01_a ⊏ gateOut Bool.and g0_a g0_b) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in (gateOut Bool.and g0_a g0_b) o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a.trans (gateOut_mono _ Hψ.w_o01_a List.prefix_rfl)
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := List.prefix_rfl
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_25 (_h : o01_b ⊏ gateOut Bool.and g1_a g1_b) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a (gateOut Bool.and g1_a g1_b) g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a.trans (gateOut_mono _ List.prefix_rfl Hψ.w_o01_b)
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := List.prefix_rfl
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_26 (_h : o23_a ⊏ gateOut Bool.and g2_a g2_b) :
    Wf (gateOut Bool.and g2_a g2_b) o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := List.prefix_rfl
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b.trans (gateOut_mono _ Hψ.w_o23_a List.prefix_rfl)
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_27 (_h : o23_b ⊏ gateOut Bool.and g3_a g3_b) :
    Wf o23_a (gateOut Bool.and g3_a g3_b) outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := List.prefix_rfl
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b.trans (gateOut_mono _ List.prefix_rfl Hψ.w_o23_b)
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_28 (_h : outg_a ⊏ gateOut Bool.or o01_a o01_b) :
    Wf o23_a o23_b (gateOut Bool.or o01_a o01_b) outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := List.prefix_rfl
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in.trans (gateOut_mono _ Hψ.w_outg_a List.prefix_rfl)
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_29 (_h : outg_b ⊏ gateOut Bool.or o23_a o23_b) :
    Wf o23_a o23_b outg_a (gateOut Bool.or o23_a o23_b) s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := List.prefix_rfl
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in.trans (gateOut_mono _ List.prefix_rfl Hψ.w_outg_b)
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q }

theorem int_30 (_h : cut_in ⊏ gateOut Bool.or outg_a outg_b) :
    Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b (gateOut Bool.or outg_a outg_b) cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem sp := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := List.prefix_rfl
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := Hψ.h_q.trans (cutOut_mono (_h.isPrefix) List.prefix_rfl List.prefix_rfl) }

/-- What the port reports is a prefix of what the netlist computes from the block's own
inputs: monotonicity, composed along the netlist. -/
theorem out_q : cutOut cut_in cut_r1 cut_r2 <+: muxOut sp.1 sp.2.1 := by
  have ha0 : fa0_in <+: addrBit 0 sp.1 :=
    Hψ.w_fa0_in.trans (addrBit_mono (Hψ.e_st ▸ List.prefix_rfl))
  have ha1 : fa1_in <+: addrBit 1 sp.1 :=
    Hψ.w_fa1_in.trans (addrBit_mono (Hψ.e_st ▸ List.prefix_rfl))
  have hn0 : fn0_in <+: na 0 sp.1 :=
    Hψ.w_fn0_in.trans (gate1Out_mono _ (Hψ.w_na0_a.trans ha0))
  have hn1 : fn1_in <+: na 1 sp.1 :=
    Hψ.w_fn1_in.trans (gate1Out_mono _ (Hψ.w_na1_a.trans ha1))
  have hs0 : gateOut Bool.and s0_a s0_b <+: sel0 sp.1 :=
    gateOut_mono _ (Hψ.w_s0_a.trans hn0) (Hψ.w_s0_b.trans hn1)
  have hs1 : gateOut Bool.and s1_a s1_b <+: sel1 sp.1 :=
    gateOut_mono _ (Hψ.w_s1_a.trans ha0) (Hψ.w_s1_b.trans hn1)
  have hs2 : gateOut Bool.and s2_a s2_b <+: sel2 sp.1 :=
    gateOut_mono _ (Hψ.w_s2_a.trans hn0) (Hψ.w_s2_b.trans ha1)
  have hs3 : gateOut Bool.and s3_a s3_b <+: sel3 sp.1 :=
    gateOut_mono _ (Hψ.w_s3_a.trans ha0) (Hψ.w_s3_b.trans ha1)
  have hm0 : g0_b <+: entry 0#2 sp.2.1 :=
    Hψ.w_g0_b.trans (entry_mono (Hψ.e_mem ▸ List.prefix_rfl))
  have hg0 : gateOut Bool.and g0_a g0_b <+: gd0 sp.1 sp.2.1 :=
    gateOut_mono _ (Hψ.w_g0_a.trans hs0) hm0
  have hm1 : g1_b <+: entry 1#2 sp.2.1 :=
    Hψ.w_g1_b.trans (entry_mono (Hψ.e_mem ▸ List.prefix_rfl))
  have hg1 : gateOut Bool.and g1_a g1_b <+: gd1 sp.1 sp.2.1 :=
    gateOut_mono _ (Hψ.w_g1_a.trans hs1) hm1
  have hm2 : g2_b <+: entry 2#2 sp.2.1 :=
    Hψ.w_g2_b.trans (entry_mono (Hψ.e_mem ▸ List.prefix_rfl))
  have hg2 : gateOut Bool.and g2_a g2_b <+: gd2 sp.1 sp.2.1 :=
    gateOut_mono _ (Hψ.w_g2_a.trans hs2) hm2
  have hm3 : g3_b <+: entry 3#2 sp.2.1 :=
    Hψ.w_g3_b.trans (entry_mono (Hψ.e_mem ▸ List.prefix_rfl))
  have hg3 : gateOut Bool.and g3_a g3_b <+: gd3 sp.1 sp.2.1 :=
    gateOut_mono _ (Hψ.w_g3_a.trans hs3) hm3
  have ho01 : gateOut Bool.or o01_a o01_b <+: or01 sp.1 sp.2.1 :=
    gateOut_mono _ (Hψ.w_o01_a.trans hg0) (Hψ.w_o01_b.trans hg1)
  have ho23 : gateOut Bool.or o23_a o23_b <+: or23 sp.1 sp.2.1 :=
    gateOut_mono _ (Hψ.w_o23_a.trans hg2) (Hψ.w_o23_b.trans hg3)
  have hw : gateOut Bool.or outg_a outg_b <+: muxWire sp.1 sp.2.1 :=
    gateOut_mono _ (Hψ.w_outg_a.trans ho01) (Hψ.w_outg_b.trans ho23)
  exact cutOut_mono (Hψ.w_cut_in.trans hw)
    (Hψ.w_cut_r1.trans (addrBit_mono (Hψ.e_st ▸ List.prefix_rfl)))
    (Hψ.w_cut_r2.trans (entry_mono (Hψ.e_mem ▸ List.prefix_rfl)))

/-- What it has reported it has reported: the report is the cut's, and the cut only grows. -/
theorem out_wf : Wf o23_a o23_b outg_a outg_b s0_a s0_b s2_a s2_b s3_a s3_b fn1_in na1_a g1_a g1_b fn0_in fa0_in g2_a g2_b na0_a fa1_in o01_a o01_b g3_a g3_b cut_in cut_r1 cut_r2 g0_a g0_b s1_a s1_b unpRD_st unpRD_mem (sp.1, sp.2.1, cutOut cut_in cut_r1 cut_r2) := by
  exact { e_st := Hψ.e_st
          e_mem := Hψ.e_mem
          w_o23_a := Hψ.w_o23_a
          w_o23_b := Hψ.w_o23_b
          w_outg_a := Hψ.w_outg_a
          w_outg_b := Hψ.w_outg_b
          w_s0_a := Hψ.w_s0_a
          w_s0_b := Hψ.w_s0_b
          w_s2_a := Hψ.w_s2_a
          w_s2_b := Hψ.w_s2_b
          w_s3_a := Hψ.w_s3_a
          w_s3_b := Hψ.w_s3_b
          w_fn1_in := Hψ.w_fn1_in
          w_na1_a := Hψ.w_na1_a
          w_g1_a := Hψ.w_g1_a
          w_g1_b := Hψ.w_g1_b
          w_fn0_in := Hψ.w_fn0_in
          w_fa0_in := Hψ.w_fa0_in
          w_g2_a := Hψ.w_g2_a
          w_g2_b := Hψ.w_g2_b
          w_na0_a := Hψ.w_na0_a
          w_fa1_in := Hψ.w_fa1_in
          w_o01_a := Hψ.w_o01_a
          w_o01_b := Hψ.w_o01_b
          w_g3_a := Hψ.w_g3_a
          w_g3_b := Hψ.w_g3_b
          w_cut_in := Hψ.w_cut_in
          w_cut_r1 := Hψ.w_cut_r1
          w_cut_r2 := Hψ.w_cut_r2
          w_g0_a := Hψ.w_g0_a
          w_g0_b := Hψ.w_g0_b
          w_s1_a := Hψ.w_s1_a
          w_s1_b := Hψ.w_s1_b
          h_q := List.prefix_rfl }

end Cases

/-! ### The refinement -/

theorem int_case_0 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_0 Hψ ‹_›⟩

theorem int_case_1 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_1 Hψ ‹_›⟩

theorem int_case_2 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_2 Hψ ‹_›⟩

theorem int_case_3 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_3 Hψ ‹_›⟩

theorem int_case_4 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_4 Hψ ‹_›⟩

theorem int_case_5 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_5 Hψ ‹_›⟩

theorem int_case_6 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_6 Hψ ‹_›⟩

theorem int_case_7 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_7 Hψ ‹_›⟩

theorem int_case_8 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_8 Hψ ‹_›⟩

theorem int_case_9 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_9 Hψ ‹_›⟩

theorem int_case_10 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_10 Hψ ‹_›⟩

theorem int_case_11 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_11 Hψ ‹_›⟩

theorem int_case_12 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_12 Hψ ‹_›⟩

theorem int_case_13 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_13 Hψ ‹_›⟩

theorem int_case_14 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_14 Hψ ‹_›⟩

theorem int_case_15 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_15 Hψ ‹_›⟩

theorem int_case_16 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_16 Hψ ‹_›⟩

theorem int_case_17 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_17 Hψ ‹_›⟩

theorem int_case_18 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_18 Hψ ‹_›⟩

theorem int_case_19 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_19 Hψ ‹_›⟩

theorem int_case_20 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_20 Hψ ‹_›⟩

theorem int_case_21 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_21 Hψ ‹_›⟩

theorem int_case_22 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_22 Hψ ‹_›⟩

theorem int_case_23 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_23 Hψ ‹_›⟩

theorem int_case_24 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_24 Hψ ‹_›⟩

theorem int_case_25 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_25 Hψ ‹_›⟩

theorem int_case_26 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_26 Hψ ‹_›⟩

theorem int_case_27 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_27 Hψ ‹_›⟩

theorem int_case_28 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 28 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_28 Hψ ‹_›⟩

theorem int_case_29 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 29 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_29 Hψ ‹_›⟩

theorem int_case_30 (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) (i mid : muxT) (Hψ : ψ i s)
    (Hrule : (muxNetlist.internals.getD 30 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_o23_a, c_o23_b⟩, ⟨c_outg_a, c_outg_b⟩, ⟨c_s0_a, c_s0_b⟩, ⟨c_s2_a, c_s2_b⟩, ⟨c_s3_a, c_s3_b⟩, c_fn1_in, c_na1_a, ⟨c_unpRD_st, c_unpRD_mem⟩, ⟨c_g1_a, c_g1_b⟩, c_fn0_in, c_fa0_in, ⟨c_g2_a, c_g2_b⟩, c_na0_a, c_fa1_in, ⟨c_o01_a, c_o01_b⟩, ⟨c_g3_a, c_g3_b⟩, ⟨c_cut_in, c_cut_r1, c_cut_r2⟩, ⟨c_g0_a, c_g0_b⟩, ⟨c_s1_a, c_s1_b⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_30 Hψ ‹_›⟩

theorem muxNetlist_internals_eq : muxNetlist.internals = [muxNetlist.internals.getD 0 (fun _ _ => False), muxNetlist.internals.getD 1 (fun _ _ => False), muxNetlist.internals.getD 2 (fun _ _ => False), muxNetlist.internals.getD 3 (fun _ _ => False), muxNetlist.internals.getD 4 (fun _ _ => False), muxNetlist.internals.getD 5 (fun _ _ => False), muxNetlist.internals.getD 6 (fun _ _ => False), muxNetlist.internals.getD 7 (fun _ _ => False), muxNetlist.internals.getD 8 (fun _ _ => False), muxNetlist.internals.getD 9 (fun _ _ => False), muxNetlist.internals.getD 10 (fun _ _ => False), muxNetlist.internals.getD 11 (fun _ _ => False), muxNetlist.internals.getD 12 (fun _ _ => False), muxNetlist.internals.getD 13 (fun _ _ => False), muxNetlist.internals.getD 14 (fun _ _ => False), muxNetlist.internals.getD 15 (fun _ _ => False), muxNetlist.internals.getD 16 (fun _ _ => False), muxNetlist.internals.getD 17 (fun _ _ => False), muxNetlist.internals.getD 18 (fun _ _ => False), muxNetlist.internals.getD 19 (fun _ _ => False), muxNetlist.internals.getD 20 (fun _ _ => False), muxNetlist.internals.getD 21 (fun _ _ => False), muxNetlist.internals.getD 22 (fun _ _ => False), muxNetlist.internals.getD 23 (fun _ _ => False), muxNetlist.internals.getD 24 (fun _ _ => False), muxNetlist.internals.getD 25 (fun _ _ => False), muxNetlist.internals.getD 26 (fun _ _ => False), muxNetlist.internals.getD 27 (fun _ _ => False), muxNetlist.internals.getD 28 (fun _ _ => False), muxNetlist.internals.getD 29 (fun _ _ => False), muxNetlist.internals.getD 30 (fun _ _ => False)] := rfl

theorem refines_ψ : muxNetlist ⊑_{ψ} readMuxSpec := by
  intro i s Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs muxNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [muxNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨_, _, spec_in_st s _ (by rw [← Hψ.e_st]; assumption), existSR_reflexive, in_st Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_mem s _ (by rw [← Hψ.e_mem]; assumption), existSR_reflexive, in_mem Hψ _ ‹_›⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_o23_a, m_o23_b⟩, ⟨m_outg_a, m_outg_b⟩, ⟨m_s0_a, m_s0_b⟩, ⟨m_s2_a, m_s2_b⟩, ⟨m_s3_a, m_s3_b⟩, m_fn1_in, m_na1_a, ⟨m_unpRD_st, m_unpRD_mem⟩, ⟨m_g1_a, m_g1_b⟩, m_fn0_in, m_fa0_in, ⟨m_g2_a, m_g2_b⟩, m_na0_a, m_fa1_in, ⟨m_o01_a, m_o01_b⟩, ⟨m_g3_a, m_g3_b⟩, ⟨m_cut_in, m_cut_r1, m_cut_r2⟩, ⟨m_g0_a, m_g0_b⟩, ⟨m_s1_a, m_s1_b⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs muxNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [muxNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ Hψ.h_q (out_q Hψ), out_wf Hψ⟩
  · intro rule mid_i Hin Hrule
    rw [muxNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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

theorem refines_initial : Module.refines_initial muxNetlist readMuxSpec ψ := by
  intro i hi
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  dsimp only [muxNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨([], [], []), rfl, Wf.init⟩

/-- **The eleven gates refine the read port.** -/
theorem mux_refines : muxNetlist ⊑ readMuxSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.ReadMux
